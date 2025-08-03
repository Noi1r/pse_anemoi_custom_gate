use ff::PrimeField;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};
use serde::{Deserialize, Serialize};

use crate::{
    anemoi_constants::AnemoiConstants,
    utils::{assign_advice_batch, assign_fixed_batch, enable_fixed_selectors},
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MerklePosition {
    Left,
    Middle,
    Right,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MerkleProofNode<F: Field> {
    pub current_hash: F,
    pub sibling1: F,
    pub sibling2: F,
    pub position: MerklePosition,
}

#[derive(Clone, Debug)]
pub struct OptimizedMerkleMembershipCircuit<F: PrimeField> {
    pub leaf_value: F,
    pub merkle_path: Vec<MerkleProofNode<F>>,
    pub expected_root: F,
}

/// 优化的TurboPlonk风格约束系统配置
/// 基于reference中的约束形式，使用5列witness + 预处理轮密钥
#[derive(Clone, Debug)]
pub struct OptimizedMerkleConfig {
    /// 5个advice列 (TurboPlonk标准)
    /// w1, w2, w3, w4, wo
    pub advices: [Column<Advice>; 5],

    /// TurboPlonk标准选择器
    pub q1: Column<Fixed>,
    pub q2: Column<Fixed>,
    pub q3: Column<Fixed>,
    pub q4: Column<Fixed>,
    pub qo: Column<Fixed>,
    pub qm1: Selector,  // w1 * w2 乘法
    pub qm2: Selector,  // w3 * w4 乘法
    pub qc: Selector,   // 常数项
    pub qecc: Selector, // 五次约束 w1*w2*w3*w4*wo
    pub qb: Selector,   // 布尔约束

    /// Anemoi预处理轮密钥 (4个，对应x[0], x[1], y[0], y[1])
    pub qprk1: Column<Fixed>, // round_keys_x[0]
    pub qprk2: Column<Fixed>, // round_keys_x[1]
    pub qprk3: Column<Fixed>, // round_keys_y[0]
    pub qprk4: Column<Fixed>, // round_keys_y[1]

    /// 实例列
    pub instance: Column<Instance>,
}

impl<F: PrimeField> Circuit<F> for OptimizedMerkleMembershipCircuit<F> {
    type Config = OptimizedMerkleConfig;
    type FloorPlanner = halo2_proofs::circuit::SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        self.clone()
    }

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let advices = [(); 5].map(|_| cs.advice_column());

        // TurboPlonk Selectors.
        let q1 = cs.fixed_column();
        let q2 = cs.fixed_column();
        let q3 = cs.fixed_column();
        let q4 = cs.fixed_column();
        let qo = cs.fixed_column();
        let qm1 = cs.complex_selector();
        let qm2 = cs.complex_selector();
        let qc = cs.complex_selector();
        let qecc = cs.complex_selector();
        let qb = cs.complex_selector();

        // Anemoi Preprocess Round Key.
        let qprk1 = cs.fixed_column();
        let qprk2 = cs.fixed_column();
        let qprk3 = cs.fixed_column();
        let qprk4 = cs.fixed_column();

        let instance = cs.instance_column();

        // Enable Permutation.
        for advice in advices.iter() {
            cs.enable_equality(*advice);
        }
        cs.enable_equality(instance);

        // Base Constraint for TurboPlonk.
        cs.create_gate("turbo_plonk_base", |meta| {
            let w1 = meta.query_advice(advices[0], Rotation::cur());
            let w2 = meta.query_advice(advices[1], Rotation::cur());
            let w3 = meta.query_advice(advices[2], Rotation::cur());
            let w4 = meta.query_advice(advices[3], Rotation::cur());
            let wo = meta.query_advice(advices[4], Rotation::cur());

            let q1 = meta.query_fixed(q1, Rotation::cur());
            let q2 = meta.query_fixed(q2, Rotation::cur());
            let q3 = meta.query_fixed(q3, Rotation::cur());
            let q4 = meta.query_fixed(q4, Rotation::cur());
            let qo = meta.query_fixed(qo, Rotation::cur());
            let qm1 = meta.query_selector(qm1);
            let qm2 = meta.query_selector(qm2);
            let qc = meta.query_selector(qc);
            let qecc = meta.query_selector(qecc);

            vec![
                // q1*w1 + q2*w2 + q3*w3 + q4*w4 + qm1*w1*w2 + qm2*w3*w4 + qc + qecc*w1*w2*w3*w4*wo - qo*wo = 0
                q1 * w1.clone()
                    + q2 * w2.clone()
                    + q3 * w3.clone()
                    + q4 * w4.clone()
                    + qm1 * w1.clone() * w2.clone()
                    + qm2 * w3.clone() * w4.clone()
                    + qc
                    + qecc * w1 * w2 * w3 * w4 * wo.clone()
                    - qo * wo,
            ]
        });

        // Boolean Constraints: qb * (w2, w3, w4 must be in {0, 1}).
        cs.create_gate(
            "boolean_constraints",
            |meta: &mut halo2_proofs::plonk::VirtualCells<'_, F>| {
                let w2 = meta.query_advice(advices[1], Rotation::cur());
                let w3 = meta.query_advice(advices[2], Rotation::cur());
                let w4 = meta.query_advice(advices[3], Rotation::cur());
                let qb = meta.query_selector(qb);

                vec![
                    qb.clone() * w2.clone() * (w2 - Expression::Constant(F::ONE)),
                    qb.clone() * w3.clone() * (w3 - Expression::Constant(F::ONE)),
                    qb * w4.clone() * (w4 - Expression::Constant(F::ONE)),
                ]
            },
        );

        // 📝 Anemoi Constraints.
        cs.create_gate("anemoi_constraints", |meta| {
            let w1 = meta.query_advice(advices[0], Rotation::cur());
            let w2 = meta.query_advice(advices[1], Rotation::cur());
            let w3 = meta.query_advice(advices[2], Rotation::cur());
            let w4 = meta.query_advice(advices[3], Rotation::cur());
            let wo = meta.query_advice(advices[4], Rotation::cur());

            let w1_next = meta.query_advice(advices[0], Rotation::next());
            let w2_next = meta.query_advice(advices[1], Rotation::next());
            let w3_next = meta.query_advice(advices[2], Rotation::next());

            let qprk1 = meta.query_fixed(qprk1, Rotation::cur());
            let qprk2 = meta.query_fixed(qprk2, Rotation::cur());
            let qprk3 = meta.query_fixed(qprk3, Rotation::cur());
            let qprk4 = meta.query_fixed(qprk4, Rotation::cur());

            // Anemoi generator.
            let g = Expression::Constant(F::from(5u64)); // generator
            let g_inv = Expression::Constant(
                F::from_str_vartime(
                    "8755297148735710088898562298102910035419345760166413737479281674630323398247",
                )
                .unwrap_or(F::ZERO),
            ); // generator_inv

            // Intermediate Expression.
            let c_prime_1 =
                w1.clone() + w4.clone() + g.clone() * (w2.clone() + w3.clone()) + qprk3.clone();
            let c_prime_2 = g.clone() * (w1.clone() + w4.clone())
                + (g.clone() * g.clone() + Expression::Constant(F::ONE))
                    * (w2.clone() + w3.clone())
                + qprk4.clone();

            let two = Expression::Constant(F::from(2u64));

            vec![
                // Anemoi Constraints 1.
                qprk3.clone()
                    * ((c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        + g.clone() * c_prime_1.clone() * c_prime_1.clone()
                        - (two.clone() * w1.clone()
                            + w4.clone()
                            + g.clone() * (two.clone() * w2.clone() + w3.clone())
                            + qprk1)),
                // Anemoi Constraints 2.
                qprk3.clone()
                    * ((c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        + g.clone() * c_prime_2.clone() * c_prime_2.clone()
                        - (g.clone() * (two.clone() * w1.clone() + w4.clone())
                            + (g.clone() * g.clone() + Expression::Constant(F::ONE))
                                * (two.clone() * w2.clone() + w3.clone())
                            + qprk2)),
                // Anemoi Constraints 3.
                qprk3.clone()
                    * ((c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        * (c_prime_1.clone() - w3_next.clone())
                        + g.clone() * w3_next.clone() * w3_next.clone()
                        + g_inv.clone()
                        - w1_next),
                // Anemoi Constraints 4.
                qprk3
                    * ((c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        * (c_prime_2.clone() - wo.clone())
                        + g.clone() * wo.clone() * wo.clone()
                        + g_inv
                        - w2_next),
            ]
        });

        OptimizedMerkleConfig {
            advices,
            q1,
            q2,
            q3,
            q4,
            qo,
            qm1,
            qm2,
            qc,
            qecc,
            qb,
            qprk1,
            qprk2,
            qprk3,
            qprk4,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let anemoi_constants = AnemoiConstants::<F>::new();

        let (leaf_cell, root_cell) = layouter.assign_region(
            || "Optimized Merkle path with TurboPlonk constraints",
            |mut region| {
                let mut offset = 0;
                let mut current_hash = self.leaf_value;

                // 分配叶子节点
                let leaf_cell = region.assign_advice(
                    || "leaf_value",
                    config.advices[0],
                    offset,
                    || Value::known(self.leaf_value),
                )?;
                offset += 1;

                // 处理每一层的Merkle路径
                for node in self.merkle_path.iter() {
                    // 位置验证 (使用TurboPlonk基础约束)
                    let (left_hash, middle_hash, right_hash) = self
                        .assign_position_verification_optimized(
                            &mut region,
                            &config,
                            &mut offset,
                            node.clone(),
                        )?;

                    // 优化的Anemoi Jive CRH实现
                    current_hash = self.assign_optimized_anemoi_jive_crh(
                        &mut region,
                        &config,
                        &mut offset,
                        left_hash,
                        middle_hash,
                        right_hash,
                        F::ZERO, // padding constant
                        node.clone(),
                        &anemoi_constants,
                    )?;
                }
                // 最终根验证
                let root_cell = self.assign_root_verification_optimized(
                    &mut region,
                    &config,
                    &mut offset,
                    current_hash,
                    self.expected_root,
                )?;

                Ok((leaf_cell, root_cell))
            },
        )?;

        // 约束公共输入
        layouter.constrain_instance(root_cell.cell(), config.instance, 0)?;
        layouter.constrain_instance(leaf_cell.cell(), config.instance, 1)?;

        Ok(())
    }
}

impl<F: PrimeField> OptimizedMerkleMembershipCircuit<F> {
    /// 使用TurboPlonk基础约束进行位置验证
    fn assign_position_verification_optimized(
        &self,
        region: &mut Region<'_, F>,
        config: &OptimizedMerkleConfig,
        offset: &mut usize,
        node: MerkleProofNode<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let (is_left, is_middle, is_right) = match node.position {
            MerklePosition::Left => (F::ONE, F::ZERO, F::ZERO),
            MerklePosition::Middle => (F::ZERO, F::ONE, F::ZERO),
            MerklePosition::Right => (F::ZERO, F::ZERO, F::ONE),
        };

        // 激活 Turbo Plonk 约束
        enable_fixed_selectors(
            region,
            "position verification",
            &[config.q2, config.q3, config.q4, config.qo],
            &[config.q1],
            *offset,
        )?;

        config.qb.enable(region, *offset)?; // 激活布尔约束

        assign_advice_batch(
            region,
            &config.advices[1..], // 跳过 unused_w1
            Some(&["is_left", "is_middle", "is_right", "sum_of_position_bit"]),
            &[is_left, is_middle, is_right, F::ONE],
            *offset,
        )?;

        *offset += 1;
        let (left_hash, middle_hash, right_hash) = match node.position {
            MerklePosition::Left => (node.current_hash, node.sibling1, node.sibling2),
            MerklePosition::Middle => (node.sibling1, node.current_hash, node.sibling2),
            MerklePosition::Right => (node.sibling1, node.sibling2, node.current_hash),
        };
        let partial_sum = left_hash * is_left + middle_hash * is_middle;

        // 激活 Turbo Plonk 约束
        config.qm1.enable(region, *offset)?;
        config.qm2.enable(region, *offset)?;
        enable_fixed_selectors(
            region,
            "position verification",
            &[config.qo],
            &[config.q1, config.q2, config.q3, config.q4],
            *offset,
        )?;

        // @WindOctober: TODO permutation.
        let left_middle_cells = assign_advice_batch(
            region,
            &config.advices,
            Some(&[
                "left_hash",
                "is_left",
                "middle_hash",
                "is_middle",
                "partial_sum",
            ]),
            &[left_hash, is_left, middle_hash, is_middle, partial_sum],
            *offset,
        )?;

        *offset += 1;

        config.qm1.enable(region, *offset)?;

        enable_fixed_selectors(
            region,
            "position verification",
            &[config.q3, config.qo],
            &[config.q1, config.q2, config.q4],
            *offset,
        )?;

        // @WindOctober: TODO permutation.
        let right_cells = assign_advice_batch(
            region,
            &config.advices,
            Some(&[
                "right_hash",
                "is_right",
                "partial_sum",
                "zero",
                "current_hash",
            ]),
            &[
                right_hash,
                is_right,
                partial_sum,
                F::ZERO,
                node.current_hash,
            ],
            *offset,
        )?;

        *offset += 1;
        let left_hash_cell = left_middle_cells[0].clone();
        let middle_hash_cell = left_middle_cells[2].clone();
        let right_hash_cell = right_cells[0].clone();

        Ok((left_hash_cell, middle_hash_cell, right_hash_cell))
    }

    /// 优化的Anemoi Jive CRH实现 (使用5列witness)
    fn assign_optimized_anemoi_jive_crh(
        &self,
        region: &mut Region<'_, F>,
        config: &OptimizedMerkleConfig,
        offset: &mut usize,
        left: AssignedCell<F, F>,
        middle: AssignedCell<F, F>,
        right: AssignedCell<F, F>,
        padding: F,
        node: MerkleProofNode<F>,
        constants: &AnemoiConstants<F>,
    ) -> Result<F, Error> {
        let (left_hash, middle_hash, right_hash) = match node.position {
            MerklePosition::Left => (node.current_hash, node.sibling1, node.sibling2),
            MerklePosition::Middle => (node.sibling1, node.current_hash, node.sibling2),
            MerklePosition::Right => (node.sibling1, node.sibling2, node.current_hash),
        };

        let mut jive_x = [left_hash, middle_hash];
        let mut jive_y = [right_hash, padding];

        let sum_before_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];
        enable_fixed_selectors(
            region,
            "jive hash round",
            &[config.q1, config.q2, config.q3, config.q4, config.qo],
            &[],
            *offset,
        )?;

        let cells = assign_advice_batch(
            region,
            &config.advices,
            Some(&["x0", "x1", "y0", "y1", "sum_before"]),
            &[jive_x[0], jive_x[1], jive_y[0], jive_y[1], sum_before_perm],
            *offset,
        )?;

        region.constrain_equal(left.cell(), cells[0].cell())?; // left -> x0
        region.constrain_equal(middle.cell(), cells[1].cell())?; // middle -> x1
        region.constrain_equal(right.cell(), cells[2].cell())?; // right -> y0
        *offset += 1;

        // 14轮Anemoi变换 (每轮一行，使用预处理轮密钥)
        for round in 0..14 {
            assign_fixed_batch(
                region,
                &[config.qprk1, config.qprk2, config.qprk3, config.qprk4],
                Some(&[
                    &format!("qprk1_round_{}", round),
                    &format!("qprk2_round_{}", round),
                    &format!("qprk3_round_{}", round),
                    &format!("qprk4_round_{}", round),
                ]),
                &[
                    constants.preprocessed_round_keys_x[round][0],
                    constants.preprocessed_round_keys_x[round][1],
                    constants.preprocessed_round_keys_y[round][0],
                    constants.preprocessed_round_keys_y[round][1],
                ],
                *offset,
            )?;
            let annotations = [
                format!("round_{}_x0", round),
                format!("round_{}_x1", round),
                format!("round_{}_y0", round),
                format!("round_{}_y1", round),
            ];

            assign_advice_batch(
                region,
                &config.advices[..4],
                Some(&annotations.iter().map(String::as_str).collect::<Vec<_>>()),
                &[jive_x[0], jive_x[1], jive_y[0], jive_y[1]],
                *offset,
            )?;

            self.apply_anemoi_round(&mut jive_x, &mut jive_y, round, constants);

            region.assign_advice(
                || "wo optimized",
                config.advices[4],
                *offset,
                || Value::known(jive_y[1]),
            )?;
            *offset += 1;
        }

        let annotations = ["final_x0", "final_x1", "final_y0", "final_y1"];

        assign_advice_batch(
            region,
            &config.advices[..4],
            Some(&annotations),
            &[jive_x[0], jive_x[1], jive_y[0], jive_y[1]],
            *offset,
        )?;

        assign_fixed_batch(
            region,
            &[config.q1, config.q2, config.q3, config.q4, config.qo],
            Some(&["q1_final", "q2_final", "q3_final", "q4_final", "qo_final"]),
            &[
                F::from(3u64) * constants.generator + F::from(3u64),
                F::from(3u64)
                    * (constants.generator * constants.generator + constants.generator + F::ONE),
                F::from(2u64)
                    * (constants.generator * constants.generator + constants.generator + F::ONE),
                F::from(2u64) * constants.generator + F::from(2u64),
                F::ONE,
            ],
            *offset,
        )?;
        self.apply_final_transformations(&mut jive_x, &mut jive_y, constants);

        let sum_after_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];

        region.assign_advice(
            || "sum_after",
            config.advices[4],
            *offset,
            || Value::known(sum_after_perm),
        )?;

        *offset += 1;
        let jive_output = sum_before_perm + sum_after_perm;
        enable_fixed_selectors(
            region,
            "final checksum",
            &[config.q1, config.q2, config.qo],
            &[config.q3, config.q4],
            *offset,
        )?;

        assign_advice_batch(
            region,
            &config.advices,
            Some(&["sum_before", "sum_after", "zero", "zero", "output"]),
            &[
                sum_before_perm,
                sum_after_perm,
                F::ZERO,
                F::ZERO,
                jive_output,
            ],
            *offset,
        )?;

        *offset += 1;

        Ok(jive_output)
    }
    fn assign_root_verification_optimized(
        &self,
        region: &mut Region<'_, F>,
        config: &OptimizedMerkleConfig,
        offset: &mut usize,
        computed_root: F,
        expected_root: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        // 激活根验证约束选择器
        enable_fixed_selectors(
            region,
            "final checksum",
            &[config.q1, config.qo],
            &[config.q3, config.q2, config.q4],
            *offset,
        )?;

        let cells = assign_advice_batch(
            region,
            &config.advices,
            Some(&[
                "computed_root",
                "unused_w2",
                "unused_w3",
                "unused_w4",
                "expected_root",
            ]),
            &[computed_root, F::ZERO, F::ZERO, F::ZERO, expected_root],
            *offset,
        )?;

        *offset += 1;

        Ok(cells[4].clone())
    }

    /// 应用单轮Anemoi变换
    fn apply_anemoi_round(
        &self,
        jive_x: &mut [F; 2],
        jive_y: &mut [F; 2],
        round: usize,
        constants: &AnemoiConstants<F>,
    ) {
        // 轮密钥添加
        jive_x[0] += constants.round_keys_x[round][0];
        jive_x[1] += constants.round_keys_x[round][1];
        jive_y[0] += constants.round_keys_y[round][0];
        jive_y[1] += constants.round_keys_y[round][1];

        // 线性层变换 (MDS矩阵)
        let temp_x0 = jive_x[0] + constants.generator * jive_x[1];
        let temp_x1 =
            constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
        jive_x[0] = temp_x0;
        jive_x[1] = temp_x1;

        let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
        let temp_y1 =
            constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
        jive_y[0] = temp_y0;
        jive_y[1] = temp_y1;

        // 状态混合 (PHT)
        for i in 0..2 {
            jive_y[i] += jive_x[i];
            jive_x[i] += jive_y[i];
        }

        // S-box变换
        for i in 0..2 {
            jive_x[i] -= constants.generator * jive_y[i].square();
            jive_y[i] -= jive_x[i].pow_vartime(&constants.alpha_inv);
            jive_x[i] += constants.generator * jive_y[i].square() + constants.generator_inv;
        }
    }

    /// 应用最终变换
    fn apply_final_transformations(
        &self,
        jive_x: &mut [F; 2],
        jive_y: &mut [F; 2],
        constants: &AnemoiConstants<F>,
    ) {
        // 最终线性层变换
        let temp_x0 = jive_x[0] + constants.generator * jive_x[1];
        let temp_x1 =
            constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
        jive_x[0] = temp_x0;
        jive_x[1] = temp_x1;

        let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
        let temp_y1 =
            constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
        jive_y[0] = temp_y0;
        jive_y[1] = temp_y1;

        // 最终状态混合
        for i in 0..2 {
            jive_y[i] += jive_x[i];
            jive_x[i] += jive_y[i];
        }
    }
}

/// 优化的Anemoi Jive哈希函数 (对应电路逻辑)
pub fn optimized_anemoi_jive_hash<F: PrimeField>(left: F, middle: F, right: F, padding: F) -> F {
    let constants = AnemoiConstants::<F>::new();
    let mut jive_x = [left, middle];
    let mut jive_y = [right, padding];

    let sum_before_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];

    // 14轮Anemoi变换
    for round in 0..14 {
        // 轮密钥添加
        jive_x[0] += constants.round_keys_x[round][0];
        jive_x[1] += constants.round_keys_x[round][1];
        jive_y[0] += constants.round_keys_y[round][0];
        jive_y[1] += constants.round_keys_y[round][1];

        // 线性层变换
        let temp_x0 = jive_x[0] + constants.generator * jive_x[1];
        let temp_x1 =
            constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
        jive_x[0] = temp_x0;
        jive_x[1] = temp_x1;

        let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
        let temp_y1 =
            constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
        jive_y[0] = temp_y0;
        jive_y[1] = temp_y1;

        // 状态混合
        for i in 0..2 {
            jive_y[i] += jive_x[i];
            jive_x[i] += jive_y[i];
        }

        // S-box变换
        for i in 0..2 {
            jive_x[i] -= constants.generator * jive_y[i].square();
            jive_y[i] -= jive_x[i].pow_vartime(&constants.alpha_inv);
            jive_x[i] += constants.generator * jive_y[i].square() + constants.generator_inv;
        }
    }

    // 最终变换
    let temp_x0 = jive_x[0] + constants.generator * jive_x[1];
    let temp_x1 = constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
    jive_x[0] = temp_x0;
    jive_x[1] = temp_x1;

    let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
    let temp_y1 = constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
    jive_y[0] = temp_y0;
    jive_y[1] = temp_y1;

    // 最终状态混合
    for i in 0..2 {
        jive_y[i] += jive_x[i];
        jive_x[i] += jive_y[i];
    }

    let sum_after_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];
    sum_before_perm + sum_after_perm
}

/// 使用优化约束计算Merkle根
pub fn compute_merkle_root_optimized<F: PrimeField>(
    leaf: F,
    siblings: &[(F, F)],    // (sibling1, sibling2) pairs
    path_indices: &[usize], // 0=Left, 1=Middle, 2=Right
) -> F {
    let mut current = leaf;

    for (i, &index) in path_indices.iter().enumerate() {
        let (sibling1, sibling2) = siblings[i];

        let (left, middle, right) = match index {
            0 => (current, sibling1, sibling2), // Left
            1 => (sibling1, current, sibling2), // Middle
            2 => (sibling1, sibling2, current), // Right
            _ => panic!("Invalid path index: {}", index),
        };

        current = optimized_anemoi_jive_hash(left, middle, right, F::ZERO);
    }

    current
}
