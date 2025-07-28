use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Value, Region},
    plonk::{Circuit, ConstraintSystem, Error, Selector, Advice, Column, Expression, Instance, Fixed},
    poly::Rotation,
};
use serde::{Deserialize, Serialize};
use ff::PrimeField;

use crate::anemoi_constants::AnemoiConstants;

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
    pub q1: Selector,
    pub q2: Selector,
    pub q3: Selector,
    pub q4: Selector,
    pub qo: Selector,
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
        
        // TurboPlonk标准选择器
        let q1 = cs.complex_selector();
        let q2 = cs.complex_selector();
        let q3 = cs.complex_selector();
        let q4 = cs.complex_selector();
        let qo = cs.complex_selector();
        let qm1 = cs.complex_selector();
        let qm2 = cs.complex_selector();
        let qc = cs.complex_selector();
        let qecc = cs.complex_selector();
        let qb = cs.complex_selector();
        
        // Anemoi预处理轮密钥
        let qprk1 = cs.fixed_column();
        let qprk2 = cs.fixed_column();
        let qprk3 = cs.fixed_column();
        let qprk4 = cs.fixed_column();
        
        let instance = cs.instance_column();

        // 启用相等约束
        for advice in advices.iter() {
            cs.enable_equality(*advice);
        }
        cs.enable_equality(instance);

        // 📝 基础TurboPlonk约束 (合并所有线性约束)
        cs.create_gate("turbo_plonk_base", |meta| {
            let w1 = meta.query_advice(advices[0], Rotation::cur());
            let w2 = meta.query_advice(advices[1], Rotation::cur());
            let w3 = meta.query_advice(advices[2], Rotation::cur());
            let w4 = meta.query_advice(advices[3], Rotation::cur());
            let wo = meta.query_advice(advices[4], Rotation::cur());
            
            let q1 = meta.query_selector(q1);
            let q2 = meta.query_selector(q2);
            let q3 = meta.query_selector(q3);
            let q4 = meta.query_selector(q4);
            let qo = meta.query_selector(qo);
            let qm1 = meta.query_selector(qm1);
            let qm2 = meta.query_selector(qm2);
            let qc = meta.query_selector(qc);
            let qecc = meta.query_selector(qecc);
            
            vec![
                // TurboPlonk基础约束：q1*w1 + q2*w2 + q3*w3 + q4*w4 + qm1*w1*w2 + qm2*w3*w4 + qc + qecc*w1*w2*w3*w4*wo - qo*wo = 0
                q1 * w1.clone() 
                + q2 * w2.clone() 
                + q3 * w3.clone() 
                + q4 * w4.clone() 
                + qm1 * w1.clone() * w2.clone()
                + qm2 * w3.clone() * w4.clone()
                + qc
                + qecc * w1 * w2 * w3 * w4 * wo.clone()
                - qo * wo
            ]
        });

        // 📝 布尔约束
        cs.create_gate("boolean_constraints", |meta| {
            let w2 = meta.query_advice(advices[1], Rotation::cur());
            let w3 = meta.query_advice(advices[2], Rotation::cur());
            let w4 = meta.query_advice(advices[3], Rotation::cur());
            let qb = meta.query_selector(qb);
            
            vec![
                qb.clone() * w2.clone() * (w2 - Expression::Constant(F::ONE)),
                qb.clone() * w3.clone() * (w3 - Expression::Constant(F::ONE)),
                qb * w4.clone() * (w4 - Expression::Constant(F::ONE)),
            ]
        });

        // 📝 Anemoi约束 (基于reference中的实现)
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
            
            // Anemoi常量
            let g = Expression::Constant(F::from(5u64)); // generator
            let g_inv = Expression::Constant(
                F::from_str_vartime("8755297148735710088898562298102910035419345760166413737479281674630323398247")
                    .unwrap_or(F::ZERO)
            ); // generator_inv
            
            // 计算中间表达式
            let c_prime_1 = w1.clone() + w4.clone() + g.clone() * (w2.clone() + w3.clone()) + qprk3.clone();
            let c_prime_2 = g.clone() * (w1.clone() + w4.clone()) 
                          + (g.clone() * g.clone() + Expression::Constant(F::ONE)) * (w2.clone() + w3.clone()) 
                          + qprk4.clone();
            
            let two = Expression::Constant(F::from(2u64));
            
            vec![
                // Anemoi约束1 - 手动展开5次幂和平方
                qprk3.clone() * (
                    (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone())
                    + g.clone() * c_prime_1.clone() * c_prime_1.clone()
                    - (two.clone() * w1.clone() + w4.clone() + g.clone() * (two.clone() * w2.clone() + w3.clone()) + qprk1)
                ),
                
                // Anemoi约束2 (使用wo而不是w4_next) - 手动展开5次幂和平方
                qprk3.clone() * (
                    (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone())
                    + g.clone() * c_prime_2.clone() * c_prime_2.clone()
                    - (g.clone() * (two.clone() * w1.clone() + w4.clone()) 
                       + (g.clone() * g.clone() + Expression::Constant(F::ONE)) * (two.clone() * w2.clone() + w3.clone())
                       + qprk2)
                ),
                
                // Anemoi约束3 - 手动展开5次幂和平方
                qprk3.clone() * (
                    (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone()) * (c_prime_1.clone() - w3_next.clone())
                    + g.clone() * w3_next.clone() * w3_next.clone() + g_inv.clone() - w1_next
                ),
                
                // Anemoi约束4 (使用wo) - 手动展开5次幂和平方
                qprk3 * (
                    (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone()) * (c_prime_2.clone() - wo.clone())
                    + g.clone() * wo.clone() * wo.clone() + g_inv - w2_next
                ),
            ]
        });

        OptimizedMerkleConfig {
            advices,
            q1, q2, q3, q4, qo, qm1, qm2, qc, qecc, qb,
            qprk1, qprk2, qprk3, qprk4,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let anemoi_constants = AnemoiConstants::<F>::new();

        // 预处理轮密钥数据
        let mut qprk1_data = vec![F::ZERO; 1 << 13]; // k=13的大小
        let mut qprk2_data = vec![F::ZERO; 1 << 13];
        let mut qprk3_data = vec![F::ZERO; 1 << 13];
        let mut qprk4_data = vec![F::ZERO; 1 << 13];
        
        // 在合适的行设置轮密钥
        for round in 0..14 {
            // 假设每轮使用4行，轮密钥在第二行
            let round_key_row = round * 4 + 1;
            if round_key_row < qprk1_data.len() {
                qprk1_data[round_key_row] = anemoi_constants.round_keys_x[round][0];
                qprk2_data[round_key_row] = anemoi_constants.round_keys_x[round][1];
                qprk3_data[round_key_row] = anemoi_constants.round_keys_y[round][0];
                qprk4_data[round_key_row] = anemoi_constants.round_keys_y[round][1];
            }
        }

        // 分配预处理多项式
        layouter.assign_region(
            || "preprocess round keys",
            |mut region| {
                for i in 0..qprk1_data.len() {
                    region.assign_fixed(
                        || format!("qprk1[{}]", i),
                        config.qprk1,
                        i,
                        || Value::known(qprk1_data[i]),
                    )?;
                    region.assign_fixed(
                        || format!("qprk2[{}]", i),
                        config.qprk2,
                        i,
                        || Value::known(qprk2_data[i]),
                    )?;
                    region.assign_fixed(
                        || format!("qprk3[{}]", i),
                        config.qprk3,
                        i,
                        || Value::known(qprk3_data[i]),
                    )?;
                    region.assign_fixed(
                        || format!("qprk4[{}]", i),
                        config.qprk4,
                        i,
                        || Value::known(qprk4_data[i]),
                    )?;
                }
                Ok(())
            },
        )?;

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
                    // 根据位置确定哈希函数参数的顺序
                    let (left_hash, middle_hash, right_hash) = match node.position {
                        MerklePosition::Left => (current_hash, node.sibling1, node.sibling2),
                        MerklePosition::Middle => (node.sibling1, current_hash, node.sibling2),
                        MerklePosition::Right => (node.sibling1, node.sibling2, current_hash),
                    };
                    
                    // 位置验证 (使用TurboPlonk基础约束)
                    self.assign_position_verification_optimized(
                        &mut region, 
                        &config, 
                        &mut offset, 
                        node.position.clone()
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
                        &anemoi_constants,
                    )?;
                }

                // 最终根验证
                self.assign_root_verification_optimized(
                    &mut region,
                    &config,
                    &mut offset,
                    current_hash,
                    self.expected_root,
                )?;

                let root_cell = region.assign_advice(
                    || "expected_root",
                    config.advices[1],
                    offset - 1,
                    || Value::known(self.expected_root),
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
        position: MerklePosition,
    ) -> Result<(), Error> {
        let (is_left, is_middle, is_right) = match position {
            MerklePosition::Left => (F::ONE, F::ZERO, F::ZERO),
            MerklePosition::Middle => (F::ZERO, F::ONE, F::ZERO),
            MerklePosition::Right => (F::ZERO, F::ZERO, F::ONE),
        };

        // 激活选择器
        config.q2.enable(region, *offset)?;
        config.q3.enable(region, *offset)?;
        config.q4.enable(region, *offset)?;
        config.qc.enable(region, *offset)?;
        config.qb.enable(region, *offset)?; // 激活布尔约束

        region.assign_advice(
            || "unused_w1",
            config.advices[0],
            *offset,
            || Value::known(F::ZERO),
        )?;
        region.assign_advice(
            || "is_left",
            config.advices[1],
            *offset,
            || Value::known(is_left),
        )?;
        region.assign_advice(
            || "is_middle",
            config.advices[2],
            *offset,
            || Value::known(is_middle),
        )?;
        region.assign_advice(
            || "is_right",
            config.advices[3],
            *offset,
            || Value::known(is_right),
        )?;
        region.assign_advice(
            || "unused_wo",
            config.advices[4],
            *offset,
            || Value::known(F::ZERO),
        )?;

        *offset += 1;
        Ok(())
    }

    /// 优化的Anemoi Jive CRH实现 (使用5列witness)
    fn assign_optimized_anemoi_jive_crh(
        &self,
        region: &mut Region<'_, F>,
        config: &OptimizedMerkleConfig,
        offset: &mut usize,
        left: F,
        middle: F,
        right: F,
        padding: F,
        constants: &AnemoiConstants<F>,
    ) -> Result<F, Error> {
        let mut jive_x = [left, middle];
        let mut jive_y = [right, padding];
        let sum_before_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];

        // 激活TurboPlonk基础约束选择器
        config.q1.enable(region, *offset)?;
        config.q2.enable(region, *offset)?;
        config.q3.enable(region, *offset)?;
        config.q4.enable(region, *offset)?;
        config.qo.enable(region, *offset)?;

        region.assign_advice(|| "x0", config.advices[0], *offset, || Value::known(jive_x[0]))?;
        region.assign_advice(|| "x1", config.advices[1], *offset, || Value::known(jive_x[1]))?;
        region.assign_advice(|| "y0", config.advices[2], *offset, || Value::known(jive_y[0]))?;
        region.assign_advice(|| "y1", config.advices[3], *offset, || Value::known(jive_y[1]))?;
        region.assign_advice(|| "sum_before", config.advices[4], *offset, || Value::known(sum_before_perm))?;

        *offset += 1;

        // 14轮Anemoi变换 (每轮一行，使用预处理轮密钥)
        for round in 0..14 {
            // 激活Anemoi约束 (通过qprk3非零)
            region.assign_fixed(|| format!("qprk3_round_{}", round), config.qprk3, *offset, || Value::known(F::ONE))?;

            // 存储当前轮状态
            region.assign_advice(
                || format!("round_{}_x0", round),
                config.advices[0],
                *offset,
                || Value::known(jive_x[0]),
            )?;
            region.assign_advice(
                || format!("round_{}_x1", round),
                config.advices[1],
                *offset,
                || Value::known(jive_x[1]),
            )?;
            region.assign_advice(
                || format!("round_{}_y0", round),
                config.advices[2],
                *offset,
                || Value::known(jive_y[0]),
            )?;
            region.assign_advice(
                || format!("round_{}_y1", round),
                config.advices[3],
                *offset,
                || Value::known(jive_y[1]),
            )?;

            // 执行完整的Anemoi轮变换
            self.apply_anemoi_round(&mut jive_x, &mut jive_y, round, constants);

            // wo存储某个中间值（根据约束需要）
            region.assign_advice(
                || format!("round_{}_intermediate", round),
                config.advices[4],
                *offset,
                || Value::known(jive_y[1]), // 可以根据约束调整
            )?;

            *offset += 1;
        }

        // 设置下一行数据以满足Rotation::next()约束
        region.assign_advice(|| "final_x0", config.advices[0], *offset, || Value::known(jive_x[0]))?;
        region.assign_advice(|| "final_x1", config.advices[1], *offset, || Value::known(jive_x[1]))?;
        region.assign_advice(|| "final_y0", config.advices[2], *offset, || Value::known(jive_y[0]))?;
        region.assign_advice(|| "final_y1", config.advices[3], *offset, || Value::known(jive_y[1]))?;

        // 应用最终变换
        self.apply_final_transformations(&mut jive_x, &mut jive_y, constants);

        let sum_after_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];
        let jive_output = sum_before_perm + sum_after_perm;

        region.assign_advice(|| "sum_after", config.advices[4], *offset, || Value::known(sum_after_perm))?;
        *offset += 1;

        // 激活最终输出约束选择器
        config.q1.enable(region, *offset)?;
        config.q2.enable(region, *offset)?;
        config.qo.enable(region, *offset)?;

        region.assign_advice(|| "sum_before_final", config.advices[0], *offset, || Value::known(sum_before_perm))?;
        region.assign_advice(|| "sum_after_final", config.advices[1], *offset, || Value::known(sum_after_perm))?;
        region.assign_advice(|| "unused_w3", config.advices[2], *offset, || Value::known(F::ZERO))?;
        region.assign_advice(|| "unused_w4", config.advices[3], *offset, || Value::known(F::ZERO))?;
        region.assign_advice(|| "jive_output", config.advices[4], *offset, || Value::known(jive_output))?;

        *offset += 1;

        Ok(jive_output)
    }

    /// 最终根验证 (使用TurboPlonk基础约束)
    fn assign_root_verification_optimized(
        &self,
        region: &mut Region<'_, F>,
        config: &OptimizedMerkleConfig,
        offset: &mut usize,
        computed_root: F,
        expected_root: F,
    ) -> Result<(), Error> {
        // 激活根验证约束选择器
        config.q1.enable(region, *offset)?;
        config.q2.enable(region, *offset)?;

        region.assign_advice(|| "computed_root", config.advices[0], *offset, || Value::known(computed_root))?;
        region.assign_advice(|| "expected_root", config.advices[1], *offset, || Value::known(expected_root))?;
        region.assign_advice(|| "unused_w3", config.advices[2], *offset, || Value::known(F::ZERO))?;
        region.assign_advice(|| "unused_w4", config.advices[3], *offset, || Value::known(F::ZERO))?;
        region.assign_advice(|| "unused_wo", config.advices[4], *offset, || Value::known(F::ZERO))?;

        *offset += 1;
        Ok(())
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
        let temp_x1 = constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
        jive_x[0] = temp_x0;
        jive_x[1] = temp_x1;

        let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
        let temp_y1 = constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
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
    }
}

/// 优化的Anemoi Jive哈希函数 (对应电路逻辑)
pub fn optimized_anemoi_jive_hash<F: PrimeField>(
    left: F,
    middle: F,
    right: F,
    padding: F,
) -> F {
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
        let temp_x1 = constants.generator * jive_x[0] + constants.generator_square_plus_one * jive_x[1];
        jive_x[0] = temp_x0;
        jive_x[1] = temp_x1;

        let temp_y0 = jive_y[1] + constants.generator * jive_y[0];
        let temp_y1 = constants.generator * jive_y[1] + constants.generator_square_plus_one * jive_y[0];
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
    siblings: &[(F, F)], // (sibling1, sibling2) pairs
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