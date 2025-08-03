pub mod anemoi_constants;
pub mod circuit_complete;
pub mod circuit_optimized;
pub(crate) mod utils;

pub use circuit_complete::{
    complete_anemoi_jive_hash, compute_merkle_root_complete, CompleteMerkleConfig,
    CompleteMerkleMembershipCircuit,
};

pub use circuit_optimized::{
    compute_merkle_root_optimized, optimized_anemoi_jive_hash, OptimizedMerkleConfig,
    OptimizedMerkleMembershipCircuit,
};

pub use anemoi_constants::AnemoiConstants;

use ff::PrimeField;

pub fn circuit_exact_anemoi_hash<F: PrimeField>(left: F, middle: F, right: F, padding: F) -> F {
    let constants = AnemoiConstants::<F>::new();

    let mut jive_x = [left, middle];
    let mut jive_y = [right, padding];

    let sum_before_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];

    for round in 0..14 {
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

        // 状态混合 (PHT: y += x, x += y)
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

    // 最终变换 (对应电路中的最终MDS + PHT)
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

    // 计算sum_after_perm
    let sum_after_perm = jive_x[0] + jive_x[1] + jive_y[0] + jive_y[1];

    // Jive输出：sum_before_perm + sum_after_perm
    sum_before_perm + sum_after_perm
}

pub fn compute_merkle_root_exact<F: PrimeField>(leaf: F, elements: &[F], indices: &[F]) -> F {
    let mut current_hash = leaf;

    for i in 0..elements.len() {
        let sibling1 = elements[i];
        let sibling2 = F::ZERO; // 对于二叉树，第二个兄弟节点为0
        let index = indices[i];

        // 根据位置确定哈希参数顺序
        let (left_hash, middle_hash, right_hash) = if index == F::ZERO {
            // Left position: (current, sibling1, sibling2)
            (current_hash, sibling1, sibling2)
        } else {
            // Right position: (sibling1, current, sibling2)
            (sibling1, current_hash, sibling2)
        };

        // 使用精确的电路逻辑计算哈希
        current_hash = circuit_exact_anemoi_hash(left_hash, middle_hash, right_hash, F::ZERO);
    }

    current_hash
}
