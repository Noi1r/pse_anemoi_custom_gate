//! 简单的Anemoi零知识证明时间测试工具
//!
//! 用法：
//! cargo run --example simple_timing_test --release
//!
//! 输出格式：
//! 证明时间(ms) 验证时间(ms)

use ff::Field;
use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr},
    plonk::{create_proof, verify_proof},
    poly::kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    },
    transcript::{Blake2bRead, Blake2bWrite, TranscriptReadBuffer, TranscriptWriterBuffer},
};
use rand::rngs::OsRng;
use std::time::Instant;

use pse_anemoi_custom_gate::{
    circuit_optimized::{MerklePosition, MerkleProofNode, OptimizedMerkleMembershipCircuit},
    complete_anemoi_jive_hash,
};

fn main() {
    let depth: usize = 256;
    let k: u32 = 14;

    // 生成测试数据
    let leaf_value = Fr::from(42);
    let mut merkle_path = Vec::new();
    let mut current_hash = leaf_value;

    // 构建Merkle路径
    for level in 0..depth {
        let sibling1 = Fr::from(100 + level as u64);
        let sibling2 = Fr::from(200 + level as u64);

        // 根据层数选择位置
        let position = match level % 3 {
            0 => MerklePosition::Left,
            1 => MerklePosition::Middle,
            _ => MerklePosition::Right,
        };

        // 计算当前层的哈希
        let (left, middle, right) = match position {
            MerklePosition::Left => (current_hash, sibling1, sibling2),
            MerklePosition::Middle => (sibling1, current_hash, sibling2),
            MerklePosition::Right => (sibling1, sibling2, current_hash),
        };

        merkle_path.push(MerkleProofNode {
            current_hash,
            sibling1,
            sibling2,
            position,
        });
        current_hash = complete_anemoi_jive_hash(left, middle, right, Fr::ZERO);
    }

    let expected_root = current_hash;

    // 创建电路
    let circuit = OptimizedMerkleMembershipCircuit {
        leaf_value,
        merkle_path,
        expected_root,
    };

    // KZG设置
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    let vk = halo2_proofs::plonk::keygen_vk(&params, &circuit).expect("VK生成失败");
    let pk = halo2_proofs::plonk::keygen_pk(&params, vk, &circuit).expect("PK生成失败");

    // 公共输入
    let public_inputs = vec![expected_root, leaf_value];

    // 证明生成时间测试
    let proof_start = Instant::now();
    let mut transcript =
        Blake2bWrite::<_, _, halo2_proofs::transcript::Challenge255<_>>::init(vec![]);
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &params,
        &pk,
        &[circuit.clone()],
        &[&[&public_inputs]],
        OsRng,
        &mut transcript,
    )
    .expect("证明生成失败");
    let proof = transcript.finalize();
    let proof_time = proof_start.elapsed();
    println!("{} ", proof_time.as_millis());

    {
        use halo2_proofs::dev::MockProver;

        let mock_prover =
            MockProver::run(k, &circuit, vec![public_inputs.clone()]).expect("MockProver 运行失败");

        mock_prover.assert_satisfied();
        println!("MockProver 约束验证通过 ✅");
    }

    // 证明验证时间测试
    let verify_start = Instant::now();
    let mut verifier_transcript =
        Blake2bRead::<_, _, halo2_proofs::transcript::Challenge255<_>>::init(&proof[..]);
    let strategy = SingleStrategy::new(&params);
    verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &params,
        pk.get_vk(),
        strategy,
        &[&[&public_inputs]],
        &mut verifier_transcript,
    )
    .expect("证明验证失败");
    let verify_time = verify_start.elapsed();

    // 只输出时间（毫秒）
    println!("{} {}", proof_time.as_millis(), verify_time.as_millis());
}
