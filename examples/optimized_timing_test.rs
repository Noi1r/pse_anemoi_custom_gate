use halo2_proofs::{
    arithmetic::Field,
    dev::MockProver,
    halo2curves::bn256::Fr,
};
use rand::rngs::OsRng;
use std::time::Instant;

use pse_anemoi_custom_gate::{
    circuit_complete::{CompleteMerkleMembershipCircuit, complete_anemoi_jive_hash},
    circuit_optimized::{OptimizedMerkleMembershipCircuit, optimized_anemoi_jive_hash, MerkleProofNode, MerklePosition},
    circuit_exact_anemoi_hash,
};

fn main() {
    println!("🔥 PSE Anemoi Custom Gate - 优化版本性能对比测试");
    println!("================================================================");
    
    // 测试参数
    let k = 14; // Circuit size parameter
    let tree_depth = 8; // Merkle tree depth
    
    println!("📊 测试配置:");
    println!("   - Circuit size parameter (k): {}", k);
    println!("   - Merkle tree depth: {}", tree_depth);
    println!("   - Field: BN256 scalar field");
    println!();
    
    // 生成测试数据
    println!("🎲 生成随机测试数据...");
    let test_data = generate_test_data(tree_depth);
    println!("   ✅ 测试数据生成完成");
    println!();
    
    // 验证哈希函数一致性
    println!("🔍 验证哈希函数一致性...");
    verify_hash_consistency();
    println!();
    
    // // 测试完整版电路
    // println!("📈 测试完整版电路 (CompleteMerkleMembershipCircuit):");
    // test_complete_circuit(k, &test_data);
    // println!();
    
    // 测试优化版电路
    println!("🚀 测试优化版电路 (OptimizedMerkleMembershipCircuit):");
    test_optimized_circuit(k, &test_data);
    println!();
    
    println!("🎯 性能对比测试完成!");
    println!("================================================================");
}

#[derive(Clone, Debug)]
struct TestData {
    leaf_value: Fr,
    merkle_path: Vec<MerkleProofNode<Fr>>,
    expected_root: Fr,
}

fn generate_test_data(depth: usize) -> TestData {
    use rand::Rng;
    let mut rng = OsRng;
    
    // 生成随机叶子值
    let leaf_value = Fr::random(&mut rng);
    let mut current_hash = leaf_value;
    let mut merkle_path = Vec::new();
    
    // 生成随机Merkle路径
    for level in 0..depth {
        let position = match rng.gen_range(0..3) {
            0 => MerklePosition::Left,
            1 => MerklePosition::Middle,
            _ => MerklePosition::Right,
        };
        
        let sibling1 = Fr::random(&mut rng);
        let sibling2 = Fr::random(&mut rng);
        
        // 根据位置确定哈希输入
        let (left, middle, right) = match position {
            MerklePosition::Left => (current_hash, sibling1, sibling2),
            MerklePosition::Middle => (sibling1, current_hash, sibling2),
            MerklePosition::Right => (sibling1, sibling2, current_hash),
        };
        
        // 计算父哈希 (使用精确的电路逻辑)
        current_hash = circuit_exact_anemoi_hash(left, middle, right, Fr::from(level as u64));
        
        merkle_path.push(MerkleProofNode {
            current_hash: match position {
                MerklePosition::Left => left,
                MerklePosition::Middle => middle,
                MerklePosition::Right => right,
            },
            sibling1,
            sibling2,
            position,
        });
    }
    
    TestData {
        leaf_value,
        merkle_path,
        expected_root: current_hash,
    }
}

fn verify_hash_consistency() {
    let mut rng = OsRng;
    
    // 生成随机测试向量
    let left = Fr::random(&mut rng);
    let middle = Fr::random(&mut rng);
    let right = Fr::random(&mut rng);
    let padding = Fr::ZERO;
    
    // 计算三种哈希函数的结果
    let exact_hash = circuit_exact_anemoi_hash(left, middle, right, padding);
    let complete_hash = complete_anemoi_jive_hash(left, middle, right, padding);
    let optimized_hash = optimized_anemoi_jive_hash(left, middle, right, padding);
    
    println!("   📋 哈希函数一致性检查:");
    println!("      - 精确版本 (circuit_exact): {:?}", exact_hash);
    println!("      - 完整版本 (complete):       {:?}", complete_hash);
    println!("      - 优化版本 (optimized):      {:?}", optimized_hash);
    
    if exact_hash == complete_hash && complete_hash == optimized_hash {
        println!("   ✅ 哈希函数一致性验证通过");
    } else {
        println!("   ❌ 哈希函数一致性验证失败!");
        println!("      exact == complete: {}", exact_hash == complete_hash);
        println!("      complete == optimized: {}", complete_hash == optimized_hash);
    }
}

fn test_complete_circuit(k: u32, test_data: &TestData) {
    // Convert MerkleProofNode from optimized to complete module
    let merkle_path: Vec<pse_anemoi_custom_gate::circuit_complete::MerkleProofNode<Fr>> = test_data.merkle_path.iter().map(|node| {
        pse_anemoi_custom_gate::circuit_complete::MerkleProofNode {
            current_hash: node.current_hash,
            sibling1: node.sibling1,
            sibling2: node.sibling2,
            position: match node.position {
                MerklePosition::Left => pse_anemoi_custom_gate::circuit_complete::MerklePosition::Left,
                MerklePosition::Middle => pse_anemoi_custom_gate::circuit_complete::MerklePosition::Middle,
                MerklePosition::Right => pse_anemoi_custom_gate::circuit_complete::MerklePosition::Right,
            },
        }
    }).collect();
    
    let circuit = CompleteMerkleMembershipCircuit {
        leaf_value: test_data.leaf_value,
        merkle_path,
        expected_root: test_data.expected_root,
    };
    
    // 计算约束系统信息
    let start = Instant::now();
    let prover = MockProver::run(k, &circuit, vec![vec![test_data.expected_root, test_data.leaf_value]]).unwrap();
    let mock_time = start.elapsed();
    
    println!("   🔧 约束系统分析:");
    println!("      - Mock prover 构建时间: {:?}", mock_time);
    
    // 验证约束
    let start = Instant::now();
    match prover.verify() {
        Ok(_) => {
            let verify_time = start.elapsed();
            println!("      - 约束验证时间: {:?}", verify_time);
            println!("   ✅ 完整版电路约束验证通过");
        }
        Err(failures) => {
            println!("   ❌ 完整版电路约束验证失败:");
            for failure in failures.iter().take(3) {
                println!("      {:?}", failure);
            }
            if failures.len() > 3 {
                println!("      ... 还有 {} 个错误", failures.len() - 3);
            }
        }
    }
    
    // 性能分析
    println!("   📊 性能指标:");
    println!("      - 使用列数: 12 advice + 8 selectors");
    println!("      - 约束门数: 8个专用约束门"); 
    println!("      - 电路行数: ~{} (估算)", test_data.merkle_path.len() * 56 + 20);
}

fn test_optimized_circuit(k: u32, test_data: &TestData) {
    let circuit = OptimizedMerkleMembershipCircuit {
        leaf_value: test_data.leaf_value,
        merkle_path: test_data.merkle_path.clone(),
        expected_root: test_data.expected_root,
    };
    
    // 计算约束系统信息
    let start = Instant::now();
    let prover_result = MockProver::run(k, &circuit, vec![vec![test_data.expected_root, test_data.leaf_value]]);
    let mock_time = start.elapsed();
    
    println!("   🔧 约束系统分析:");
    println!("      - Mock prover 构建时间: {:?}", mock_time);
    
    match prover_result {
        Ok(prover) => {
            // 验证约束
            let start = Instant::now();
            match prover.verify() {
                Ok(_) => {
                    let verify_time = start.elapsed();
                    println!("      - 约束验证时间: {:?}", verify_time);
                    println!("   ✅ 优化版电路约束验证通过");
                }
                Err(failures) => {
                    println!("   ❌ 优化版电路约束验证失败:");
                    for failure in failures.iter().take(3) {
                        println!("      {:?}", failure);
                    }
                    if failures.len() > 3 {
                        println!("      ... 还有 {} 个错误", failures.len() - 3);
                    }
                }
            }
        }
        Err(e) => {
            println!("   ❌ Mock prover 构建失败:");
            println!("      错误: {:?}", e);
        }
    }
    
    // 性能分析
    println!("   📊 性能指标:");
    println!("      - 使用列数: 5 advice + 14 fixed (TurboPlonk)");
    println!("      - 约束门数: 3个合并约束门");
    println!("      - 电路行数: ~{} (估算)", test_data.merkle_path.len() * 18 + 10);
    println!("      - 理论优化: ~{}% 列数减少", ((12.0 - 5.0) / 12.0 * 100.0) as u32);
}