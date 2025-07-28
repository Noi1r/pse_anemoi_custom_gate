# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Rust zero-knowledge proof library implementing the Anemoi hash function with Halo2 circuits for Merkle tree membership proofs. The project focuses on academic-grade cryptographic implementations with complete constraint systems.

**Key Technologies:**
- Halo2 (v0.3.0 from PSE fork) - ZK proof system
- Anemoi hash function - Cryptographic permutation optimized for ZK circuits
- BLS12-381/Bn256 elliptic curves
- Merkle trees for authenticated data structures

## Development Commands

### Build and Check
```bash
cargo check              # Quick compilation check
cargo build              # Debug build
cargo build --release    # Release build with optimizations
```

### Testing and Benchmarking
```bash
cargo test               # Run unit tests
cargo run --example simple_timing_test --release  # Performance benchmark
```

### Format and Linting
```bash
cargo fmt                # Format code
cargo clippy             # Run linter
```

## Core Architecture

### Main Components

1. **lib.rs** - Library entry point exposing:
   - `circuit_exact_anemoi_hash()` - Pure computation version
   - `CompleteMerkleMembershipCircuit` - Full academic constraint system
   - `OptimizedMerkleMembershipCircuit` - TurboPlonk-style optimized version (partial)
   - `SimpleMerkleMembershipCircuit` - Simplified demonstration version
   - `AnemoiConstants` - Cryptographic parameters

2. **circuit_complete.rs** - Complete academic implementation:
   - `CompleteMerkleMembershipCircuit` - Full constraint system for Merkle proofs
   - `CompleteMerkleConfig` - 12 advice columns with 8 specialized selectors
   - Detailed constraints for all Anemoi operations (14 rounds)

3. **circuit_optimized.rs** - TurboPlonk-style optimization attempt:
   - Reduced to 5 advice columns (standard TurboPlonk)
   - Combined constraint gates
   - Direct 5th power constraints (based on reference implementation)
   - **Note**: Contains Halo2 selector usage issues, incomplete implementation

4. **circuit_simple.rs** - Working simplified demonstration:
   - 5 advice columns, 3 constraint gates
   - Quadratic constraints instead of 5th power
   - Position verification and basic hash simulation
   - **Note**: Uses different hash function (not cryptographically equivalent)

5. **anemoi_constants.rs** - Cryptographic parameters:
   - Round keys for 14-round Anemoi permutation
   - Field generator constants for BLS12-381 scalar field
   - Alpha inverse for S-box operations

### Circuit Design

The circuit implements a complete Merkle membership proof with 8 constraint gates:
- Position verification (Left/Middle/Right node placement)
- Round key addition (14 rounds)
- Linear layer transformation (MDS matrix operations)
- State mixing (PHT transformations)
- S-box constraints (3-step non-linear operations)
- Round consistency validation
- Final hash output computation
- Root verification

### Field Elements and Constants

- Uses BLS12-381 scalar field for all operations
- Generator value: 5
- 14 rounds of Anemoi permutation
- Support for ternary Merkle trees (3 children per node)

## Important Implementation Details

### Constraint System
- 12 advice columns for witness data
- 8 specialized selectors for different constraint types
- Each Anemoi round requires 4 constraint rows (key addition, linear, mixing, S-box)
- Complete academic-grade implementation with full mathematical verification

### Hash Function
- Implements Anemoi-2-1 variant (2 branches, 1 output)
- Jive compression: sum_before + sum_after permutation
- 14-round security parameter
- Supports 4-ary input (left, middle, right, padding)

### Performance Considerations
- Circuit size scales with Merkle tree depth
- Each tree level adds ~56 constraint rows (14 rounds × 4 steps)
- Memory usage grows linearly with proof depth
- Recommended k=14 for reasonable proof sizes

## Circuit Optimization Analysis

### Identified Optimization Opportunities

Based on analysis of reference implementations, several optimization strategies were identified:

1. **Column Reduction**: From 12 advice columns to 5 (TurboPlonk standard)
2. **Gate Consolidation**: Combine multiple Anemoi operations into fewer constraint gates
3. **Selector Optimization**: Use preprocessed round keys instead of witness storage
4. **Constraint Efficiency**: Direct 5th power constraints instead of decomposed operations
5. **Rotation Optimization**: Better use of Rotation::next() for round connections

### Implementation Challenges

1. **Halo2 Selector Restrictions**: Cannot use selectors in addition expressions
2. **Expression Ownership**: Need careful cloning of Expression objects
3. **Cryptographic Correctness**: Maintaining exact Anemoi specification
4. **Degree Constraints**: 5th power expressions increase constraint degree

### Performance Comparison

The original `circuit_complete.rs` provides:
- Full academic-grade constraint verification
- Complete Anemoi implementation (14 rounds)
- Detailed step-by-step verification
- Proof time: ~349ms (depth=8, k=12)

The optimization attempts show:
- Significant code complexity reduction potential
- Need for careful Halo2 constraint system design
- Trade-offs between verification completeness and efficiency

### Recommendations

1. **For Production**: Use `circuit_complete.rs` for cryptographic correctness
2. **For Research**: Examine reference implementations for constraint patterns
3. **For Learning**: Study `circuit_simple.rs` for basic Halo2 patterns
4. **For Optimization**: Focus on selector usage patterns and expression management

## Testing

The main test is in `examples/simple_timing_test.rs` which:
- Generates a 256-depth Merkle tree
- Creates and proves membership
- Outputs proof/verification times in milliseconds  
- Uses optimized release builds for accurate benchmarking

Additional testing:
- `examples/optimized_timing_test.rs` - Compares different circuit implementations
- Performance benchmarking with different tree depths
- Hash function consistency verification