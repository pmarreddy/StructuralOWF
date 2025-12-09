# Zero-Knowledge Proofs: Cryptographic Applications

**Location**: `lean/Layer5_Applications/Crypto/ZeroKnowledge/`

This module contains Zero-Knowledge proof primitives derived from the L* OWF construction.

## Architecture

```
Layer 5: P≠NP (main result) + Applications
    └── Crypto/
        ├── ZeroKnowledge/     -- ZK proofs for NP (this module)
        ├── PRG/               -- Pseudorandom generators
        └── Cryptomania/       -- Public-key primitives
```

## What We Get From OWF

| Primitive | Status | Security Basis |
|-----------|--------|----------------|
| **ZK for NP** | Implemented | OWF → Commitment → GMW |
| Commitments | Future | OWF → PRG → Hiding+Binding |
| PRG | Future | Håstad et al. construction |
| Digital Signatures | Future | OWF direct construction |

## What We Don't Get (Impagliazzo-Rudich)

- Public-key encryption (needs trapdoor structure)
- Key agreement (needs DDH/LWE assumptions)

## ZeroKnowledge Module

### Path 2 (Direct) Implementation

The L* OWF directly encodes an NP relation:

```
R(φ, x*, r) ≡ WellFormedRandomness(φ, r) ∧ plant(φ, r) = x*
```

**Key insight**: This IS the NP statement "I know satisfying assignment for φ"
because `WellFormedRandomness` requires `φ.satisfies(r.assignment)`.

### Files

- `NPRelation.lean` - NP relation R(φ, x*, r) with poly-time verifier
- `SigmaProtocol.lean` - Three-move Sigma protocol for R
- `SecurityProofs.lean` - Completeness, Soundness, Zero-Knowledge theorems

### Security Properties

1. **Completeness**: Honest prover with valid r always convinces verifier
2. **Soundness**: Reduces to OWF inversion (hard by SCL/Theorem 8.A)
3. **Zero-Knowledge**: Simulator produces indistinguishable transcripts

## Trust Boundary

All security reduces to L* OWF hardness, which is proven (not assumed) via SCL.
This gives **unconditionally secure** ZK for NP - no cryptographic assumptions needed.

---

**Last Updated**: 2025-12-09 (fixed layer numbering, added location and footer)
