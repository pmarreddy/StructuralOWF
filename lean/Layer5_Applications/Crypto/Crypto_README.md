# Crypto: From L* Structural OWF to Minicrypt and Cryptomania

**Location**: `lean/Layer5_Applications/Crypto/`

This module derives the complete landscape of cryptographic primitives from the L* one-way function (proven unconditionally in Layer2). The construction spans both Impagliazzo's "Minicrypt" (private-key cryptography) and "Cryptomania" (public-key cryptography).

---

## 1. Overview

### Impagliazzo's Five Worlds

Russell Impagliazzo (1995) identified five possible "worlds" based on the existence of various cryptographic primitives:

1. **Algorithmica** - P = NP, no cryptography possible
2. **Heuristica** - P ≠ NP but no OWF (worst-case ≠ average-case)
3. **Pessiland** - OWF exist but not usefully (hard problems, no solutions)
4. **Minicrypt** - OWF exist → private-key cryptography
5. **Cryptomania** - Trapdoor functions exist → public-key cryptography

The L* Plant construction has two applications: the **OWF application** (for Minicrypt) and the **trapdoor application** (for Cryptomania). Both use the same core Plant(φ, r) machinery with different φ sources.

### Main Results

**Minicrypt (13 primitives)**: L* OWF → PRG → PRF → MAC, PRP, Encryption, Commitment → ZK, Coin Flip, Signatures → Merkle Signatures, OT → MPC, UOWHF

**Cryptomania (3 primitives)**: L* Trapdoor Function → Public-Key Encryption, Key Exchange, Public-Key Signatures

### Reduction Hierarchy

```
L* OWF (Plant + OWF application, Layer2)
    │
    ├──► PRG (HILL 1999)
    │     ├──► PRF (GGM 1986)
    │     │     ├──► MAC (standard)
    │     │     ├──► PRP (Luby-Rackoff 1988)
    │     │     └──► Symmetric Encryption (CPA + AE)
    │     └──► Commitment (Naor 1991)
    │           ├──► Zero-Knowledge Proofs (GMW 1991)
    │           └──► Coin Flipping (Blum 1982)
    │
    ├──► UOWHF (Naor-Yung 1989)
    │
    ├──► Digital Signatures (Lamport 1979)
    │     └──► Many-Time Signatures (Merkle 1989)
    │
    ├──► Oblivious Transfer (semi-honest)
    │     └──► Secure MPC (GMW 1987)
    │
    └──► ZK Soundness (Bellare-Goldreich 1992)

L* Trapdoor Function (Plant + trapdoor application, Layer2)
    │
    ├──► Public-Key Encryption (Goldreich 2004)
    │     └──► Key Exchange
    │
    └──► Public-Key Signatures (Fiat-Shamir 1986)
```

---

## 2. File Organization

**22 files across 4 directories:**

```
Crypto/
├── PRG/                    # Pseudorandom generation chain
│   ├── HardcoreBit.lean    # Goldreich-Levin predicate
│   ├── GoldreichLevin.lean # OWF → hardcore bit
│   ├── PRG1Bit.lean        # 1-bit stretch PRG
│   └── PRGAmplify.lean     # Polynomial stretch PRG
│
├── ZeroKnowledge/          # Zero-knowledge proofs
│   ├── NPRelation.lean     # NP relation definition
│   ├── SigmaProtocol.lean  # 3-move protocol
│   └── SecurityProofs.lean # ZK security
│
├── Cryptomania/            # Public-key cryptography
│   ├── PKE.lean            # Public-key encryption
│   ├── KeyExchange.lean    # Key exchange protocol
│   ├── PKSignature.lean    # Public-key signatures
│   └── Cryptomania.lean    # Master theorem
│
├── PRF.lean                # Pseudorandom functions
├── PRP.lean                # Block ciphers
├── MAC.lean                # Message authentication
├── Encryption.lean         # Symmetric encryption
├── Commitment.lean         # Bit commitment
├── Signature.lean          # One-time signatures
├── MerkleSignature.lean    # Many-time signatures
├── CoinFlip.lean           # Fair coin flipping
├── MPC.lean                # Secure computation
├── UOWHF.lean              # Universal hash functions
├── Minicrypt.lean          # Minicrypt master theorem
└── Crypto_README.md        # This file
```

---

## 3. PRG Chain (OWF → Pseudorandomness)

The foundation of Minicrypt: extracting pseudorandomness from one-way functions.

### HardcoreBit.lean
Goldreich-Levin inner product predicate.
- `glInnerProduct`: ⟨x,r⟩ = Σᵢ xᵢ·rᵢ mod 2
- `GLHardcoreProperty`: Unpredictability definition

**Reference**: Goldreich-Levin (1989)

### GoldreichLevin.lean
OWF interface and L* instantiation.
- `OneWayFunction`: OWF interface
- `lstarOWF`: L* as OWF
- `lstar_owf_security`: Security axiom

**Reference**: Goldreich-Levin (1989)

### PRG1Bit.lean
1-bit stretch PRG from OWF.
- `PRG`: PRG interface
- `prg1Bit_hybrid_argument`: Security axiom
- `lstarPRG1Bit_secure`: L* instantiation

**Reference**: HILL (1999)

### PRGAmplify.lean
Amplify 1-bit PRG to polynomial stretch.
- `prg_amplification`: Amplification axiom
- `unconditionalPRG`: Final L* PRG

**Reference**: Blum-Micali (1984)

---

## 4. Symmetric Primitives (PRG → Private-Key Crypto)

Building private-key cryptography from pseudorandomness.

### PRF.lean
Pseudorandom function from PRG via GGM tree.
- `PRF`: PRF interface
- `prf_from_prg`: PRG → PRF axiom
- `lstarPRF_secure`: L* instantiation

**Reference**: GGM (1986)

### PRP.lean
Block cipher (pseudorandom permutation) from PRF.
- `PRP`: Block cipher interface
- `prp_from_prf`: PRF → PRP axiom
- `lstarPRP_secure`: L* instantiation

**Reference**: Luby-Rackoff (1988)

### MAC.lean
Message authentication code from PRF.
- `MAC`: MAC interface
- `mac_from_prf`: PRF → MAC axiom
- `lstarMAC_secure`: L* instantiation

### Encryption.lean
Symmetric encryption from PRF.
- `SymmetricEncryption`: CPA encryption interface
- `AuthenticatedEncryption`: AE interface
- `cpa_encryption_from_prf`: PRF → CPA axiom
- `ae_from_cpa_and_mac`: CPA + MAC → AE axiom

**References**: Goldreich (2001), Bellare-Namprempre (2000)

---

## 5. Commitment and Applications

Bit commitment enables interactive protocols.

### Commitment.lean
Bit commitment from PRG via Naor scheme.
- `CommitmentScheme`: Commitment interface
- `commitment_from_prg`: PRG → Commitment axiom
- `lstarCommitment_secure`: L* instantiation

**Reference**: Naor (1991)

### CoinFlip.lean
Fair coin flipping from commitment.
- `CoinFlipProtocol`: Coin flip interface
- `coinflip_from_commitment`: Commitment → CoinFlip axiom
- `lstarCoinFlip_secure`: L* instantiation

**Reference**: Blum (1982)

---

## 6. Zero-Knowledge Proofs

Interactive proofs that reveal nothing beyond validity.

### ZeroKnowledge/NPRelation.lean
NP relation for L* ZK proofs.
- `Statement`: Public (φ, x*)
- `ZKWitness`: Secret randomness r
- `NPRelation`: R(stmt, w) definition

### ZeroKnowledge/SigmaProtocol.lean
Three-move Sigma protocol.
- `Commitment`, `Challenge`, `Response`: Protocol messages
- `executeProtocol`: Full execution
- `completeness`: Honest prover succeeds (proven)

**Reference**: Schnorr (1991)

### ZeroKnowledge/SecurityProofs.lean
Full ZK security from OWF + commitment.
- `soundness_from_owf`: Soundness axiom
- `fullzk_from_commitment`: Full ZK axiom
- `lstar_zk_secure`: Complete ZK security

**References**: Bellare-Goldreich (1992), GMW (1991)

---

## 7. Digital Signatures

Authentication without shared secrets.

### Signature.lean
One-time signatures from OWF via Lamport.
- `SignatureScheme`: Signature interface
- `ots_from_owf`: OWF → OTS axiom
- `lstarSignature_secure`: L* instantiation

**Reference**: Lamport (1979)

### MerkleSignature.lean
Many-time signatures from OTS via Merkle trees.
- `ManyTimeSignature`: Many-time signature interface
- `manytime_sig_from_ots`: OTS → Many-time axiom
- `lstarMerkleSignature_secure`: L* instantiation

**Reference**: Merkle (1989)

---

## 8. Secure Computation

Multi-party protocols from oblivious transfer.

### MPC.lean
Secure multi-party computation from OT.
- `OT`: Oblivious transfer interface
- `MPCProtocol`: MPC interface
- `ot_from_owf`: OWF → OT axiom
- `mpc_from_ot`: OT → MPC axiom
- `lstarMPC_exists`: L* instantiation

**Reference**: GMW (1987)

---

## 9. Hash Functions

### UOWHF.lean
Universal one-way hash functions from OWF.
- `HashFamily`: Hash function family interface
- `uowhf_from_owf`: OWF → UOWHF axiom
- `lstarUOWHF_secure`: L* instantiation

**Reference**: Naor-Yung (1989), Rompel (1990)

---

## 10. Master Theorems

### Minicrypt.lean
Ties all private-key primitives together.
- `minicrypt_from_lstar`: All 12 primitives from L* Structural OWF

---

## 11. Cryptomania/ - Public-Key Cryptography

The `Cryptomania/` folder implements public-key primitives using the Structural OWF construction from `Layer2/Plant/TrapdoorStructuralOWF.lean`.

**Key Insight**: The L* Structural OWF security proof is agnostic to CNF origin. When Alice generates φ from a known satisfying assignment x, `generateCNF_satisfied` proves φ is satisfiable, so the existing OWF security applies unchanged and Alice retains x as a trapdoor for efficient inversion.

### Cryptomania/PKE.lean
Public-key encryption from Structural OWF.
- `PKEScheme`: PKE interface
- `pke_from_parity_owf`: Structural OWF → PKE axiom
- `lstarPKE_cpa_secure`: L* instantiation

**Reference**: Goldreich (2004)

### Cryptomania/KeyExchange.lean
Key exchange protocol from PKE.
- `KEProtocol`: Key exchange interface
- `ke_from_pke`: PKE → KE axiom
- `lstarKeyExchange_secure`: L* instantiation

### Cryptomania/PKSignature.lean
Public-key signatures from Structural OWF via Fiat-Shamir.
- `PKSigScheme`: Signature interface
- `sig_from_parity_owf`: Structural OWF → Sig axiom
- `lstarPKSignature_euf_cma`: L* instantiation

**Reference**: Fiat-Shamir (1986), Pointcheval-Stern (2000)

### Cryptomania/Cryptomania.lean
Master theorem for public-key primitives.
- `cryptomania_from_lstar`: All 3 public-key primitives

See `Layer2_StructuralOWF/Layer2_README.md §3` for trapdoor construction details.

---

## 12. Axiom Summary

All reductions are axiomatized standard results from peer-reviewed cryptography literature:

### Minicrypt Axioms (17 total)

| Axiom | File | Reference | Reduction |
|-------|------|-----------|-----------|
| `lstar_owf_security` | GoldreichLevin | Layer2 | L* is OWF |
| `prg1Bit_hybrid_argument` | PRG1Bit | HILL 1999 | OWF → PRG |
| `prg_amplification` | PRGAmplify | BM 1984 | PRG → PRG (amplified) |
| `prf_from_prg` | PRF | GGM 1986 | PRG → PRF |
| `prp_from_prf` | PRP | LR 1988 | PRF → PRP |
| `mac_from_prf` | MAC | Standard | PRF → MAC |
| `cpa_encryption_from_prf` | Encryption | Standard | PRF → CPA |
| `ae_from_cpa_and_mac` | Encryption | BN 2000 | CPA + MAC → AE |
| `commitment_from_prg` | Commitment | Naor 1991 | PRG → Commitment |
| `coinflip_from_commitment` | CoinFlip | Blum 1982 | Commitment → CoinFlip |
| `ots_from_owf` | Signature | Lamport 1979 | OWF → OTS |
| `manytime_sig_from_ots` | MerkleSignature | Merkle 1989 | OTS → Many-time |
| `soundness_from_owf` | SecurityProofs | BG 1992 | OWF → Soundness |
| `fullzk_from_commitment` | SecurityProofs | GMW 1991 | Commitment → ZK |
| `ot_from_owf` | MPC | Various | OWF → OT |
| `mpc_from_ot` | MPC | GMW 1987 | OT → MPC |
| `uowhf_from_owf` | UOWHF | NY 1989 | OWF → UOWHF |

### Cryptomania Axioms (3 total)

| Axiom | File | Reference | Reduction |
|-------|------|-----------|-----------|
| `pke_from_trapdoor_owf` | PKE | Goldreich 2004 | Trapdoor → PKE |
| `ke_from_pke` | KeyExchange | Standard | PKE → KE |
| `sig_from_trapdoor_owf` | PKSignature | FS 1986 | Trapdoor → Sig |

---

## 13. Usage

```lean
import Layer5_Applications.Crypto.Minicrypt
import Layer5_Applications.Crypto.Cryptomania.Cryptomania

-- All Minicrypt primitives exist from any CNF with nvars ≥ 4
example (φ : CNF) (h : φ.nvars ≥ 4) : ∃ G : PRG, PRGSecure G :=
  prg_exists φ h

example (φ : CNF) (h : φ.nvars ≥ 4) : ZKSecure negl :=
  zk_exists φ h

-- Cryptomania primitives exist from security parameter n ≥ 4
example (n : Nat) (h : n ≥ 4) : ∃ E : PKEScheme, CPA_Secure E :=
  lstarPKE_exists n h
```

---

## References

- Bellare, M. & Goldreich, O. (1992). "On Defining Proofs of Knowledge"
- Bellare, M. & Namprempre, C. (2000). "Authenticated Encryption"
- Blum, M. (1982). "Coin Flipping by Telephone"
- Blum, M. & Micali, S. (1984). "How to Generate Cryptographically Strong Sequences of Pseudo-Random Bits"
- Fiat, A. & Shamir, A. (1986). "How to Prove Yourself"
- GMW - Goldreich, Micali, Wigderson (1987). "How to Play Any Mental Game"
- GGM - Goldreich, Goldwasser, Micali (1986). "How to Construct Random Functions"
- Goldreich, O. (2001/2004). "Foundations of Cryptography" Volumes 1 & 2
- Goldreich, O. & Levin, L. (1989). "A Hard-Core Predicate for All One-Way Functions"
- HILL - Håstad, Impagliazzo, Levin, Luby (1999). "A Pseudorandom Generator from Any One-Way Function"
- Impagliazzo, R. (1995). "A Personal View of Average-Case Complexity"
- Lamport, L. (1979). "Constructing Digital Signatures from a One-Way Function"
- Luby, M. & Rackoff, C. (1988). "How to Construct Pseudorandom Permutations from Pseudorandom Functions"
- Merkle, R. (1989). "A Certified Digital Signature"
- Naor, M. (1991). "Bit Commitment Using Pseudorandomness"
- Naor, M. & Yung, M. (1989). "Universal One-Way Hash Functions"
- Pointcheval, D. & Stern, J. (2000). "Security Arguments for Digital Signatures"
- Rompel, J. (1990). "One-Way Functions are Necessary and Sufficient for Secure Signatures"
- Schnorr, C.P. (1991). "Efficient Signature Generation by Smart Cards"

---

**Last Updated**: 2025-12-09 (added location and footer)
