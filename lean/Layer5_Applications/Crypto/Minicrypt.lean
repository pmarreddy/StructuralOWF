import Layer5_Applications.Crypto.PRG.PRG1Bit
import Layer5_Applications.Crypto.PRG.PRGAmplify
import Layer5_Applications.Crypto.Commitment
import Layer5_Applications.Crypto.PRF
import Layer5_Applications.Crypto.MAC
import Layer5_Applications.Crypto.Signature
import Layer5_Applications.Crypto.PRP
import Layer5_Applications.Crypto.MerkleSignature
import Layer5_Applications.Crypto.CoinFlip
import Layer5_Applications.Crypto.MPC
import Layer5_Applications.Crypto.Encryption
import Layer5_Applications.Crypto.UOWHF
import Layer5_Applications.Crypto.ZeroKnowledge.SecurityProofs

/-! # Minicrypt: All Private-Key Crypto from L* OWF

L* OWF gives all of Minicrypt: PRG, PRF, PRP, Encryption, UOWHF, Commitment, MAC, Signatures, ZK, MPC.

**The Minicrypt World** (Impagliazzo 1995):
- One-way functions exist
- Private-key crypto is possible
- Public-key crypto may not be (requires Structural OWF)

**What We Prove**: L* OWF → All of Minicrypt (12 primitives)

```
L* OWF (Layer2, unconditional)
    │
    ├──► PRG (HILL 1999)
    │     ├──► PRF (GGM 1986)
    │     │     ├──► MAC
    │     │     ├──► PRP (Luby-Rackoff 1988)
    │     │     └──► Encryption (CPA + AE)
    │     └──► Commitment (Naor 1991)
    │           ├──► Full ZK (GMW 1991)
    │           └──► Coin Flipping (Blum 1982)
    │
    ├──► UOWHF (Naor-Yung 1989)
    │
    ├──► Signatures (Lamport 1979)
    │     └──► Many-Time Sig (Merkle 1989)
    │
    ├──► OT (semi-honest)
    │     └──► MPC (GMW 1987)
    │
    └──► Soundness (Bellare-Goldreich 1992)
```

**Reference**: Impagliazzo "Five Worlds" (1995)
-/

namespace LStar.Crypto.Minicrypt

open LStar.StructuralOWF
open LStar.Crypto.PRG
open LStar.Crypto.Commitment
open LStar.Crypto.PRF
open LStar.Crypto.MAC
open LStar.Crypto.Signature
open LStar.Crypto.PRP
open LStar.Crypto.MerkleSignature
open LStar.Crypto.CoinFlip
open LStar.Crypto.MPC
open LStar.Crypto.Encryption
open LStar.Crypto.UOWHF
open LStar.ZK
open LStar.ZK.Security
open LStar.ZK.Sigma

private abbrev negl := Crypto.PRG.negligible

/-! ## Individual Existence Theorems -/

/-- PRG exists from L* OWF. -/
theorem prg_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ G : PRG, PRGSecure G :=
  unconditionalPRG_exists φ h_nvars

/-- PRF exists from L* OWF. -/
theorem prf_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ F : PRF, IsPRFSecure F :=
  lstarPRF_exists φ h_nvars

/-- Commitment exists from L* OWF. -/
theorem commitment_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ C : CommitmentScheme, CommitmentSecureFull C :=
  lstarCommitment_exists φ h_nvars

/-- MAC exists from L* OWF. -/
theorem mac_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ M : MAC, IsMACSecure M :=
  lstarMAC_exists φ h_nvars msgLen

/-- One-time signatures exist from L* OWF. -/
theorem ots_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgBits : Nat) :
    ∃ S : SignatureScheme, IsOTSSecure S :=
  lstarSignature_exists φ h_nvars msgBits

/-- Zero Knowledge exists from L* OWF. -/
theorem zk_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) : ZKSecure negl :=
  lstar_zk_secure φ h_nvars

/-- PRP exists from L* OWF. -/
theorem prp_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (inputLen : Nat) :
    ∃ P : PRP, IsPRPSecure P :=
  lstarPRP_exists φ h_nvars inputLen

/-- Many-time signatures exist from L* OWF. -/
theorem manytime_sig_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgBits depth : Nat) :
    ∃ M : ManyTimeSignature, IsManyTimeSigSecure M :=
  lstarMerkleSignature_exists φ h_nvars msgBits depth

/-- Coin flipping exists from L* OWF. -/
theorem coinflip_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ P : CoinFlipProtocol, CoinFlipSecure P :=
  lstarCoinFlip_exists φ h_nvars

/-- MPC exists from L* OWF. -/
theorem mpc_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (F : TwoPartyFunction) :
    ∃ P : MPCProtocol, MPCSecure F P :=
  lstarMPC_exists φ h_nvars F

/-- CPA encryption exists from L* OWF. -/
theorem cpa_encryption_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ E : SymmetricEncryption, IsCPASecure E :=
  lstarCPAEncryption_exists φ h_nvars msgLen

/-- Authenticated encryption exists from L* OWF. -/
theorem ae_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ AE : AuthenticatedEncryption, AESecure AE :=
  lstarAE_exists φ h_nvars msgLen

/-- UOWHF exists from L* OWF. -/
theorem uowhf_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ H : HashFamily, IsUOWHF H :=
  lstarUOWHF_exists φ h_nvars

/-! ## Master Theorem -/

/-- **Minicrypt Master Theorem**: L* OWF gives all of Minicrypt.

    **Components** (12 primitives):
    1. PRG - Pseudorandom generator
    2. PRF - Pseudorandom function
    3. PRP - Block cipher
    4. Encryption - CPA + Authenticated
    5. UOWHF - Target collision resistant hash
    6. Commitment - Bit commitment
    7. MAC - Message authentication
    8. OTS - One-time signatures
    9. Many-time Sig - Merkle tree signatures
    10. ZK - Zero-knowledge proofs
    11. Coin Flip - Fair coin flipping
    12. MPC - Secure computation -/
theorem minicrypt_from_lstar (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    (∃ G : PRG, PRGSecure G) ∧
    (∃ F : PRF, IsPRFSecure F) ∧
    (∃ C : CommitmentScheme, CommitmentSecureFull C) ∧
    (∀ msgLen : Nat, ∃ M : MAC, IsMACSecure M) ∧
    (∀ msgBits : Nat, ∃ S : SignatureScheme, IsOTSSecure S) ∧
    ZKSecure negl ∧
    (∀ inputLen : Nat, ∃ P : PRP, IsPRPSecure P) ∧
    (∀ msgBits depth : Nat, ∃ M : ManyTimeSignature, IsManyTimeSigSecure M) ∧
    (∃ P : CoinFlipProtocol, CoinFlipSecure P) ∧
    (∀ F : TwoPartyFunction, ∃ P : MPCProtocol, MPCSecure F P) ∧
    (∀ msgLen : Nat, ∃ E : SymmetricEncryption, IsCPASecure E) ∧
    (∀ msgLen : Nat, ∃ AE : AuthenticatedEncryption, AESecure AE) ∧
    (∃ H : HashFamily, IsUOWHF H) :=
  ⟨prg_exists φ h_nvars,
   prf_exists φ h_nvars,
   commitment_exists φ h_nvars,
   mac_exists φ h_nvars,
   ots_exists φ h_nvars,
   zk_exists φ h_nvars,
   prp_exists φ h_nvars,
   manytime_sig_exists φ h_nvars,
   coinflip_exists φ h_nvars,
   mpc_exists φ h_nvars,
   cpa_encryption_exists φ h_nvars,
   ae_exists φ h_nvars,
   uowhf_exists φ h_nvars⟩

end LStar.Crypto.Minicrypt
