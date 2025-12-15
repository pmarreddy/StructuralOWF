import Layer5_Applications.Crypto.Cryptomania.PKE
import Layer5_Applications.Crypto.Cryptomania.KeyExchange
import Layer5_Applications.Crypto.Cryptomania.PKSignature
import Layer5_Applications.Crypto.Minicrypt

/-! # Cryptomania: Public-Key Cryptography from L* Structural OWF

This module establishes that L* OWF enables **Cryptomania** (Impagliazzo 1995):
the world where public-key cryptography is possible.

## Impagliazzo's Five Worlds

1. **Algorithmica** - P = NP, no cryptography
2. **Heuristica** - P ≠ NP but no OWF
3. **Pessiland** - Hard problems exist but unusable
4. **Minicrypt** - OWF exist → private-key crypto
5. **Cryptomania** - Structural OWF exist → public-key crypto

## What We Prove

The L* construction provides **Structural OWF** (Layer2/Plant/TrapdoorStructuralOWF.lean):
- Public key: CNF formula φ generated from known assignment x
- Private key: The satisfying assignment x
- Trapdoor property: Knowing x allows efficient inversion

This enables all public-key primitives via standard reductions.

## References

- Impagliazzo, R. (1995). "A Personal View of Average-Case Complexity"
- Goldreich, O. (2004). "Foundations of Cryptography", Volume 2
-/

namespace LStar.Crypto.Cryptomania

open PKE
open KeyExchange
open PKSignature

open LStar.Crypto.Minicrypt
open LStar.ZK
open LStar.ZK.Sigma  -- For ZKSecure
open LStar.Crypto.PRG
open LStar.Crypto.PRF
open LStar.Crypto.Commitment
open LStar.Crypto.MAC
open LStar.Crypto.Signature
open LStar.Crypto.PRP
open LStar.Crypto.MerkleSignature
open LStar.Crypto.CoinFlip
open LStar.Crypto.MPC
open LStar.Crypto.Encryption
open LStar.Crypto.UOWHF

private abbrev negl := LStar.Crypto.PRG.negligible


/-! ## Master Theorem -/

/-- **Cryptomania Master Theorem**: L* Structural OWF gives public-key crypto.

    From the Structural OWF construction, we derive:
    1. **PKE** - Public-key encryption (CPA-secure)
    2. **Key Exchange** - Secure key agreement
    3. **PK Signatures** - Digital signatures (EUF-CMA) -/
theorem cryptomania_from_lstar (n : Nat) (h_n : n ≥ 4) :
    (∃ E : PKEScheme, CPA_Secure E) ∧
    (∃ K : KEProtocol, KESecure K) ∧
    (∃ S : PKSigScheme, EUF_CMA_Secure S) :=
  ⟨lstarPKE_exists n h_n,
   lstarKeyExchange_exists n h_n,
   lstarPKSignature_exists n h_n⟩

/-! ## Complete Cryptographic Landscape -/

/-! ## NOTE: Theorem Commented Out (Depends on Deleted Trapdoor Module)

The `complete_crypto_from_lstar` theorem below was commented out because it depends on
`generateCNF` from the deleted `TrapdoorStructuralOWF` module (QP-profile specific).

This is an EXTENSION result showing that L* enables both Minicrypt and Cryptomania.
It is NOT required for the main P≠NP proof.

To restore: Reimplement trapdoor CNF generation for the exponential profile.
-/

/-
/-- **Complete Cryptographic Foundation**: Minicrypt + Cryptomania from L* OWF.

    The L* construction provides BOTH:

    **Minicrypt** (13 private-key primitives):
    PRG, PRF, PRP, Symmetric Encryption, UOWHF, Commitment,
    MAC, OTS, Many-time Signatures, ZK, Coin Flip, MPC, Authenticated Encryption

    **Cryptomania** (3 public-key primitives):
    PKE, Key Exchange, Public-Key Signatures

    This is the complete cryptographic landscape derivable from OWF. -/
theorem complete_crypto_from_lstar (n : Nat) (h_n : n ≥ 4) :
    (  -- Cryptomania primitives
      (∃ E : PKEScheme, CPA_Secure E) ∧
      (∃ K : KEProtocol, KESecure K) ∧
      (∃ S : PKSigScheme, EUF_CMA_Secure S)
    ) ∧
    (  -- Minicrypt primitives
      (∃ G : PRG, PRGSecure G) ∧
      (∃ F : PRF, IsPRFSecure F) ∧
      (∃ C : CommitmentScheme, CommitmentSecureFull C) ∧
      (∀ msgLen : Nat, ∃ M : MAC, IsMACSecure M) ∧
      (∀ msgBits : Nat, ∃ S_ots : SignatureScheme, IsOTSSecure S_ots) ∧
      (ZKSecure negl) ∧
      (∀ inputLen : Nat, ∃ P : PRP, IsPRPSecure P) ∧
      (∀ msgBits depth : Nat, ∃ M : ManyTimeSignature, IsManyTimeSigSecure M) ∧
      (∃ P : CoinFlipProtocol, CoinFlipSecure P) ∧
      (∀ F_mpc : TwoPartyFunction, ∃ P : MPCProtocol, MPCSecure F_mpc P) ∧
      (∀ msgLen : Nat, ∃ E_cpa : SymmetricEncryption, IsCPASecure E_cpa) ∧
      (∀ msgLen : Nat, ∃ AE : AuthenticatedEncryption, AESecure AE) ∧
      (∃ H : HashFamily, IsUOWHF H)
    ) := by
  -- Cryptomania part
  let cryptomania_res := cryptomania_from_lstar n h_n

  -- Minicrypt part
  let dummy_assignment : Assignment := fun _ => false
  let minicrypt_cnf := generateCNF n dummy_assignment h_n  -- BROKEN: generateCNF deleted
  let h_minicrypt_nvars_ge_4 : minicrypt_cnf.nvars ≥ 4 := generateCNF_nvars_ge_4 n dummy_assignment h_n

  let minicrypt_res := minicrypt_from_lstar minicrypt_cnf h_minicrypt_nvars_ge_4

  exact And.intro cryptomania_res minicrypt_res
-/

end LStar.Crypto.Cryptomania
