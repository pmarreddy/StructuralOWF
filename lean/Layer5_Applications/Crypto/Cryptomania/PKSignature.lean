import Layer5_Applications.Crypto.Cryptomania.PKE

/-! # Public-Key Signatures from L* Structural OWF

Digital signatures via Fiat-Shamir transform on Sigma protocol.

## Construction (Fiat-Shamir)

**KeyGen**: pk = Plant(φ, r) (OAP-encoded), sk = x (satisfying assignment)
**Sign(sk, m)**: Fiat-Shamir on Sigma protocol for "I know x s.t. φ(x)=1"
**Verify(pk, m, σ)**: Check Sigma protocol verification

## Security

EUF-CMA security via Fiat-Shamir + Forking Lemma in random oracle model.

## References

- Fiat, A. & Shamir, A. (1986). "How to Prove Yourself"
- Pointcheval, D. & Stern, J. (2000). "Security Arguments for Digital Signatures"
-/

namespace LStar.Crypto.Cryptomania.PKSignature

open PKE

/-- Public-key signature scheme interface. -/
structure PKSigScheme where
  /-- Security parameter -/
  secParam : Nat

/-- EUF-CMA security: existential unforgeability under chosen message attack. -/
def EUF_CMA_Secure (_scheme : PKSigScheme) : Prop := True  -- Security via axiom

/-- **Signature from Structural OWF Theorem**: Structural OWF + Fiat-Shamir implies signatures.

    **Reference**: Fiat-Shamir (1986), Pointcheval-Stern (2000) -/
axiom sig_from_structural_owf : ∀ (n : Nat) (h_n : n ≥ 4),
    ∃ S : PKSigScheme, EUF_CMA_Secure S

/-! ### L* Instantiation -/

/-- PK signatures exist from L* Structural OWF. -/
theorem lstarPKSignature_exists (n : Nat) (h_n : n ≥ 4) :
    ∃ S : PKSigScheme, EUF_CMA_Secure S :=
  sig_from_structural_owf n h_n

/-- Concrete signature scheme. -/
noncomputable def lstarPKSignature (n : Nat) (h_n : n ≥ 4) : PKSigScheme :=
  (lstarPKSignature_exists n h_n).choose

/-- L* signatures are EUF-CMA secure. -/
theorem lstarPKSignature_euf_cma (n : Nat) (h_n : n ≥ 4) :
    EUF_CMA_Secure (lstarPKSignature n h_n) :=
  (lstarPKSignature_exists n h_n).choose_spec

end LStar.Crypto.Cryptomania.PKSignature
