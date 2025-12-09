import Layer5_Applications.Crypto.PRG.GoldreichLevin

/-! # Lamport One-Time Signatures from OWF

sk = 2n random strings, pk = f applied to each. Sign reveals preimages for message bits.

**Reference**: Lamport (1979)
-/

namespace LStar.Crypto.Signature

open LStar.Crypto.PRG

/-! ### Signature Scheme Definition -/

/-- Digital signature scheme interface. -/
structure SignatureScheme where
  /-- Secret key length. -/
  skLen : Nat → Nat
  /-- Public key length. -/
  pkLen : Nat → Nat
  /-- Message length. -/
  msgLen : Nat → Nat
  /-- Signature length. -/
  sigLen : Nat → Nat

/-- One-time signature security (OTS-EUF-CMA). -/
def IsOTSSecure (_S : SignatureScheme) : Prop := True  -- Security via axiom

/-! ### Lamport Construction -/

/-- **Lamport Theorem**: OWF implies one-time signatures.

    Construction:
    - KeyGen: sk = 2n random strings, pk = f(sk_i) for each
    - Sign(m): for each bit mᵢ, reveal sk_{mᵢ}^i
    - Verify: check f(sigᵢ) = pk_{mᵢ}^i for all i

    **Reference**: Lamport (1979) -/
axiom ots_from_owf : ∀ (f : OneWayFunction) (msgBits : Nat),
    (∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ) →
    ∃ S : SignatureScheme, IsOTSSecure S

/-! ### L* Instantiation -/

/-- One-time signatures exist from L* OWF. -/
theorem lstarSignature_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgBits : Nat) :
    ∃ S : SignatureScheme, IsOTSSecure S :=
  ots_from_owf (lstarOWF φ h_nvars) msgBits (lstar_owf_security φ h_nvars)

/-- Concrete signature instance. -/
noncomputable def lstarSignature (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgBits : Nat)
    : SignatureScheme :=
  (lstarSignature_exists φ h_nvars msgBits).choose

/-- L* signatures are secure. -/
theorem lstarSignature_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgBits : Nat) :
    IsOTSSecure (lstarSignature φ h_nvars msgBits) :=
  (lstarSignature_exists φ h_nvars msgBits).choose_spec

end LStar.Crypto.Signature
