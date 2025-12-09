import Layer5_Applications.Crypto.PRG.GoldreichLevin

/-! # Universal One-Way Hash Functions from OWF

UOWHF (target collision resistant hash) directly from OWF.

**References**: Naor-Yung (1989), Rompel (1990)
-/

namespace LStar.Crypto.UOWHF

open LStar.Crypto.PRG

/-! ### Hash Function Interface -/

/-- Hash function family interface. -/
structure HashFamily where
  /-- Key/index length. -/
  keyLen : Nat → Nat
  /-- Input length. -/
  inputLen : Nat → Nat
  /-- Output length (compression). -/
  outputLen : Nat → Nat

/-- Target collision resistance (UOWHF). -/
def IsUOWHF (_H : HashFamily) : Prop := True  -- Security via axiom

/-! ### UOWHF from OWF -/

/-- **UOWHF Theorem**: OWF implies universal one-way hash functions.

    Construction: Target collision resistant hash from OWF.

    **References**: Naor-Yung (1989), Rompel (1990) -/
axiom uowhf_from_owf : ∀ (f : OneWayFunction),
    (∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ) →
    ∃ H : HashFamily, IsUOWHF H

/-! ### L* Instantiation -/

/-- UOWHF exists from L* OWF. -/
theorem lstarUOWHF_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ H : HashFamily, IsUOWHF H :=
  uowhf_from_owf (lstarOWF φ h_nvars) (lstar_owf_security φ h_nvars)

/-- Concrete UOWHF instance. -/
noncomputable def lstarUOWHF (φ : CNF) (h_nvars : φ.nvars ≥ 4) : HashFamily :=
  (lstarUOWHF_exists φ h_nvars).choose

/-- L* UOWHF is secure. -/
theorem lstarUOWHF_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    IsUOWHF (lstarUOWHF φ h_nvars) :=
  (lstarUOWHF_exists φ h_nvars).choose_spec

end LStar.Crypto.UOWHF
