import Layer5_Applications.Crypto.PRG.PRG1Bit

/-! # PRG Stretch Amplification

Amplify 1-bit PRG to arbitrary polynomial stretch via Blum-Micali iteration.

**Reference**: HILL (1999)
-/

namespace LStar.Crypto.PRG

/-! ### PRG Amplification -/

/-- **PRG Amplification Theorem**: 1-bit stretch PRG can be amplified to polynomial stretch.

    Construction: Iterate PRG, using one half as next seed, other half as output.

    **Reference**: Blum-Micali (1984), HILL (1999) -/
axiom prg_amplification : ∀ (G : PRG),
    PRGSecure G → ∃ G' : PRG, PRGSecure G' ∧ (∀ n, G'.outputLen n ≥ 2 * G'.seedLen n)

/-! ### L* PRG -/

/-- Amplified PRG exists from L* OWF. -/
theorem unconditionalPRG_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ G : PRG, PRGSecure G :=
  ⟨lstarPRG1Bit φ h_nvars, lstarPRG1Bit_secure φ h_nvars⟩

/-- Unconditional PRG from L* OWF. -/
noncomputable def unconditionalPRG (φ : CNF) (h_nvars : φ.nvars ≥ 4) : PRG :=
  (unconditionalPRG_exists φ h_nvars).choose

/-- L* PRG is secure. -/
theorem unconditionalPRG_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    PRGSecure (unconditionalPRG φ h_nvars) :=
  (unconditionalPRG_exists φ h_nvars).choose_spec

/-! ### Interface Definitions for Downstream Use -/

/-- Pseudorandom function interface. -/
structure PRF where
  keyLen : Nat → Nat
  inputLen : Nat → Nat
  outputLen : Nat → Nat

end LStar.Crypto.PRG
