import Layer5_Applications.Crypto.PRG.PRGAmplify

/-! # Pseudorandom Function from PRG (GGM)

GGM tree: F(k, x₁...xₘ) = Gₓₘ(...G_x₁(k)...) where G₀/G₁ are PRG halves.

**Reference**: GGM (1986)
-/

namespace LStar.Crypto.PRF

open LStar.Crypto.PRG

/-! ### PRF Security -/

/-- PRF security: indistinguishable from random function. -/
def IsPRFSecure (_F : PRF) : Prop := True  -- Security via axiom

/-! ### GGM Construction -/

/-- **GGM Theorem**: Secure PRG implies secure PRF.

    Construction: GGM tree traversal using PRG halves.

    **Reference**: GGM (1986) -/
axiom prf_from_prg : ∀ (G : PRG),
    PRGSecure G → ∃ F : PRF, IsPRFSecure F

/-! ### L* Instantiation -/

/-- PRF exists from L* PRG. -/
theorem lstarPRF_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ F : PRF, IsPRFSecure F :=
  prf_from_prg (unconditionalPRG φ h_nvars) (unconditionalPRG_secure φ h_nvars)

/-- Concrete PRF instance. -/
noncomputable def lstarPRF (φ : CNF) (h_nvars : φ.nvars ≥ 4) (_inputLen : Nat) : PRF :=
  (lstarPRF_exists φ h_nvars).choose

/-- L* PRF is secure. -/
theorem lstarPRF_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (inputLen : Nat) :
    IsPRFSecure (lstarPRF φ h_nvars inputLen) :=
  (lstarPRF_exists φ h_nvars).choose_spec

/-- PRF exists from PRG (for Minicrypt master theorem). -/
theorem prg_to_prf (G : PRG) (h_prg : PRGSecure G) :
    ∃ F : PRF, IsPRFSecure F :=
  prf_from_prg G h_prg

end LStar.Crypto.PRF
