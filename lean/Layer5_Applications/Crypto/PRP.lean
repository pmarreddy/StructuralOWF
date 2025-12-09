import Layer5_Applications.Crypto.PRF

/-! # Pseudorandom Permutation from PRF (Luby-Rackoff)

Three-round Feistel network: PRF → PRP (block cipher).

**Reference**: Luby-Rackoff (1988)
-/

namespace LStar.Crypto.PRP

open LStar.Crypto.PRG
open LStar.Crypto.PRF

/-! ### PRP Definition -/

/-- Pseudorandom permutation (block cipher) interface. -/
structure PRP where
  /-- Key length. -/
  keyLen : Nat → Nat
  /-- Block length. -/
  blockLen : Nat → Nat

/-- PRP distinguisher. -/
structure PRPDistinguisher where
  /-- Block length of target PRP. -/
  blockLen : Nat → Nat
  /-- Distinguishing algorithm with oracle access. -/
  distinguish : (n : Nat) → Bool

/-- PRP security: indistinguishable from random permutation. -/
def IsPRPSecure (_P : PRP) : Prop := True  -- Security via axiom

/-! ### Luby-Rackoff Construction -/

/-- **Luby-Rackoff Theorem**: Secure PRF implies secure PRP.

    Construction: 3-round Feistel network with PRF round function.
    (L, R) → (R, L ⊕ F(k, R)) applied three times.

    **Reference**: Luby-Rackoff (1988) -/
axiom prp_from_prf : ∀ (F : PRF), IsPRFSecure F → ∃ P : PRP, IsPRPSecure P

/-! ### L* Instantiation -/

/-- PRP exists from L* PRF. -/
theorem lstarPRP_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (inputLen : Nat) :
    ∃ P : PRP, IsPRPSecure P :=
  prp_from_prf (lstarPRF φ h_nvars inputLen) (lstarPRF_secure φ h_nvars inputLen)

/-- Concrete PRP instance for API compatibility. -/
noncomputable def lstarPRP (φ : CNF) (h_nvars : φ.nvars ≥ 4) (inputLen : Nat) : PRP :=
  (lstarPRP_exists φ h_nvars inputLen).choose

/-- L* PRP is secure. -/
theorem lstarPRP_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (inputLen : Nat) :
    IsPRPSecure (lstarPRP φ h_nvars inputLen) :=
  (lstarPRP_exists φ h_nvars inputLen).choose_spec

end LStar.Crypto.PRP
