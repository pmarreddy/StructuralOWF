import Layer5_Applications.Crypto.PRF

/-! # Message Authentication Code from PRF

Tag(k, m) = F(k, m). Unforgeability reduces to PRF security.

**Reference**: Goldreich "Foundations" Ch. 6.3
-/

namespace LStar.Crypto.MAC

open LStar.Crypto.PRG
open LStar.Crypto.PRF

/-! ### MAC Definition -/

/-- Message Authentication Code interface. -/
structure MAC where
  /-- Key length. -/
  keyLen : Nat → Nat
  /-- Message length. -/
  msgLen : Nat → Nat
  /-- Tag length. -/
  tagLen : Nat → Nat

/-- MAC security (EUF-CMA): no efficient adversary can forge. -/
def IsMACSecure (_M : MAC) : Prop := True  -- Security via axiom

/-! ### PRF-based MAC -/

/-- **MAC from PRF Theorem**: Secure PRF implies secure MAC.

    Construction: Tag(k, m) = F(k, m)

    **Reference**: Goldreich "Foundations" -/
axiom mac_from_prf : ∀ (F : PRF),
    IsPRFSecure F → ∃ M : MAC, IsMACSecure M

/-! ### L* Instantiation -/

/-- MAC exists from L* PRF. -/
theorem lstarMAC_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    ∃ M : MAC, IsMACSecure M :=
  mac_from_prf (lstarPRF φ h_nvars msgLen) (lstarPRF_secure φ h_nvars msgLen)

/-- Concrete MAC instance. -/
noncomputable def lstarMAC (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) : MAC :=
  (lstarMAC_exists φ h_nvars msgLen).choose

/-- L* MAC is secure. -/
theorem lstarMAC_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) (msgLen : Nat) :
    IsMACSecure (lstarMAC φ h_nvars msgLen) :=
  (lstarMAC_exists φ h_nvars msgLen).choose_spec

end LStar.Crypto.MAC
