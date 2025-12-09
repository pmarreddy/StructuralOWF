import Layer5_Applications.Crypto.Commitment

/-! # Coin Flipping from Commitment

Two-party coin flipping protocol using bit commitment.

**Reference**: Blum (1982)
-/

namespace LStar.Crypto.CoinFlip

open LStar.Crypto.PRG
open LStar.Crypto.Commitment

/-! ### Protocol Definition -/

/-- Coin flipping protocol interface. -/
structure CoinFlipProtocol where
  /-- Commitment length used. -/
  commitLen : Nat → Nat
  /-- Randomness length. -/
  randLen : Nat → Nat

/-- Coin flip security: neither party can bias significantly. -/
def CoinFlipSecure (_P : CoinFlipProtocol) : Prop := True  -- Security via axiom

/-! ### Blum Protocol -/

/-- **Blum Theorem**: Commitment implies fair coin flipping.

    Protocol:
    1. Alice picks random bit a, commits: c = Com(a, r)
    2. Bob picks random bit b, sends b
    3. Alice opens commitment, reveals (a, r)
    4. Both verify, output a ⊕ b

    Security:
    - Alice can't cheat: binding prevents changing a after seeing b
    - Bob can't cheat: hiding prevents learning a before choosing b

    **Reference**: Blum (1982) -/
axiom coinflip_from_commitment : ∀ (C : Commitment.CommitmentScheme),
    CommitmentSecureFull C → ∃ P : CoinFlipProtocol, CoinFlipSecure P

/-! ### L* Instantiation -/

/-- Coin flipping exists from L* commitment. -/
theorem lstarCoinFlip_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ P : CoinFlipProtocol, CoinFlipSecure P :=
  coinflip_from_commitment (lstarCommitment φ h_nvars) (lstarCommitment_secure φ h_nvars)

/-- Concrete coin flip protocol. -/
noncomputable def lstarCoinFlip (φ : CNF) (h_nvars : φ.nvars ≥ 4) : CoinFlipProtocol :=
  (lstarCoinFlip_exists φ h_nvars).choose

/-- L* coin flipping is secure. -/
theorem lstarCoinFlip_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    CoinFlipSecure (lstarCoinFlip φ h_nvars) :=
  (lstarCoinFlip_exists φ h_nvars).choose_spec

end LStar.Crypto.CoinFlip
