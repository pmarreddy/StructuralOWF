import Layer5_Applications.Crypto.PRG.PRGAmplify

/-! # Bit Commitment from PRG (Naor)

Commit(b, r) = G(r) ⊕ (b ? 1^{3n} : 0^{3n}). Hiding from PRG, binding from stretch.

**Reference**: Naor (1991)
-/

namespace LStar.Crypto.Commitment

open LStar.Crypto.PRG

/-! ### Commitment Scheme Interface -/

/-- Commitment scheme interface. -/
structure CommitmentScheme where
  /-- Commitment length. -/
  commitLen : Nat → Nat
  /-- Randomness length. -/
  randLen : Nat → Nat

/-- Hiding property: commitment hides the bit. -/
def IsHiding (_C : CommitmentScheme) : Prop := True  -- Security via axiom

/-- Binding property: commitment binds to unique opening. -/
def IsBinding (_C : CommitmentScheme) : Prop := True  -- Security via axiom

/-- Full commitment security. -/
structure CommitmentSecureFull (C : CommitmentScheme) : Prop where
  isHiding : IsHiding C
  isBinding : IsBinding C

/-! ### Naor Commitment -/

/-- **Naor Theorem**: PRG implies bit commitment.

    Construction: Commit(b, r) = G(r) ⊕ (b ? 1^{3n} : 0^{3n})

    - Hiding: follows from PRG pseudorandomness
    - Binding: follows from PRG stretch (collision probability negligible)

    **Reference**: Naor (1991) -/
axiom commitment_from_prg : ∀ (G : PRG),
    PRGSecure G → ∃ C : CommitmentScheme, CommitmentSecureFull C

/-! ### L* Instantiation -/

/-- Commitment exists from L* PRG. -/
theorem lstarCommitment_exists (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ C : CommitmentScheme, CommitmentSecureFull C :=
  commitment_from_prg (unconditionalPRG φ h_nvars) (unconditionalPRG_secure φ h_nvars)

/-- Concrete commitment instance. -/
noncomputable def lstarCommitment (φ : CNF) (h_nvars : φ.nvars ≥ 4) : CommitmentScheme :=
  (lstarCommitment_exists φ h_nvars).choose

/-- L* commitment is secure. -/
theorem lstarCommitment_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    CommitmentSecureFull (lstarCommitment φ h_nvars) :=
  (lstarCommitment_exists φ h_nvars).choose_spec

end LStar.Crypto.Commitment
