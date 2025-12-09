import Layer5_Applications.PvsNP.ComplexityClasses.Sized

/-! ## AlgSpec: Pure Algorithmic Specification (0 axioms)

**Purpose**: Algorithmic specification WITHOUT TM implementation proof.

**Motivation**: The P≠NP proof only uses algorithmic properties (`run`, polynomial bounds),
not TM execution proofs (`run_correct`, `halts`). Separating these concerns:
1. Makes composition natural (compose algorithms, not TMs)
2. TM proofs only needed where TM execution is actually invoked

**Design**:
- `AlgSpec`: Pure algorithmic specification (run + polynomial bounds)
- `RandAdv`: Full structure with TM implementation proof (for backward compatibility)

**Key Insight**: When we compose algorithms (prefix check + verify, loop, dispatch),
we modify `run` but the underlying TM doesn't change. With this design:
- Compositions work at `AlgSpec` level (natural)
- TM proofs only needed at leaves (where real TMs exist)
-/

namespace LStar.Complexity

open Sized

/-- Pure algorithmic specification with polynomial time bound.

**Purpose**: Captures the algorithmic properties used by complexity proofs,
WITHOUT requiring TM implementation proof.

**Fields**:
- `run`: Algorithm specification (coins → input → output)
- `time_bound`: Size-indexed time bound
- `C`, `k`: Uniform polynomial constants
- `poly_explicit`: Polynomial bound using actual input sizes
- `output_bounded`: Output size bounded by computation time
- `coins_pos`: Positive coins (enables averaging)

**Trust Boundary**: 0 axioms (pure specification)
-/
structure AlgSpec (α β : Type) [Sized α] [Sized β] (T : Nat) where
  /-- Algorithm specification: given coins and input, produce output. -/
  run : Fin T → α → β

  /-- Time bound as function of input size. -/
  time_bound : Nat → Nat

  /-- Uniform polynomial constant (works for ALL input sizes). -/
  C : Nat

  /-- Uniform polynomial exponent (works for ALL input sizes). -/
  k : Nat

  /-- Positivity of uniform constant C (non-degenerate polynomial). -/
  h_C_pos : C > 0

  /-- Positivity of uniform exponent k (non-degenerate polynomial). -/
  h_k_pos : k > 0

  /-- Polynomial domination certificate using EXPLICIT input sizes.

      **Rigorous formulation**: For ALL inputs x, runtime ≤ C · (|x| + 1)^k
      where |x| = size x is explicitly defined via Sized typeclass. -/
  poly_explicit : ∀ x : α, time_bound (size x) ≤ C * (size x + 1) ^ k

  /-- Uniform polynomial bound on time_bound as a FUNCTION.

      **Purpose**: Ensures time_bound : Nat → Nat is polynomially bounded everywhere,
      not just at sizes realizable by type α values. -/
  time_bound_uniform : ∀ n, time_bound n ≤ C * (n + 1) ^ k

  /-- Output size bounded by computation time.

      **Fundamental principle**: An algorithm running for T steps can write at most T bits. -/
  output_bounded : ∀ c x, size (run c x) ≤ time_bound (size x)

  /-- Coins are finite and positive (enables averaging). -/
  coins_pos : 0 < T

-- Axiom Audit
#print axioms AlgSpec

/-- Deterministic AlgSpec: all coin choices produce same output. -/
def AlgSpec.isDeterministic {α β : Type} [Sized α] [Sized β] {T : Nat}
    (A : AlgSpec α β T) : Prop :=
  ∀ c₁ c₂ x, A.run c₁ x = A.run c₂ x

/-- Run with default coin (coin 0). -/
def AlgSpec.runDefault {α β : Type} [Sized α] [Sized β] {T : Nat}
    (A : AlgSpec α β T) (x : α) : β :=
  A.run ⟨0, A.coins_pos⟩ x

#print axioms AlgSpec.isDeterministic
#print axioms AlgSpec.runDefault

end LStar.Complexity
