/-! ## NPDefs: Minimal NP Framework (0 axioms)

**Purpose**: Definitional NP via verifiers + Karp reductions (lightweight, axioms-free).

**IMPORTANT - Logical NP vs Complexity-Theoretic NP**:
- This `InNP` is an **extensional/semantic NP** with no resource bounds
- `InNP L` means: ∃ verifier V such that `L x ↔ ∃ w, V x w` (pure logic, no time/size bounds)
- **Contrast**: Complexity-theoretic NP requires polynomial-time verification + poly-bounded witnesses
- **For complexity theory**: Use `InNP_Alg` (ComplexityClasses.lean) or `InNP_parametric` with
  explicit polynomial bounds
- **This Module**: Provides minimal logical framework for abstract reasoning about NP structure

**Definitions**:
- `Lang α`: Decision language over α
- `VerifierCert L`: Packaged verifier (witness type β + relation V)
- `InNP L`: Existence of verifier certificate (LOGICAL, not complexity-bounded)
- `Reduces A B`: Many-one (Karp) reduction (extensional, correctness only)

**Use Cases**:
- Abstract NP reasoning (e.g., p_subset_np theorem structure)
- Reduction correctness (separate from complexity bounds)
- Logical foundations for complexity classes

**For Complexity Theory**: Use `InNP_Alg` or `InNP_parametric` with explicit polynomial bounds.

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

universe u

/-- A decision language over `α`. -/
abbrev Lang (α : Type u) := α → Prop

/-- A packaged verifier certificate for NP‑membership. -/
structure VerifierCert {α : Type u} (L : Lang α) where
  β : Type
  V : α → β → Prop
  spec : ∀ x, L x ↔ ∃ w : β, V x w

/-- Verifier‑based NP (existence of a verifier certificate). -/
def InNP {α : Type u} (L : Lang α) : Prop := Nonempty (VerifierCert L)

/-- Many-one (Karp) reduction (extensional, total).

`Reduces A B` if there exists a function `f` such that `x ∈ A → f x ∈ B`.
This is the core correctness part; size/time bounds can be documented beside
concrete reductions when needed. -/
def Reduces {α : Type u} {γ : Type u}
  (A : Lang α) (B : Lang γ) : Prop :=
  ∃ f : α → γ, ∀ x, A x → B (f x)

-- Axiom Audits: Trust Boundary Transparency
#print axioms VerifierCert
#print axioms InNP
#print axioms Reduces

end LStar.Complexity
