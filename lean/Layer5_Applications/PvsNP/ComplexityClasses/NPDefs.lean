/-! ## NPDefs: Minimal NP Framework (0 axioms)

**Purpose**: Definitional foundations for NP + Karp reductions (lightweight, axiom-free).

**Definitions**:
- `Lang α`: Decision language over α
- `VerifierCert L`: Packaged verifier (witness type β + relation V)
- `InNP_Logical L`: Logical NP (∃ verifier, no resource bounds) - for abstract reasoning
- `Reduces A B`: Many-one (Karp) reduction (extensional, correctness only)

**Note**: The canonical complexity-theoretic `InNP` (with poly bounds) is in ComplexityClasses.lean.
`InNP_Logical` here is for abstract proofs that don't need resource bounds.

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

universe u

/-- A decision language over `α`. -/
abbrev Lang (α : Type u) := α → Prop

/-- A packaged verifier certificate for NP‑membership (logical, no resource bounds). -/
structure VerifierCert {α : Type u} (L : Lang α) where
  β : Type
  V : α → β → Prop
  spec : ∀ x, L x ↔ ∃ w : β, V x w

/-- Logical NP: existence of a verifier certificate (NO resource bounds).

**Note**: This is for abstract reasoning only. For complexity theory,
use `InNP` from ComplexityClasses.lean which includes poly time/size bounds. -/
def InNP_Logical {α : Type u} (L : Lang α) : Prop := Nonempty (VerifierCert L)

/-- Many-one (Karp) reduction (extensional, total).

`Reduces A B` if there exists a function `f` such that `x ∈ A → f x ∈ B`.
This is the core correctness part; size/time bounds can be documented beside
concrete reductions when needed. -/
def Reduces {α : Type u} {γ : Type u}
  (A : Lang α) (B : Lang γ) : Prop :=
  ∃ f : α → γ, ∀ x, A x → B (f x)

-- Axiom Audits: Trust Boundary Transparency
#print axioms VerifierCert
#print axioms InNP_Logical
#print axioms Reduces

end LStar.Complexity
