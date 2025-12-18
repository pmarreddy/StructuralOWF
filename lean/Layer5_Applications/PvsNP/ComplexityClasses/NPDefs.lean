/-! ## NPDefs: Helper Definitions (0 axioms)

**Purpose**: Lightweight helper definitions for witness structure.

**Definitions**:
- `Lang α`: Decision language over α (standard: `α → Prop`)
- `VerifierCert L`: Packaged verifier (witness type β + relation V)
- `HasWitnessStructure L`: Language has a witness/verifier structure (no resource bounds)

**Note**: For complexity-theoretic definitions with polynomial bounds, use ComplexityClasses.lean:
- `InNP` — NP with polynomial witness size and verification time bounds
- `InP`, `InFP`, `InFNP` — standard complexity classes with poly bounds

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

universe u

/-- A decision language over `α`. -/
abbrev Lang (α : Type u) := α → Prop

/-- A packaged verifier certificate: witness type β + verifier relation V. -/
structure VerifierCert {α : Type u} (L : Lang α) where
  β : Type
  V : α → β → Prop
  spec : ∀ x, L x ↔ ∃ w : β, V x w

/-- Language has witness/verifier structure (no resource bounds).

This asserts existence of a witness type and verifier relation, but imposes
no computational constraints. For complexity-theoretic NP (with polynomial
time and witness size bounds), use `InNP` from ComplexityClasses.lean. -/
def HasWitnessStructure {α : Type u} (L : Lang α) : Prop := Nonempty (VerifierCert L)

-- Axiom Audits: Trust Boundary Transparency
#print axioms VerifierCert
#print axioms HasWitnessStructure

end LStar.Complexity
