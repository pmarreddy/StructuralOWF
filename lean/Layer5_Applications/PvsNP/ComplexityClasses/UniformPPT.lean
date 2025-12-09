/-! ## UniformPPT: Uniform PPT Minimal Interface (0 axioms)

**Purpose**: Minimal interface for uniform PPT algorithms (avoids machine model commitment).

**Polynomial Bounds - Weak vs Strong**:
- This structure uses **WEAK (pointwise)** polynomial bounds: `∀ n, ∃ C k, time_bound n ≤ C * n^k`
- Contrast with **STRONG (uniform)** bounds in `RandAdv`: `∃ C k, ∀ n, time_bound n ≤ C * (n+1)^k`
- **Design Choice**: UniformPPT uses pointwise bounds (∀n∃C,k) and is intended for abstract
  specifications, not as the primary PPT notion (for which use PPTAdversary/RandAdv)
- **Main Proof Chain**: Uses `RandAdv` with strong uniform bounds (textbook-standard)
- **This Structure**: Deliberately weaker - suitable for contexts where specific constants C, k
  are not needed

**Fields**:
- `time_bound`: time as function of input size
- `poly`: pointwise polynomial domination (allows different C, k per n)
- `uniform`: marker that no non-uniform advice is used

**Note**: For complexity class definitions with uniform polynomial bounds (standard textbook
form), use `RandAdv` instead. UniformPPT is only for contexts where pointwise bounds suffice.

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

structure UniformPPT (α β : Type) where
  /-- Time bound as a function of input size. -/
  time_bound : Nat → Nat
  /-- Polynomial domination certificate (exists polynomial p). -/
  poly : ∀ n, ∃ C k, time_bound n ≤ C * n ^ k
  /-- Uniform (no non-uniform advice); marker only. -/
  uniform : True := by trivial

-- Axiom Audits: Trust Boundary Transparency
#print axioms UniformPPT

end LStar.Complexity

