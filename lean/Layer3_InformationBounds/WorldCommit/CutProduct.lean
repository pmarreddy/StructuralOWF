import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Defs

/-! ## CutProduct: Cartesian Product Factoring for Cut-World Cardinality

**Purpose**: Abstract tools for decomposing constrained product types via predicate factoring.

**Key pattern**: When global predicate P factors pointwise (P f ↔ ∀ i, P_i (f i)), then:
```
{f : ∀ i, α i // P f} ≃ (∀ i, {x : α i // P_i x})
```

**Cardinality consequences**:
- #{global satisfying} = ∏ #{local satisfying}
- When each #{local} = 2^k_i → #{global} = 2^(∑ k_i)

**Application**: Cut-world cardinality proofs—global feasibility factors into per-node local feasibility.

## Paper vs Lean Proof Paths

**Paper path** (Appendix J, Lemma J.1-Cart):
  A1-A5 → H1-H5 → Lemma J.1-Cart → Cartesian factoring → |Worlds| = 2^ρ

  The paper requires H1-H5 hypotheses to justify that feasible worlds factor as
  Cartesian product WITHOUT probabilistic independence.

**Lean path** (actually used):
  CutWorld := Pi type (definitional) → |Pi| = ∏|components| (Mathlib) → |Worlds| = 2^ρ

  In Lean, CutWorld is DEFINED as a dependent product type. Cartesian structure is
  definitional, so no H-hypotheses are needed. Cardinality follows directly from
  Mathlib's `Fintype.card_pi`.

**A→H Bridge Theorems** (for paper correspondence, NOT used in main proof):
  See `AppendixJBridge.lean` for proven bridges:
  - `a1_implies_h1`: A1 → H1 (definitionally equal)
  - `a2_implies_h3`: A2 → H3 (contrapositive)
  - `a3_implies_h4`: A3 → H4 (definitionally equal)

  H2 and H5 are NOT formalized because the Lean proof doesn't need them.

**Main results**: piSubtypeEquiv (global-to-local factoring), prod_two_pow_eq_two_pow_sum, card_pi_eq_pow_sum

**Trust boundary**: Pure type theory + Mathlib - no custom axioms

See Layer3_InformationBounds/Layer3_README.md §World Commitment.
-/

namespace LStar.StructuralOWF.Foundations.CutProduct

open scoped BigOperators

universe u v

/-! ## Pi-Subtype Equivalence (Core Factoring)

The fundamental equivalence showing that constrained dependent products factor.
-/

/-- **Global-to-local factoring** for dependent products with predicates.

**Theorem**: When predicate P factors pointwise, global constraints decompose:

    {f : ∀ i, α i // ∀ i, P i (f i)} ≃ (∀ i, {x : α i // P i x})

**Proof idea**:
- Forward: Extract each component with its proof
- Backward: Combine components (proofs already packaged)
- Inverses: Definitional equality + subtype eta

**Why this works for L* cut-worlds** (Paper Appendix J, Lemma J.1-Cart):

Under L* instance properties A1-A5 → H1-H5:
- H1 (Disjoint pools from A1): Different nodes use disjoint memory → no shared constraints
- H5 (No coupling from A5+FG): Choices at v₁ don't constrain choices at v₂ (structural independence)
- H3 (Injectivity from A2): Seeds encode parent data uniquely → no hidden correlations
- H4 (Realizability from A3): Full-rank emergence → all local configs achievable
- Therefore: Global satisfaction = conjunction of local satisfaction (Cartesian factoring)

**This is NOT probabilistic independence** — it's structural/information-theoretic independence
from disjoint memory + algebraic independence (full rank). Much stronger than statistical independence!

**Paper**: Appendix J (bijection construction), Lemma J.1-Cart (factoring proof) -/
def piSubtypeEquiv {ι : Type u} (α : ι → Type v) (P : ∀ i, α i → Prop) :
  {f : ∀ i, α i // ∀ i, P i (f i)} ≃ (∀ i, {x : α i // P i x}) :=
{ toFun    := fun f i => ⟨f.1 i, f.2 i⟩,
  invFun   := fun g   => ⟨(fun i => (g i).1), (fun i => (g i).2)⟩,
  left_inv := by intro f; rcases f with ⟨val, prop⟩; rfl,
  right_inv := by intro g; ext i; simp }

section fintype

variable {ι : Type u} [Fintype ι]
variable {α : ι → Type v} [∀ i, Fintype (α i)]
variable {P : ∀ i, α i → Prop} [∀ i, DecidablePred (P i)]

-- Lean 4 synthesizes Fintype (∀ i, {x : α i // P i x}) automatically via Pi instance
noncomputable instance globalSubtypeFintype : Fintype {f : ∀ i, α i // ∀ i, P i (f i)} := by
  classical
  exact Fintype.ofEquiv (∀ i, {x : α i // P i x}) (piSubtypeEquiv α P).symm

/-- **Cardinality multiplies across cut**: `#{global} = ∏ #{local}`

**Paper reference**: |Π_C(π)| = ∏_{v∈C} |S_v| (Appendix J)

**Proof**: Via piSubtypeEquiv + standard Fintype.card_pi -/
theorem card_piSubtype :
  Fintype.card {f : ∀ i, α i // ∀ i, P i (f i)} =
    ∏ i, Fintype.card {x : α i // P i x} := by
  classical
  rw [Fintype.card_congr (piSubtypeEquiv α P)]
  exact Fintype.card_pi

end fintype

/-! ## Power Algebra

Convert between product and sum forms for exponentials.
-/

/-- **Product of powers = power of sum**: `∏ 2^(k i) = 2^(∑ k i)` -/
lemma prod_two_pow_eq_two_pow_sum (ι : Type u) [Fintype ι] (k : ι → ℕ) :
  ∏ i : ι, (2 : ℕ) ^ k i = 2 ^ (∑ i : ι, k i) := by
  rw [Finset.prod_pow_eq_pow_sum]

/-- **Each type has size 2^r → product has size 2^(∑ r)**

**Application**: In cut-world proofs, each node contributes 2^(R_v - q_v) states.

**Proof**: Fintype.card_pi + power algebra -/
theorem card_pi_eq_pow_sum
  {ι : Type u} [Fintype ι]
  (α : ι → Type v) [∀ i, Fintype (α i)] [Fintype (∀ i, α i)]
  (r : ι → ℕ)
  (h : ∀ i, Fintype.card (α i) = 2 ^ r i) :
  Fintype.card (∀ i, α i) = 2 ^ (∑ i, r i) := by
  classical
  trans (∏ i, Fintype.card (α i))
  · convert Fintype.card_pi; infer_instance
  · simp only [h]
    exact prod_two_pow_eq_two_pow_sum _ r

/-! ## Axiom Verification

These lemmas use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms LStar.StructuralOWF.Foundations.CutProduct.prod_two_pow_eq_two_pow_sum
#print axioms LStar.StructuralOWF.Foundations.CutProduct.card_pi_eq_pow_sum

end LStar.StructuralOWF.Foundations.CutProduct
