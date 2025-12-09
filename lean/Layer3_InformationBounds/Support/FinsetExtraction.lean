import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## FinsetExtraction: Witness Extraction Helpers

**Purpose**: Utilities to avoid elaboration depth issues when extracting properties from filtered finsets.

**Key lemmas**:
- extract_from_double_filter: Extract witness satisfying both predicates + membership
- extract_predicates_from_double_filter: Simplified version (just predicates)

**Usage pattern**: Package "nonempty → extract witness → unpack properties" to avoid deep elaboration with complex predicates.

**Trust boundary**: 2 axiom audits - all proven (standard Lean foundations only)

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

/-- Extract a witness satisfying both a filter predicate and membership.

    This helper packages the standard "nonempty → extract witness → unpack properties"
    pattern in a way that avoids deep elaboration when the predicates are complex. -/
theorem extract_from_double_filter {α : Type*} [DecidableEq α]
    (outer_pred inner_pred : α → Prop) [DecidablePred outer_pred] [DecidablePred inner_pred]
    (base : Finset α)
    (h_ne : (base.filter outer_pred).filter inner_pred |>.Nonempty) :
    ∃ a : α, outer_pred a ∧ inner_pred a ∧ a ∈ base.filter outer_pred ∧
             a ∈ (base.filter outer_pred).filter inner_pred := by
  obtain ⟨a, ha⟩ := h_ne
  refine ⟨a, ?_, ?_, ?_, ha⟩
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
  · exact (Finset.mem_filter.mp ha).2
  · exact (Finset.mem_filter.mp ha).1

/-- Simplified version: extract just the predicates without membership. -/
theorem extract_predicates_from_double_filter {α : Type*} [DecidableEq α]
    (outer_pred inner_pred : α → Prop) [DecidablePred outer_pred] [DecidablePred inner_pred]
    (base : Finset α)
    (h_ne : (base.filter outer_pred).filter inner_pred |>.Nonempty) :
    ∃ a : α, outer_pred a ∧ inner_pred a := by
  obtain ⟨a, h_outer, h_inner, _, _⟩ := extract_from_double_filter outer_pred inner_pred base h_ne
  exact ⟨a, h_outer, h_inner⟩

/-! ## Axiom Verification

These helper lemmas use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms extract_from_double_filter
#print axioms extract_predicates_from_double_filter

end LStar.StructuralOWF.Foundations
