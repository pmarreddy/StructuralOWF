/-
Copyright (c) 2025 FormalOWF Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Butterfly Formalization Team
-/

import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer3_InformationBounds.ConstraintSystem.ConfigTypes
import Infrastructure.Witness.WitnessAlgorithm
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! ## CanonicalKeyednessBounds: Canonical Keyedness Encodings Bounded

**Theorem**: canonical_keyedness_bounded_all - canonical encoding < haltTime for all cuts/configs.

**Why extracted**: Breaks circular dependency (TMAxioms ← this ← TMAdapterProofs ← TMAxioms).

**Canonical encoding**: Uses Fintype.equivFin for {0,...,N-1} indexing where N = |ConfigSpace|.

**Main results** (§7, Appendix C):
- canonical_satisfies_keyedness_bound: FG singleton cuts
- canonical_satisfies_all_cuts_bound: Arbitrary multi-gate cuts
- canonical_keyedness_bounded_all: General bound with 0 sorries

**Trust boundary**: 3 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §Segment Reduction.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF Classical

/-! ## ConfigSpace Cardinality Lemmas -/

/-- Cardinality bound for ConfigSpace at a cut.

    **Content**: The number of configurations at cut C is exactly ∏_{v∈C} 2^(R_v).

    **Consequence**: For singleton FG cut {v}, this is exactly 2^λ. -/
lemma configSpace_card (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    Fintype.card (ConfigSpace L C) = Finset.prod C (fun v => 2^(L.R v)) := by
  classical
  simp only [ConfigSpace]

  -- Now work with the unfolded type directly
  trans (∏ v : InCut L C, Fintype.card (Fin (2^(L.R v.val))))
  · -- Use convert to handle instance mismatch between instFintype_ConfigSpace and Pi.instFintype
    convert Fintype.card_pi using 2
    infer_instance  -- DecidableEq (InCut L C)

  trans (∏ v : InCut L C, 2^(L.R v.val))
  · -- Simplify Fintype.card (Fin n) = n
    congr 1
    funext v
    rw [Fintype.card_fin]

  trans ((Finset.univ : Finset (InCut L C)).prod (fun v => 2^(L.R v.val)))
  · -- Fintype.prod = Finset.prod over univ (definitional)
    rfl

  -- Use Finset.prod_bij to convert product over subtype to product over C
  apply Finset.prod_bij (fun (a : InCut L C) (_ha : a ∈ Finset.univ) => a.val)
  · -- Show a.val ∈ C
    intro a ha
    exact a.property
  · -- Injectivity
    intro a₁ ha₁ a₂ ha₂ heq
    exact Subtype.ext heq
  · -- Surjectivity
    intro b hb
    use ⟨b, hb⟩
    use Finset.mem_univ _
  · -- Function values equal
    intro a ha
    rfl

/-- For singleton FG cut, config space has exactly 2^λ elements. -/
lemma configSpace_card_fg_singleton (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v}) :
    Fintype.card (ConfigSpace L {v.val}) = 2^(L.R v.val) := by
  rw [configSpace_card]
  simp [Finset.prod_singleton]

/-! ## Canonical Keyedness Definition -/

/-- Canonical keyedness encoding using Fintype.equivFin.

    **Design**: Maps configs to {0, 1, ..., N-1} where N = |ConfigSpace L C|.

    **Injectivity**: Follows from Fintype.equivFin injectivity.

    **Bound**: All values < Fintype.card (ConfigSpace L C) ≤ 2^λ (built into type via Fin).  -/
noncomputable def canonicalKeyedness (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    KeyednessProperty L C (Fintype.card (ConfigSpace L C)) := {
  configToState := fun cfg =>
    -- Use Fintype.equivFin to get canonical index in {0, ..., N-1}
    -- Returns Fin (Fintype.card (ConfigSpace L C)) directly
    Fintype.equivFin (ConfigSpace L C) cfg
  h_injective := by
    intro cfg1 cfg2 h_eq
    -- Fintype.equivFin is an equivalence, hence injective
    exact (Fintype.equivFin (ConfigSpace L C)).injective h_eq
}

/-! ## Boundedness Theorems -/

/-- Canonical encoding is bounded by config space cardinality.

    **Note**: This is now definitional - the bound is built into the type! -/
lemma canonical_keyedness_bounded_by_card (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (cfg : ConfigSpace L C) :
    ((canonicalKeyedness L C).configToState cfg).val < Fintype.card (ConfigSpace L C) := by
  exact ((canonicalKeyedness L C).configToState cfg).isLt

/-- For FG instance, canonical encoding at gate v is bounded by 2^λ. -/
lemma canonical_keyedness_bounded_by_fg (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (cfg : ConfigSpace L {v.val}) :
    ((canonicalKeyedness L {v.val}).configToState cfg).val < 2^(L.R v.val) := by
  calc ((canonicalKeyedness L {v.val}).configToState cfg).val
      < Fintype.card (ConfigSpace L {v.val}) := canonical_keyedness_bounded_by_card L {v.val} cfg
    _ = 2^(L.R v.val) := configSpace_card_fg_singleton L v

/-- Canonical encoding satisfies h_all_keyedness_bounded for singleton FG cuts.

    **Proof**: For FG instances with haltTime ≥ 2^λ, canonical encoding < haltTime. -/
theorem canonical_satisfies_keyedness_bound
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (haltTime : Nat)
    (h_time_sufficient : 2^(L.R v.val) ≤ haltTime) :
    ∀ (cfg : ConfigSpace L {v.val}),
      ((canonicalKeyedness L {v.val}).configToState cfg).val < haltTime := by
  intro cfg
  calc ((canonicalKeyedness L {v.val}).configToState cfg).val
      < 2^(L.R v.val) := canonical_keyedness_bounded_by_fg L v cfg
    _ ≤ haltTime := h_time_sufficient

/-- General bound for canonical encoding at arbitrary cut.

    **Extension to all cuts**: For any cut C, canonical encoding < ∏_{v∈C} 2^(R_v). -/
theorem canonical_satisfies_all_cuts_bound
    (L : LStarInstanceFG)
    (haltTime : Nat)
    (h_time_large : ∀ C : Finset (Fin L.dag.n),
                     Finset.prod C (fun v => 2^(L.R v)) ≤ haltTime) :
    ∀ (C : Finset (Fin L.dag.n))
      (cfg : ConfigSpace L C),
      ((canonicalKeyedness L C).configToState cfg).val < haltTime := by
  intro C cfg
  calc ((canonicalKeyedness L C).configToState cfg).val
      < Fintype.card (ConfigSpace L C) := canonical_keyedness_bounded_by_card L C cfg
    _ = Finset.prod C (fun v => 2^(L.R v)) := configSpace_card L C
    _ ≤ haltTime := h_time_large C

/-- **Complete PROOF**: For sufficiently large haltTime, canonical encoding
    satisfies h_all_keyedness_bounded for ALL cuts and ALL configs.

    **Bound required**: haltTime ≥ max over all cuts C of ∏_{v∈C} 2^(R_v).
    For FG instances with lambda_base, this max is 2^lambda_base at the FG cut.

    **Status**: ZERO sorries - complete proof -/
theorem canonical_keyedness_bounded_all
    (L : LStarInstanceFG)
    (lambda_base : Nat)
    (h_lambda_is_max : ∀ C : Finset (Fin L.dag.n),
                   Finset.prod C (fun v => 2^(L.R v)) ≤ 2^lambda_base)
    (haltTime : Nat)
    (h_time_sufficient : 2^lambda_base ≤ haltTime) :
    ∀ (C : Finset (Fin L.dag.n))
      (cfg : ConfigSpace L C),
      ((canonicalKeyedness L C).configToState cfg).val < haltTime := by
  intro C cfg
  apply canonical_satisfies_all_cuts_bound L haltTime ?_ C cfg
  intro C'
  calc Finset.prod C' (fun v => 2^(L.R v))
      ≤ 2^lambda_base := h_lambda_is_max C'
    _ ≤ haltTime := h_time_sufficient

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms canonical_satisfies_keyedness_bound
#print axioms canonical_satisfies_all_cuts_bound
#print axioms canonical_keyedness_bounded_all

end LStar.StructuralOWF.Foundations
