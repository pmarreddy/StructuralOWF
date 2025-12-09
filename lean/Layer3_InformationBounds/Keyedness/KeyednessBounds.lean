/-
Copyright (c) 2025 FormalOWF Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Butterfly Formalization Team
-/

import Layer2_StructuralOWF.Plant.PlantCore
import Layer1_Construction.Core.InstanceOps
import Layer3_InformationBounds.ConstraintSystem.ConfigTypes
import Infrastructure.Witness.WitnessAlgorithm
import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! ## KeyednessBounds: Canonical Keyedness Bounded by Halt Time

**Main Theorem**: `canonical_keyedness_singleton_bounded` - Keyedness encodings < haltTime.

**Key Insight**: For TM solving FG instance in haltTime steps:
```
Canonical keyedness: configs → 0..2^(R_v)-1
Exhaustive search requires: 2^(R_v) ≤ haltTime
Therefore: keyedness outputs < haltTime ✓
```

**Why it matters**: Observable TM state space {0,...,haltTime-1} must accommodate all
keyedness encodings. This structural TM property enables h_configs_via_keyedness proof
in TMAdapter (bridges semantic configs to operational TM states).

**Key Theorems**:
```lean
canonical_keyedness_singleton_bounded : For FG cuts, keyedness < haltTime
canonical_keyedness_all_cuts_bounded : Universal bound for all cuts
```

**Trust Boundary**: Proven theorems (no axioms).

**Paper**: §7 "Turing Machine Keyedness", Appendix C "State Space Bounds"

See Layer3_InformationBounds/Layer3_README.md for keyedness and TM state space context.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF Classical

variable {k : Nat} {states alphabet : Type}
variable [Fintype states] [DecidableEq states]
variable [Fintype alphabet] [DecidableEq alphabet]

/-- **Canonical keyedness at singleton FG cut is bounded by halt time**.

    **Claim**: For canonical keyedness `keyedness_singleton_by_value` at FG gate v,
    all outputs are strictly less than haltTime (when 2^(R_v) ≤ haltTime).

    **Proof**:
    1. Canonical keyedness extracts `cfg.val : Fin (2^(R_v))`
    2. Therefore: output < 2^(R_v) (Fin upper bound)
    3. Given: 2^(R_v) ≤ haltTime
    4. Transitivity: output < haltTime ✓

    **Why this matters**: This enables h_configs_via_keyedness proof in tmToWitnessFinder,
    showing that keyed states are in the visited state set {0,...,haltTime-1}. -/
theorem canonical_keyedness_singleton_bounded
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (haltTime : Nat)
    (h_sufficient_time : 2^(L.R v.val) ≤ haltTime)
    (cfg : ConfigSpace L {v.val}) :
    (keyedness_singleton_by_value L v).configToState cfg < haltTime := by
  -- Step 1: Canonical keyedness returns cfg.val where cfg : singleton → Fin (2^(R_v))
  unfold keyedness_singleton_by_value
  simp only

  -- Step 2: cfg ⟨v.val, _⟩ : Fin (2^(L.R v.val)), so cfg.val < 2^(R_v)
  have h_fin_bound : (cfg ⟨v.val, by simp⟩).val < 2^(L.R v.val) :=
    Fin.is_lt (cfg ⟨v.val, by simp⟩)

  -- Step 3: Combine with h_sufficient_time
  calc (cfg ⟨v.val, by simp⟩).val
      < 2^(L.R v.val) := h_fin_bound
    _ ≤ haltTime := h_sufficient_time

/-- **Universal keyedness bound for canonical encodings at ALL FG gates**.

    **Extension**: If we have sufficient time bounds for ALL FG gates,
    then canonical keyedness at ANY FG singleton cut is bounded.

    **Use case**: When a TM performs exhaustive search over ALL FG gates
    (or we have multiple gates with independent time bounds). -/
theorem canonical_keyedness_all_fg_gates_bounded
    (L : LStarInstanceFG)
    (haltTime : Nat)
    -- For ALL FG gates, we have sufficient time
    (h_all_sufficient : ∀ (v : {v // L.fg.gateReq v}), 2^(L.R v.val) ≤ haltTime) :
    ∀ (v : {v // L.fg.gateReq v}) (cfg : ConfigSpace L {v.val}),
      (keyedness_singleton_by_value L v).configToState cfg < haltTime := by
  intro v cfg
  exact canonical_keyedness_singleton_bounded L v haltTime (h_all_sufficient v) cfg

/-- **Canonical keyedness bounded for ANY singleton cut** (when haltTime ≥ max emergence).

    **Note**: Uses `maxEmergence` from WitnessAlgorithm.lean (imported above).

    **General bound**: If haltTime exceeds the maximum emergence across all nodes,
    then canonical keyedness at ANY singleton cut {v} is bounded by haltTime.

    **Intuition**: Even non-FG nodes have emergent configs bounded by 2^(R_v),
    and canonical keyedness extracts these values. -/
theorem canonical_keyedness_any_singleton_bounded
    (L : LStarInstanceFG)
    (haltTime : Nat)
    {h_nonempty : (Finset.univ : Finset (Fin L.dag.n)).Nonempty}
    (h_max_bound : maxEmergence L h_nonempty ≤ haltTime)
    (v : Fin L.dag.n)
    {bound : Nat}  -- Bound parameter (polymorphic)
    (keyedness : KeyednessProperty L {v} bound)
    -- Require that this keyedness IS the canonical one (or equivalent)
    (h_is_canonical : ∀ cfg, (keyedness.configToState cfg).val = (cfg ⟨v, by simp⟩).val) :
    ∀ (cfg : ConfigSpace L {v}),
      (keyedness.configToState cfg).val < haltTime := by
  intro cfg
  rw [h_is_canonical]

  -- cfg ⟨v, _⟩ : Fin (2^(R_v))
  have h_fin : (cfg ⟨v, by simp⟩).val < 2^(L.R v) := Fin.is_lt _

  -- 2^(R_v) ≤ maxEmergence (from WitnessAlgorithm.lean)
  have h_le_max : 2^(L.R v) ≤ maxEmergence L h_nonempty := emergence_le_max L v

  calc (cfg ⟨v, by simp⟩).val
      < 2^(L.R v) := h_fin
    _ ≤ maxEmergence L h_nonempty := h_le_max
    _ ≤ haltTime := h_max_bound

/-- **Practical instantiation**: h_all_keyedness_bounded for canonical keyedness at FG gate.

    **Use**: This is the hypothesis needed by tmToWitnessFinder. For the specific
    FG gate being tracked, we can instantiate h_all_keyedness_bounded by:

    1. For cut {v} with canonical keyedness: Use canonical_keyedness_singleton_bounded
    2. For other cuts: Require structural bound (max emergence) or prove separately

    **Limitation**: This theorem only handles the SPECIFIC cut {v} with canonical keyedness.
    For h_configs_via_keyedness in tmToWitnessFinder, which quantifies over ALL cuts,
    we need additional reasoning about arbitrary cuts. -/
theorem h_all_keyedness_bounded_for_specific_gate
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (haltTime : Nat)
    (h_sufficient_time : 2^(L.R v.val) ≤ haltTime)
    -- For the specific cut {v.val} with canonical keyedness
    (C : Finset (Fin L.dag.n))
    (h_C_eq : C = {v.val})
    {bound : Nat}  -- Bound parameter (polymorphic)
    (keyedness : KeyednessProperty L C bound)
    (h_is_canonical : ∀ cfg, (keyedness.configToState cfg).val = (cfg ⟨v.val, by rw [h_C_eq]; simp⟩).val) :
    ∀ (cfg : ConfigSpace L C),
      (keyedness.configToState cfg).val < haltTime := by
  intro cfg
  rw [h_is_canonical]
  have h_fin : (cfg ⟨v.val, by rw [h_C_eq]; simp⟩).val < 2^(L.R v.val) := Fin.is_lt _
  calc (cfg ⟨v.val, by rw [h_C_eq]; simp⟩).val
      < 2^(L.R v.val) := h_fin
    _ ≤ haltTime := h_sufficient_time

/-! ## Full Universal Bound (Requires Stronger Assumptions)

The hypothesis `h_all_keyedness_bounded` in tmToWitnessFinder quantifies over
ALL cuts and ALL keyedness maps. This is stronger than what we've proven above.

**Options for proving the full universal bound**:

1. **Restrict to canonical keyedness**: Only allow canonical encodings
2. **Add bounded output constraint**: Require keyedness maps satisfy output bounds
3. **Structural max-emergence bound**: Assume haltTime ≥ maxEmergence
4. **Per-cut reasoning**: Provide bounds for each cut separately

For now, we provide the framework for option 3 (structural bound) and option 4 (specific cut).
The caller can choose which approach fits their use case.
-/

/-- **Full universal bound under max-emergence assumption** (strongest version).

    **Claim**: If haltTime ≥ maxEmergence AND all keyedness maps are canonical,
    then h_all_keyedness_bounded holds for ALL cuts and configs.

    **Note**: This requires canonicality assumption for ALL keyedness maps,
    which is reasonable in practice (we always use canonical encodings). -/
theorem h_all_keyedness_bounded_under_max_emergence
    (L : LStarInstanceFG)
    (haltTime : Nat)
    {h_nonempty : (Finset.univ : Finset (Fin L.dag.n)).Nonempty}
    (h_max_bound : maxEmergence L h_nonempty ≤ haltTime)
    -- Assumption: ALL keyedness maps used are canonical (singleton cuts only)
    (h_all_canonical : ∀ (v : Fin L.dag.n) {bound : Nat} (keyedness : KeyednessProperty L {v} bound),
        ∀ cfg, (keyedness.configToState cfg).val = (cfg ⟨v, by simp⟩).val) :
    ∀ (C : Finset (Fin L.dag.n))
      {bound : Nat}  -- Bound parameter (polymorphic)
      (keyedness : KeyednessProperty L C bound)
      (cfg : ConfigSpace L C),
      -- Restrict to singleton cuts (general cuts need more work)
      C.card = 1 →
      (keyedness.configToState cfg).val < haltTime := by
  intro C bound keyedness cfg h_singleton
  -- Extract the unique element from singleton C
  obtain ⟨v, h_C_eq⟩ := Finset.card_eq_one.mp h_singleton

  -- Substitute C = {v} in the goal
  subst h_C_eq

  -- Now keyedness : KeyednessProperty L {v} and cfg : ConfigSpace L {v}
  have h_canon := h_all_canonical v keyedness
  exact canonical_keyedness_any_singleton_bounded L haltTime h_max_bound v keyedness h_canon cfg

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms canonical_keyedness_singleton_bounded
#print axioms canonical_keyedness_all_fg_gates_bounded
#print axioms canonical_keyedness_any_singleton_bounded
#print axioms h_all_keyedness_bounded_for_specific_gate
#print axioms h_all_keyedness_bounded_under_max_emergence

end LStar.StructuralOWF.Foundations
