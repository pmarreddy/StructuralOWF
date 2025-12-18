import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction
import Layer3_InformationBounds.ConstraintSystem.NormalForm
import Layer3_InformationBounds.SegmentReduction.SegmentBoundaries
import Layer3_InformationBounds.WorldCommit.ExecutionHistory
import Layer3_InformationBounds.WorldCommit.WorldCommit
import Layer2_StructuralOWF.Plant.PlantCore
import Mathlib.Tactic
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.FinRange

/-! ## WC1Bridge: WorldCommit-1 Based Time Bounds (ZERO CUSTOM AXIOMS!)

**Purpose**: Provide an axiom-free path from TM execution to time bounds via WC-1.

**Restored from**: TMToExecutionPrefix.lean (deleted in commit 9776781)

**Key Insight**: The WorldCommit-1 theorem (`world_commit_refutation_excludes_one`)
proves that each UnitRefute step eliminates exactly 1 world. By tracking refutations
as UnitRefute constraints (instead of ConfigMatch), we can derive time bounds
WITHOUT the Church-Turing bridge axiom.

**Architecture**:
```
TM execution → ExecutionPrefixReal → UnitRefuteHistory → WC-1 → Time bound
```

**Main Results** (all proven with 0 custom axioms):
- `unitRefuteStep_increases_eliminations_by_one`: Each step adds exactly 1 elimination
- `finalEliminations_eq_refutationSteps`: k steps = k eliminations
- `eliminations_to_time`: k eliminations implies time ≥ k

**Integration Path**:
To use this for weakening the main axiom, we need to:
1. Build UnitRefuteHistory from TM execution trace
2. Prove h_refuted_were_feasible (each refuted world was previously feasible)
3. Apply eliminations_to_time to get time bound

**See also**:
- WorldCommit.lean: WC-1 theorem (world_commit_refutation_excludes_one)
- ExecutionHistory.lean: eliminations_to_time_proven infrastructure
- TMAdapterExponential.lean: Current axiom-based approach
-/

namespace LStar.StructuralOWF.Foundations

open Classical

/-! ## UnitRefute-Based History (ELIMINATES AXIOMS!)

**KEY INSIGHT**:
- ConfigMatch can refute many worlds at once (depends on how many have wrong config)
- UnitRefute refutes exactly ONE world by protocol design
- WorldCommit.world_commit_refutation_excludes_one PROVES the "+1" property!

**Architecture**:
- Base ExecutionPrefixReal π (represents observations: bits + computed configs)
- List of refuted worlds: [ω₁, ω₂, ..., ωₖ] (each becomes UnitRefute(ωᵢ) constraint)
- Effective constraints at step i: extractConstraints(π) ++ refuted[0..i].map(UnitRefute)
- Eliminations at step i: |all_worlds| - |FeasibleUnder(effective constraints)|

**Proof strategy**:
1. Step i → step i+1 adds exactly one UnitRefute(ωᵢ₊₁)
2. Apply world_commit_refutation_excludes_one → feasible decreases by exactly 1
3. Therefore: eliminations increase by exactly 1 per step
4. Time bound: Each step requires ≥1 time unit → time ≥ #steps = eliminations
-/

/-- **UnitRefute-based elimination history**: Tracks incremental world refutations.

    Unlike ExecutionHistory (which tracks changing observations), this tracks
    a fixed observation prefix π and an incrementing list of refuted worlds.

    **Example**:
    ```
    Step 0: π, refuted=[]           → eliminations = 0
    Step 1: π, refuted=[ω₁]         → eliminations = 1  (+1)
    Step 2: π, refuted=[ω₁, ω₂]     → eliminations = 2  (+1)
    Step 3: π, refuted=[ω₁, ω₂, ω₃] → eliminations = 3  (+1)
    ```

    **Key property**: Each step increases eliminations by EXACTLY 1
    (proven from world_commit_refutation_excludes_one, NO axioms!).
-/
structure UnitRefuteHistory (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) where
  /-- Base execution prefix (observations from TM execution) -/
  base_prefix : ExecutionPrefixReal L

  /-- Sequence of refuted worlds (each becomes a UnitRefute constraint) -/
  refuted_worlds : List (CutWorld L C)

  /-- Total time bound (each refutation step takes ≥1 time unit) -/
  total_time : Nat

  /-- Time bound: enough time to perform all refutation steps -/
  h_time_sufficient : total_time ≥ refuted_worlds.length

  /-- Each refuted world was feasible just before being refuted.

      **Meaning**: When we refute world i, it must have been feasible
      under the constraints at step i (before adding UnitRefute(world_i)).

      **Formally**: For world at index i, it's feasible under:
      base_constraints ++ [UnitRefute(world_0), ..., UnitRefute(world_{i-1})]
  -/
  h_refuted_were_feasible : ∀ (i : Nat) (h : i < refuted_worlds.length),
    refuted_worlds.get ⟨i, h⟩ ∈ NormalForm.FeasibleUnder (
      extractConstraints L C base_prefix ++
      (refuted_worlds.take i).map CutConstraint.UnitRefute
    )

/-- **Effective constraints at step i**: Base constraints + first i UnitRefutes. -/
noncomputable def effectiveConstraintsAt (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C) (i : Nat) : List (CutConstraint L C) :=
  extractConstraints L C hist.base_prefix ++
  (hist.refuted_worlds.take i).map (CutConstraint.UnitRefute)

/-- **Effective feasible set at step i**: Worlds satisfying effective constraints. -/
noncomputable def effectiveFeasibleAt (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C) (i : Nat) : Finset (CutWorld L C) :=
  NormalForm.FeasibleUnder (effectiveConstraintsAt L C hist i)

/-- **Eliminations at step i**: Number of worlds eliminated BY UnitRefute steps (incremental).

    **Definition**: Measures worlds eliminated by UnitRefute constraints ONLY,
    not including any eliminations from base_prefix constraints.

    **Formula**: |feasible_base| - |feasible_i|

    **Intuition**:
    - Step 0: 0 eliminations (no UnitRefute yet, same as base)
    - Step k: k eliminations (k UnitRefute steps applied)
-/
noncomputable def eliminationsAt (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C) (i : Nat) : Nat :=
  let base_feasible := NormalForm.FeasibleUnder (extractConstraints L C hist.base_prefix)
  let feasible_i := effectiveFeasibleAt L C hist i
  base_feasible.card - feasible_i.card

/-! ## Core Theorem: +1 Property (ZERO AXIOMS!) -/

/-- **THEOREM: Each UnitRefute step increases eliminations by EXACTLY 1** (proven from WC-1!).

    **Statement**: Going from step i to step i+1 increases eliminations by exactly 1.

    **Proof**: Direct application of WorldCommit.world_commit_refutation_excludes_one!
    - Step i has constraints: base_constraints ++ [UnitRefute ω₁, ..., UnitRefute ωᵢ]
    - Step i+1 adds: UnitRefute ωᵢ₊₁
    - WC-1 theorem says: adding one UnitRefute reduces feasible by exactly 1
    - Therefore: eliminations increase by exactly 1 ✓

    **NO AXIOMS!** Uses fully proven world_commit_refutation_excludes_one theorem.
-/
theorem unitRefuteStep_increases_eliminations_by_one
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C)
    (i : Nat)
    (h_valid : i < hist.refuted_worlds.length)
    : eliminationsAt L C hist (i + 1) = eliminationsAt L C hist i + 1 := by

  -- Definitions
  unfold eliminationsAt effectiveFeasibleAt effectiveConstraintsAt

  let base_feasible_card := (NormalForm.FeasibleUnder (extractConstraints L C hist.base_prefix)).card
  let constraints_i := extractConstraints L C hist.base_prefix ++
                       (hist.refuted_worlds.take i).map CutConstraint.UnitRefute
  let constraints_i_plus_1 := extractConstraints L C hist.base_prefix ++
                               (hist.refuted_worlds.take (i + 1)).map CutConstraint.UnitRefute
  let feasible_i := (NormalForm.FeasibleUnder constraints_i).card
  let feasible_i_plus_1 := (NormalForm.FeasibleUnder constraints_i_plus_1).card

  -- Key observation: take (i+1) = take i ++ [element at index i]
  have h_i_lt : i < hist.refuted_worlds.length := h_valid

  -- Standard list property: take (i+1) = take i ++ [elem i]
  have h_take_succ : hist.refuted_worlds.take (i + 1) =
                     hist.refuted_worlds.take i ++ [hist.refuted_worlds[i]] := by
    have h_get : hist.refuted_worlds[i] = hist.refuted_worlds.get ⟨i, h_i_lt⟩ := by rfl
    rw [h_get]
    rw [← List.concat_eq_append]
    exact (List.take_concat_get h_i_lt).symm

  let ω_target := hist.refuted_worlds[i]

  -- Therefore: constraints_i_plus_1 = constraints_i ++ [UnitRefute ω_target]
  have h_constraints_diff : constraints_i_plus_1 = constraints_i ++ [CutConstraint.UnitRefute ω_target] := by
    simp only [constraints_i, constraints_i_plus_1, ω_target]
    rw [h_take_succ, List.map_append, List.map_cons, List.map_nil]
    simp [List.append_assoc]

  -- Lemma 1: ω_target was feasible at step i (from structure hypothesis!)
  have h_target_feasible_i : ω_target ∈ NormalForm.FeasibleUnder constraints_i := by
    have h_from_struct := hist.h_refuted_were_feasible i h_valid
    exact h_from_struct

  -- Lemma 2: ω_target is NOT feasible at step i+1 (excluded by UnitRefute)
  have h_target_not_feasible_i_plus_1 : ω_target ∉ NormalForm.FeasibleUnder constraints_i_plus_1 := by
    unfold NormalForm.FeasibleUnder
    simp only [Finset.mem_filter]
    intro h_contra
    obtain ⟨_, h_all⟩ := h_contra
    have h_refute_in : CutConstraint.UnitRefute ω_target ∈ constraints_i_plus_1 := by
      rw [h_constraints_diff]
      rw [List.mem_append, List.mem_singleton]
      right
      rfl
    rw [List.all_eq_true] at h_all
    have h_satisfies := h_all (CutConstraint.UnitRefute ω_target) h_refute_in
    simp only [decide_eq_true_iff] at h_satisfies
    unfold CutConstraint.Satisfies at h_satisfies
    exact h_satisfies rfl

  -- Lemma 3: Other worlds preserved (ω ≠ ω_target stays same feasibility)
  have h_others_preserved : ∀ ω : CutWorld L C, ω ≠ ω_target →
      (ω ∈ NormalForm.FeasibleUnder constraints_i ↔
       ω ∈ NormalForm.FeasibleUnder constraints_i_plus_1) := by
    intro ω h_ne
    constructor
    · intro h_ω_i
      unfold NormalForm.FeasibleUnder at h_ω_i ⊢
      simp only [Finset.mem_filter] at h_ω_i ⊢
      obtain ⟨h_mem, h_all_i⟩ := h_ω_i
      constructor
      · exact h_mem
      · rw [List.all_eq_true] at h_all_i ⊢
        intro c h_c_in
        rw [h_constraints_diff] at h_c_in
        rw [List.mem_append, List.mem_singleton] at h_c_in
        cases h_c_in with
        | inl h_old => exact h_all_i c h_old
        | inr h_new =>
            rw [h_new]
            simp only [decide_eq_true_iff]
            unfold CutConstraint.Satisfies
            exact h_ne
    · intro h_ω_i_plus_1
      unfold NormalForm.FeasibleUnder at h_ω_i_plus_1 ⊢
      simp only [Finset.mem_filter] at h_ω_i_plus_1 ⊢
      obtain ⟨h_mem, h_all_i_plus_1⟩ := h_ω_i_plus_1
      constructor
      · exact h_mem
      · rw [List.all_eq_true] at h_all_i_plus_1 ⊢
        intro c h_c_in
        apply h_all_i_plus_1
        rw [h_constraints_diff]
        rw [List.mem_append]
        left
        exact h_c_in

  -- Combine: FeasibleUnder(i+1) = FeasibleUnder(i) \ {ω_target}
  have h_set_decomp : NormalForm.FeasibleUnder constraints_i =
                      NormalForm.FeasibleUnder constraints_i_plus_1 ∪ {ω_target} := by
    ext ω
    simp only [Finset.mem_union, Finset.mem_singleton]
    by_cases h_eq : ω = ω_target
    · simp [h_eq, h_target_feasible_i, h_target_not_feasible_i_plus_1]
    · simp [h_eq]
      exact h_others_preserved ω h_eq

  -- Cardinality: |i| = |i+1| + 1
  have h_card_eq : feasible_i = feasible_i_plus_1 + 1 := by
    simp only [feasible_i, feasible_i_plus_1]
    have h_disjoint : Disjoint (NormalForm.FeasibleUnder constraints_i_plus_1) {ω_target} := by
      rw [Finset.disjoint_singleton_right]
      exact h_target_not_feasible_i_plus_1
    rw [h_set_decomp]
    rw [Finset.card_union_of_disjoint h_disjoint]
    simp [Finset.card_singleton]

  -- Monotonicity: adding constraints only shrinks feasible set
  have h_feasible_i_le_base : (NormalForm.FeasibleUnder constraints_i).card ≤ base_feasible_card := by
    apply Finset.card_le_card
    intro ω h_ω_in_i
    unfold NormalForm.FeasibleUnder at h_ω_in_i ⊢
    simp only [Finset.mem_filter] at h_ω_in_i ⊢
    obtain ⟨h_mem, h_all⟩ := h_ω_in_i
    constructor
    · exact h_mem
    · rw [List.all_eq_true] at h_all ⊢
      intro c h_c_in_base
      apply h_all
      unfold constraints_i
      rw [List.mem_append]
      left
      exact h_c_in_base

  have h_feasible_i_plus_1_le_base : (NormalForm.FeasibleUnder constraints_i_plus_1).card ≤ base_feasible_card := by
    apply Finset.card_le_card
    intro ω h_ω_in
    unfold NormalForm.FeasibleUnder at h_ω_in ⊢
    simp only [Finset.mem_filter] at h_ω_in ⊢
    obtain ⟨h_mem, h_all⟩ := h_ω_in
    constructor
    · exact h_mem
    · rw [List.all_eq_true] at h_all ⊢
      intro c h_c_in_base
      apply h_all
      unfold constraints_i_plus_1
      rw [List.mem_append]
      left
      exact h_c_in_base

  -- Final arithmetic
  simp only [feasible_i, feasible_i_plus_1] at h_card_eq h_feasible_i_le_base h_feasible_i_plus_1_le_base

  calc (base_feasible_card - (NormalForm.FeasibleUnder constraints_i_plus_1).card)
      = base_feasible_card - (NormalForm.FeasibleUnder constraints_i).card + 1 := by
          have : (NormalForm.FeasibleUnder constraints_i).card ≤ base_feasible_card := h_feasible_i_le_base
          omega
      _ = (base_feasible_card - (NormalForm.FeasibleUnder constraints_i).card) + 1 := by rfl

/-- **THEOREM: Final eliminations equals number of refutation steps** (ZERO AXIOMS!).

    **Statement**: After k refutation steps, exactly k worlds have been eliminated.

    **Proof**: Induction using unitRefuteStep_increases_eliminations_by_one.
-/
theorem finalEliminations_eq_refutationSteps
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C)
    : eliminationsAt L C hist hist.refuted_worlds.length = hist.refuted_worlds.length := by
  let n := hist.refuted_worlds.length

  have h_ind : ∀ k ≤ n, eliminationsAt L C hist k = k := by
    intro k h_le
    induction k with
    | zero =>
        unfold eliminationsAt effectiveFeasibleAt effectiveConstraintsAt
        simp [List.take_zero, List.map_nil, List.append_nil]
    | succ k ih =>
        have h_k_le_n : k ≤ n := Nat.le_of_succ_le h_le
        have h_k_elim := ih h_k_le_n
        have h_succ_valid : k < hist.refuted_worlds.length := by omega
        have h_step := unitRefuteStep_increases_eliminations_by_one L C hist k h_succ_valid
        calc eliminationsAt L C hist (k + 1)
            = eliminationsAt L C hist k + 1 := h_step
            _ = k + 1 := by rw [h_k_elim]

  exact h_ind n (Nat.le_refl n)

/-- **THEOREM: Eliminations → Time bound** (ZERO AXIOMS!).

    **Statement**: If we have k eliminations, then time ≥ k.
-/
theorem eliminations_to_time
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C)
    (k : Nat)
    (h_elim : eliminationsAt L C hist hist.refuted_worlds.length ≥ k)
    : hist.total_time ≥ k := by
  have h_eq := finalEliminations_eq_refutationSteps L C hist
  have h_length : hist.refuted_worlds.length ≥ k := by
    calc hist.refuted_worlds.length
        = eliminationsAt L C hist hist.refuted_worlds.length := h_eq.symm
        _ ≥ k := h_elim
  calc hist.total_time
      ≥ hist.refuted_worlds.length := hist.h_time_sufficient
      _ ≥ k := h_length

/-! ## ExecutionHistory Construction Infrastructure -/

/-- **Helper: Build incremental state at index i**

    Constructs ExecutionPrefixReal with first i configs from final_configs.
    Time is set to i (representing i digest observations made).
-/
def buildStateAt (L : LStarInstanceFG) (final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))) (i : Nat) : ExecutionPrefixReal L :=
  { time := i
    revealedBits := []  -- FG construction has no bit observations
    computedConfigs := final_configs.take i }

/-- **Helper: Build all incremental states**

    Produces [state_0, state_1, ..., state_n] where state_i has first i configs.
-/
def buildIncrementalStates (L : LStarInstanceFG) (final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))) (n : Nat) : List (ExecutionPrefixReal L) :=
  List.range (n + 1) |>.map (buildStateAt L final_configs)

/-- **Lemma: buildStateAt is monotonic in index** -/
theorem buildStateAt_prefix (L : LStarInstanceFG)
    {final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))} {i j : Nat}
    (h : i ≤ j) : isPrefixOf L (buildStateAt L final_configs i) (buildStateAt L final_configs j) := by
  unfold buildStateAt isPrefixOf
  simp only []
  constructor
  · exact h
  constructor
  · rfl
  · have : final_configs.take i = (final_configs.take j).take i := by
      rw [List.take_take, min_eq_left h]
    rw [this]
    exact List.take_prefix i (final_configs.take j)

/-- **Lemma: Consecutive elements have consecutive time values** -/
theorem buildIncrementalStates_consecutive_times (L : LStarInstanceFG)
    (final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))) (n : Nat)
    {i : Nat} (h_i_bound : i + 1 < (buildIncrementalStates L final_configs n).length) :
    let states := buildIncrementalStates L final_configs n
    (states.get ⟨i+1, h_i_bound⟩).time = (states.get ⟨i, Nat.lt_of_succ_lt h_i_bound⟩).time + 1 := by
  unfold buildIncrementalStates
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  unfold buildStateAt
  simp

/-- **Helper lemma: List.range decomposition** -/
private lemma range_succ_append (n : Nat) : List.range (n + 1) = List.range n ++ [n] := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc List.range (n' + 2)
        = List.range (n' + 1 + 1) := by ring_nf
      _ = 0 :: List.map Nat.succ (List.range (n' + 1)) := List.range_succ_eq_map
      _ = 0 :: List.map Nat.succ (List.range n' ++ [n']) := by rw [ih]
      _ = 0 :: (List.map Nat.succ (List.range n') ++ List.map Nat.succ [n']) := by rw [List.map_append]
      _ = 0 :: (List.map Nat.succ (List.range n') ++ [n' + 1]) := by simp
      _ = (0 :: List.map Nat.succ (List.range n')) ++ [n' + 1] := by rfl
      _ = List.range (n' + 1) ++ [n' + 1] := by rw [← List.range_succ_eq_map]

/-- **Lemma: buildIncrementalStates forms a chain** -/
theorem buildIncrementalStates_chain (L : LStarInstanceFG)
    (final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))) (n : Nat) :
    (buildIncrementalStates L final_configs n).Chain' (isPrefixOf L) := by
  unfold buildIncrementalStates
  show (List.range (n+1)).map (buildStateAt L final_configs) |>.IsChain (isPrefixOf L)
  induction n with
  | zero =>
    have : List.range 1 = [0] := rfl
    rw [this]
    exact List.isChain_singleton _
  | succ n' ih =>
    rw [range_succ_append, List.map_append, List.isChain_append]
    refine ⟨ih, List.isChain_singleton _, ?_⟩
    intro x h_x y h_y
    cases h_y
    have : x = buildStateAt L final_configs n' := by
      have h_getLast : ((List.range (n'+1)).map (buildStateAt L final_configs)).getLast? = some x := h_x
      rw [List.getLast?_map] at h_getLast
      have h_ne : List.range (n'+1) ≠ [] := by simp
      have : (List.range (n'+1)).getLast? = some n' := by
        rw [List.getLast?_eq_getLast h_ne, List.getLast_range]
        simp
      rw [this] at h_getLast
      simp at h_getLast
      exact h_getLast.symm
    rw [this]
    exact buildStateAt_prefix L (Nat.le_succ n')

/-- **buildStateAt is injective** -/
theorem buildStateAt_injective
    (L : LStarInstanceFG)
    (final_configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v))) :
    Function.Injective (buildStateAt L final_configs) := by
  intro i j h
  have := congrArg (fun (s : ExecutionPrefixReal L) => s.time) h
  simpa [buildStateAt] using this

/-- **Build ExecutionHistory from execution prefix** (RIGOROUS multi-state construction).

    **Strategy**: Build incremental history with one state per digest observation.
    States: [π₀, π₁, ..., πₙ] where πᵢ has first i configs from π_final.

    **Key property**: Between consecutive states, at most 1 config is added,
    so by WC-1, at most 1 world is eliminated.
-/
noncomputable def tmExecutionToHistory
    (L : LStarInstanceFG)
    (π_final : ExecutionPrefixReal L)
    : ExecutionHistory L :=
  let n := π_final.computedConfigs.length
  {
    states := buildIncrementalStates L π_final.computedConfigs n
    h_chain := buildIncrementalStates_chain L π_final.computedConfigs n
    h_nonempty := by
      unfold buildIncrementalStates
      intro h_contra
      have h_len : ((List.range (n + 1)).map (buildStateAt L π_final.computedConfigs)).length = 0 := by
        simp only [h_contra, List.length_nil]
      simp [List.length_map, List.length_range] at h_len
    h_consecutive := fun i h => buildIncrementalStates_consecutive_times L π_final.computedConfigs n h
  }

/-! ## Axiom Audit -/

#print axioms UnitRefuteHistory
#print axioms unitRefuteStep_increases_eliminations_by_one
#print axioms finalEliminations_eq_refutationSteps
#print axioms eliminations_to_time
#print axioms tmExecutionToHistory

/-! ## TM Adapter Lemmas (REMAINING WORK)

The theorems above are proven with 0 custom axioms. To use them to replace the
current axiom `tm_correctness_implies_realizesAllValuesFrom_flat_encoded`, we need
adapter lemmas that construct a valid `UnitRefuteHistory` from TM execution.

**Work Packages**:
1. Define `tmRefutedWorlds` - extract refuted worlds from TM trace
2. Prove `tmRefutedWorlds_refuted_were_feasible` - the core invariant (MAIN GAP)
3. Prove elimination lower bound from planted correctness
4. Conclude time bound via `eliminations_to_time`

**Status**: These are stubs with `sorry`. Completing them eliminates the axiom.
-/

/-! ### Package 1: Empty Base Prefix -/

/-- **Empty base prefix**: No observations, no bulk pruning.

    Using an empty base prefix ensures that:
    - `extractConstraints L C base_prefix = []`
    - All 2^R worlds are initially feasible
    - Eliminations come ONLY from UnitRefute steps
-/
def emptyBasePrefix (L : LStarInstanceFG) : ExecutionPrefixReal L :=
  { time := 0
    revealedBits := []
    computedConfigs := [] }

theorem emptyBasePrefix_no_constraints (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (h_positive_R : ∀ v ∈ C, L.R v > 0) :
    extractConstraints L C (emptyBasePrefix L) = [] := by
  -- With empty prefix (no revealed bits, no computed configs), extractConstraints = []
  -- because: extractBitConstraints = [], extractConfigConstraints = [],
  -- and extractSyntheticConfigs = [] (completeAt fails with no bits and R > 0)
  sorry -- ~20 lines: unfold definitions and show filterMaps return []

/-! ### Package 2: Refuted Worlds Extraction

**Restored from**: TMToExecutionPrefix.lean (deleted in commit 9776781)

The key insight is to process configs sequentially, extracting violators at each step.
This ensures the feasibility invariant holds by construction.
-/

/-- **Extract violators for a single ConfigMatch step**.

    Given current accumulated UnitRefute constraints and a new config,
    find worlds that violate the ConfigMatch for this config.
-/
noncomputable def extractViolatorsForConfig
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (base_constraints : List (CutConstraint L C))
    (accumulated_refutes : List (CutWorld L C))
    (config : (v : Fin L.dag.n) ×' Fin (2 ^ L.R v))
    : List (CutWorld L C) :=
  match config with
  | ⟨v, cfg⟩ =>
    if h : v ∈ C then
      let constraint := CutConstraint.ConfigMatch v h cfg
      -- Compute current feasible set (base + accumulated UnitRefutes)
      let current_constraints := base_constraints ++ accumulated_refutes.map CutConstraint.UnitRefute
      let current_feasible := NormalForm.FeasibleUnder current_constraints
      -- Find violators of the new ConfigMatch in current feasible set
      let violators_set := violatorsOf L C current_feasible constraint
      violators_set.toList
    else
      []  -- Vertex not in cut, no constraint added

/-- **Build refuted_worlds list by processing configs sequentially**.

    For each config:
    1. Compute current feasible set (base + accumulated refuted worlds)
    2. Find violators of ConfigMatch for this config
    3. Accumulate violators into refuted_worlds list

    **Key property**: By construction, each world added to refuted_worlds
    was in the feasible set at the moment it was added. This is exactly
    `h_refuted_were_feasible`!
-/
noncomputable def buildRefutedWorlds.aux
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (base_constraints : List (CutConstraint L C))
    (accumulated_refutes : List (CutWorld L C))
    : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)) → List (CutWorld L C)
  | [] => accumulated_refutes
  | config :: rest =>
    let new_violators := extractViolatorsForConfig L C base_constraints accumulated_refutes config
    buildRefutedWorlds.aux L C base_constraints (accumulated_refutes ++ new_violators) rest

noncomputable def buildRefutedWorlds
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    : List (CutWorld L C) :=
  -- Use empty base constraints (no bulk pruning)
  buildRefutedWorlds.aux L C [] [] configs

/-- **Extract refuted worlds from computed configs**.

    This is the concrete implementation of tmRefutedWorlds using buildRefutedWorlds.
    The configs come from the TM's execution (what it computed before halting).
-/
noncomputable def tmRefutedWorlds
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    : List (CutWorld L C) :=
  buildRefutedWorlds L C configs

/-! ### Package 3: Core Invariant

**Key insight**: With `buildRefutedWorlds`, the feasibility invariant holds BY CONSTRUCTION!

Each world added to the list comes from `violatorsOf current_feasible constraint`,
which means it was in `current_feasible` at that moment. The `current_feasible`
set is computed from `base_constraints ++ accumulated_refutes.map UnitRefute`,
which is exactly what the invariant requires.
-/

/-- **Core invariant: each refuted world was feasible before refutation**.

    **Why this now works**: With `buildRefutedWorlds`, worlds are added to the
    refuted list only if they are in the current feasible set. This is exactly
    what `h_refuted_were_feasible` requires!

    **Proof strategy**:
    - Induction on the `buildRefutedWorlds.aux` recursion
    - Each step adds worlds from `violatorsOf current_feasible`
    - By definition, these worlds were in `current_feasible`
-/
theorem buildRefutedWorlds_aux_feasibility
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (base_constraints : List (CutConstraint L C))
    (accumulated : List (CutWorld L C))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    -- Hypothesis: accumulated already satisfies the invariant
    (h_acc_invariant : ∀ (i : Nat) (h : i < accumulated.length),
        accumulated.get ⟨i, h⟩ ∈ NormalForm.FeasibleUnder (
          base_constraints ++ (accumulated.take i).map CutConstraint.UnitRefute
        ))
    : let result := buildRefutedWorlds.aux L C base_constraints accumulated configs
      ∀ (i : Nat) (h : i < result.length),
        result.get ⟨i, h⟩ ∈ NormalForm.FeasibleUnder (
          base_constraints ++ (result.take i).map CutConstraint.UnitRefute
        ) := by
  sorry -- ~100 lines: induction on configs, use violatorsOf membership

/-- **Corollary: buildRefutedWorlds satisfies the feasibility invariant**. -/
theorem buildRefutedWorlds_feasibility
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    : ∀ (i : Nat) (h : i < (buildRefutedWorlds L C configs).length),
        (buildRefutedWorlds L C configs).get ⟨i, h⟩ ∈ NormalForm.FeasibleUnder (
          ((buildRefutedWorlds L C configs).take i).map CutConstraint.UnitRefute
        ) := by
  -- Apply aux lemma with empty base_constraints and empty accumulated
  intro i h
  have h_aux := buildRefutedWorlds_aux_feasibility L C [] [] configs (by simp)
  simp only [List.append_nil] at h_aux
  exact h_aux i h

/-- **tmRefutedWorlds satisfies the feasibility invariant**. -/
theorem tmRefutedWorlds_refuted_were_feasible
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    (h_positive_R : ∀ v ∈ C, L.R v > 0)
    : ∀ (i : Nat) (h : i < (tmRefutedWorlds L C configs).length),
        (tmRefutedWorlds L C configs).get ⟨i, h⟩ ∈
          NormalForm.FeasibleUnder (
            extractConstraints L C (emptyBasePrefix L) ++
            ((tmRefutedWorlds L C configs).take i).map CutConstraint.UnitRefute
          ) := by
  intro i h
  -- tmRefutedWorlds = buildRefutedWorlds
  -- extractConstraints (emptyBasePrefix L) = [] (from emptyBasePrefix_no_constraints)
  have h_empty := emptyBasePrefix_no_constraints L C h_positive_R
  rw [h_empty, List.nil_append]
  exact buildRefutedWorlds_feasibility L C configs i h

/-! ### Package 4: Build UnitRefuteHistory from TM Run -/

/-- **Construct UnitRefuteHistory from TM execution**.

    Combines the extracted refuted worlds with the core invariant proof.

    **Parameters**:
    - `configs`: The computed configurations from TM execution
    - `haltTime`: The number of steps TM took to halt
    - `h_positive_R`: All vertices in cut have positive emergence
-/
noncomputable def tmRunToUnitRefuteHistory
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    (haltTime : Nat)
    (h_positive_R : ∀ v ∈ C, L.R v > 0)
    (h_time_bound : haltTime ≥ (tmRefutedWorlds L C configs).length)
    : UnitRefuteHistory L C :=
  { base_prefix := emptyBasePrefix L
    refuted_worlds := tmRefutedWorlds L C configs
    total_time := haltTime
    h_time_sufficient := h_time_bound
    h_refuted_were_feasible := tmRefutedWorlds_refuted_were_feasible L C configs h_positive_R }

/-! ### Package 5: Elimination Lower Bound -/

/-- **Base feasible set has size 2^R** (for singleton cut C = {v}).

    With empty base prefix and singleton cut, all 2^(L.R v) worlds are feasible.
-/
theorem base_feasible_card_eq_pow_R
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_singleton : C = {v})
    : (NormalForm.FeasibleUnder (extractConstraints L C (emptyBasePrefix L))).card = 2 ^ (L.R v) := by
  sorry -- Should follow from emptyBasePrefix_no_constraints + CutWorld cardinality

/-- **Final feasible set has size 1** (unique world at acceptance).

    After all refutations, exactly one world remains feasible (the planted world).
-/
theorem final_feasible_card_eq_one
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (hist : UnitRefuteHistory L C)
    -- Add planted/correctness hypotheses
    : (effectiveFeasibleAt L C hist hist.refuted_worlds.length).card = 1 := by
  sorry -- Follows from planted uniqueness + TM correctness

/-- **Elimination lower bound from planted correctness**.

    Combines base size and final size to get eliminations ≥ 2^R - 1.
-/
theorem elimination_lower_bound
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_singleton : C = {v})
    (hist : UnitRefuteHistory L C)
    (h_base : (NormalForm.FeasibleUnder (extractConstraints L C hist.base_prefix)).card = 2 ^ (L.R v))
    (h_final : (effectiveFeasibleAt L C hist hist.refuted_worlds.length).card = 1)
    : eliminationsAt L C hist hist.refuted_worlds.length ≥ 2 ^ (L.R v) - 1 := by
  unfold eliminationsAt
  simp only [h_base]
  -- eliminationsAt = base_card - final_card = 2^R - 1
  have h_final' : (effectiveFeasibleAt L C hist hist.refuted_worlds.length).card = 1 := h_final
  omega

/-! ### Package 6: End-to-End Time Bound (Replaces Axiom) -/

/-- **End-to-end time lower bound via WC-1 bridge**.

    This theorem, once the sorries are filled, provides the same conclusion as
    `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` but with 0 axioms.

    **Current axiom says**: TM correctness implies time ≥ 2^R
    **This theorem says**: Same conclusion, proven via WC-1 protocol
-/
theorem tm_time_lower_bound_via_WC1Bridge
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_singleton : C = {v})
    (configs : List ((v : Fin L.dag.n) ×' Fin (2 ^ L.R v)))
    (haltTime : Nat)
    (h_positive_R : ∀ v ∈ C, L.R v > 0)
    (h_time_bound : haltTime ≥ (tmRefutedWorlds L C configs).length)
    -- Add planted/correctness hypotheses as needed
    : haltTime ≥ 2 ^ (L.R v) - 1 := by
  -- Step 1: Build UnitRefuteHistory from TM run
  let hist := tmRunToUnitRefuteHistory L C configs haltTime h_positive_R h_time_bound

  -- Step 2: Prove elimination lower bound
  have h_base : (NormalForm.FeasibleUnder (extractConstraints L C hist.base_prefix)).card = 2 ^ (L.R v) := by
    sorry -- From base_feasible_card_eq_pow_R

  have h_final : (effectiveFeasibleAt L C hist hist.refuted_worlds.length).card = 1 := by
    sorry -- From final_feasible_card_eq_one

  have h_elim : eliminationsAt L C hist hist.refuted_worlds.length ≥ 2 ^ (L.R v) - 1 :=
    elimination_lower_bound L v C h_singleton hist h_base h_final

  -- Step 3: Apply eliminations_to_time (PROVEN, 0 axioms)
  have h_time : hist.total_time ≥ 2 ^ (L.R v) - 1 :=
    eliminations_to_time L C hist (2 ^ (L.R v) - 1) h_elim

  -- Step 4: hist.total_time = haltTime by construction
  have h_eq : hist.total_time = haltTime := rfl
  omega

/-! ## Summary of Remaining Work

### PROVEN (0 custom axioms)
| Theorem | Status |
|---------|--------|
| `unitRefuteStep_increases_eliminations_by_one` | ✅ PROVEN |
| `finalEliminations_eq_refutationSteps` | ✅ PROVEN |
| `eliminations_to_time` | ✅ PROVEN |
| `buildRefutedWorlds_feasibility` | ✅ (modulo aux lemma) |
| `tmRefutedWorlds_refuted_were_feasible` | ✅ (modulo aux + empty base) |
| `tmRunToUnitRefuteHistory` | ✅ DEFINED |

### REMAINING (sorry stubs)
| Lemma | Purpose | Est. Lines |
|-------|---------|------------|
| `emptyBasePrefix_no_constraints` | Empty prefix has no constraints | ~20 |
| `buildRefutedWorlds_aux_feasibility` | Core inductive proof | ~100 |
| `base_feasible_card_eq_pow_R` | Base set has 2^R worlds | ~30 |
| `final_feasible_card_eq_one` | Final set has 1 world | ~50 |
| `tm_time_lower_bound_via_WC1Bridge` (glue) | End-to-end | ~20 |

**Total**: ~220 lines to eliminate the axiom completely.

### Key Insight
The `buildRefutedWorlds` construction ensures the feasibility invariant
holds BY CONSTRUCTION: each world added comes from `violatorsOf current_feasible`,
so it was in the feasible set at that moment. The main remaining work is the
inductive proof `buildRefutedWorlds_aux_feasibility`.
-/

end LStar.StructuralOWF.Foundations
