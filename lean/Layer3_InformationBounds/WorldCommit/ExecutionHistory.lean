/-
Copyright (c) 2025 ButterflyEffect authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ButterflyEffect contributors
-/
import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction
import Layer3_InformationBounds.SegmentReduction.SegmentBoundaries
import Layer3_InformationBounds.SegmentReduction.SegmentReduction
import Layer3_InformationBounds.WorldCommit.WorldCommit

/-! ## Suffix Lemmas (for threading suffix witness through recursion) -/

/-- Every list is a suffix of itself -/
lemma suffix_refl {α : Type _} (l : List α) : l <:+ l := ⟨[], by simp [List.nil_append]⟩

/-- Tail of a suffix is a suffix -/
lemma suffix_tail {α : Type _} {l full : List α} (h : l <:+ full) : l.tail <:+ full := by
  obtain ⟨t, ht⟩ := h
  cases l with
  | nil =>
    -- Empty list: tail is still empty, still a suffix
    simp [ht]
  | cons hd tl =>
    -- Non-empty list: tail is a suffix
    simp only [List.tail_cons]
    -- full = t ++ (hd :: tl), so tl is suffix with prefix (t ++ [hd])
    exact ⟨t ++ [hd], by simp [←ht]⟩

/-! ## ExecutionHistory: Time Bounds from Refutation Counting

**Purpose**: Formalize WorldCommit protocol's per-world refutation mechanism → time bounds.

**WorldCommit Protocol (W = 1)** (WorldCommit.lean):
- Each refutation adds exactly one UnitRefute(ω*) to constraint system
- WC-1: Exactly 1 world excluded per refutation (protocol specification)
- Sequential world checking via CommitSelector (computational constraint)

**Proof chain** (§7, Appendix C):
```
refutations = 2^{ρ-s}     [SegmentReduction.lean]
    ↓ WC-1: W = 1
boundaries ≥ 2^{ρ-s}      [This file]
    ↓ each boundary = 1 time step
time ≥ 2^{ρ-s}            [This file]
```

**Infrastructure**: Includes List.IsPrefix lemmas for monotonicity proofs.

**Main results**: time_bound_from_refutations (refutations → boundaries → time lower bound)

**Trust boundary**: 0 axioms, 0 sorries - FULLY PROVEN

See Layer3_InformationBounds/Layer3_README.md §World Commitment.

## Implementation

- ExecutionHistory structure
- boundaries_from_refutations (proven with WC-1)
- time_from_boundaries (proven)
-/

open BigOperators Classical

namespace LStar.StructuralOWF.Foundations

variable {L : LStarInstanceFG}

/-! ## List.IsPrefix Infrastructure

This lemma should be in Mathlib but is missing. We prove it here.
-/

namespace List

/-- **IsPrefix preserves membership**: If l₁ is a prefix of l₂ and x ∈ l₁, then x ∈ l₂. -/
theorem IsPrefix.subset {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) : ∀ x ∈ l₁, x ∈ l₂ := by
  intro x hx
  obtain ⟨t, rfl⟩ := h
  apply List.mem_append_left
  exact hx

end List

/-! ## Execution History Structure -/

/-- **Execution history**: Sequence of execution snapshots forming a chain.

    Represents the execution as a sequence of states [π₀, π₁, π₂, ..., πₙ],
    where each πᵢ is a prefix of πᵢ₊₁ (πᵢ ≤ πᵢ₊₁).

    **Key property**: Can count segment boundaries between consecutive states.

    **Difference from ExecutionPrefixReal**: This tracks the full history,
    not just the final state. This allows us to count boundaries explicitly.

    **Example**:
    ```
    π₀: time=0, revealedBits=[], computedConfigs=[]
    π₁: time=5, revealedBits=[(v=3,i=0,b=1)], computedConfigs=[]
    π₂: time=12, revealedBits=[(v=3,i=0,b=1), (v=3,i=1,b=0)], computedConfigs=[cfg₁]
    ...
    πₙ: final state
    ```
-/
structure ExecutionHistory (L : LStarInstanceFG) where
  /-- Sequence of execution snapshots, from initial to final state -/
  states : List (ExecutionPrefixReal L)

  /-- States form a chain: each state is a prefix of the next -/
  h_chain : states.IsChain (isPrefixOf L)

  /-- History is nonempty (at least contains initial or final state) -/
  h_nonempty : states ≠ []

  /-- Consecutive states have consecutive time values (structural property) -/
  h_consecutive : ∀ (i : Nat) (h : i + 1 < states.length),
    (states.get ⟨i+1, h⟩).time = (states.get ⟨i, Nat.lt_of_succ_lt h⟩).time + 1

/-! ## Boundary Counting -/

/-- **Count segment boundaries** in execution history.

    A boundary occurs between consecutive states πᵢ and πᵢ₊₁ when
    their constraint normal forms differ (SegmentBoundary πᵢ πᵢ₊₁).

    **Interpretation**: Each boundary = one observation that changed constraints.

    **Example**:
    ```
    [π₀, π₁, π₂, π₃] with boundaries between (π₀,π₁) and (π₂,π₃)
    → boundaryCount = 2
    ```

    **Implementation**: Recursively count consecutive pairs with different ConstraintNFs.
    Uses Classical logic for decidability of ConstraintNF equality.
-/

noncomputable def boundaryCount.aux (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    List (ExecutionPrefixReal L) → Nat
  | [] => 0
  | [_] => 0
  | π₁ :: π₂ :: rest =>
      (if SegmentBoundary L C π₁ π₂ then 1 else 0) + aux L C (π₂ :: rest)

noncomputable def boundaryCount (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L) : Nat :=
  boundaryCount.aux L C hist.states

/-! ## Digest-Only Boundary Counting (for W=1 Proof)

**PURPOSE**: Count only digest boundaries (not bit boundaries) to enable clean W=1 proof.

**KEY INSIGHT**: Each digest boundary corresponds to exactly one WorldCommit step,
which eliminates at most 1 world by WC-1 theorem.

**ARCHITECTURE**: Clone of boundaryCount but using DigestBoundary predicate.
-/

/-- **Digest boundary count (auxiliary)**: Count digest boundaries in state list.

    **Recursive structure**: Identical to boundaryCount.aux but uses DigestBoundary.
-/
noncomputable def digestBoundaryCount.aux (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) :
    List (ExecutionPrefixReal L) → Nat
  | [] => 0
  | [_] => 0
  | π₁ :: π₂ :: rest =>
      (if DigestBoundary L C π₁ π₂ then 1 else 0) + aux L C (π₂ :: rest)

/-- **Digest boundary count**: Number of digest boundaries in execution history.

    **Definition**: Count pairs of adjacent states with digest boundary.

    **Used for**: W=1 proof via WorldCommit protocol.
-/
noncomputable def digestBoundaryCount (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L) : Nat :=
  digestBoundaryCount.aux L C hist.states

/-- **Auxiliary lemma: digest boundaries ≤ segment boundaries**.

    **Statement**: For any state list, digest boundary count ≤ segment boundary count.

    **Proof**: By structural induction on the list. At each pair (π₁, π₂):
    - If DigestBoundary holds, then SegmentBoundary holds (by digestBoundary_implies_segmentBoundary)
    - So both counters increment by 1
    - If DigestBoundary doesn't hold, digestBoundaryCount.aux adds 0
      while boundaryCount.aux might add 1 (bit-only boundary)
    - By IH on tail: digestBoundaryCount.aux(tail) ≤ boundaryCount.aux(tail)
    - Therefore: digestBoundaryCount.aux ≤ boundaryCount.aux
-/
theorem digestBoundaryCount_aux_le_boundaryCount_aux
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (states : List (ExecutionPrefixReal L))
    : digestBoundaryCount.aux L C states ≤ boundaryCount.aux L C states := by
  induction states with
  | nil =>
      -- Base case: empty list
      simp [digestBoundaryCount.aux, boundaryCount.aux]
  | cons π₁ rest IH =>
      cases rest with
      | nil =>
          -- Base case: single element
          simp [digestBoundaryCount.aux, boundaryCount.aux]
      | cons π₂ rest' =>
          -- Inductive case: at least two elements
          unfold digestBoundaryCount.aux boundaryCount.aux

          -- Split on whether there's a digest boundary
          by_cases h_digest : DigestBoundary L C π₁ π₂

          case pos =>
            -- DigestBoundary holds
            simp [h_digest]
            -- DigestBoundary → SegmentBoundary (digestBoundary_implies_segmentBoundary theorem)
            have h_seg := digestBoundary_implies_segmentBoundary L C π₁ π₂ h_digest
            simp [h_seg]
            -- Both add 1, so need: 1 + digest_tail ≤ 1 + boundary_tail
            -- Which follows from IH on tail
            omega

          case neg =>
            -- No digest boundary
            simp [h_digest]
            -- digestBoundaryCount.aux adds 0
            -- boundaryCount.aux adds 0 or 1 (depending on SegmentBoundary)
            by_cases h_seg : SegmentBoundary L C π₁ π₂
            · -- SegmentBoundary but not DigestBoundary (bit-only boundary)
              simp [h_seg]
              -- Need: 0 + digest_tail ≤ 1 + boundary_tail
              -- Which follows from IH: digest_tail ≤ boundary_tail
              omega
            · -- No boundary at all
              simp [h_seg]
              -- Need: 0 + digest_tail ≤ 0 + boundary_tail
              -- Which is exactly IH
              exact IH

/-- **Digest boundaries are subset of all boundaries**.

    **Statement**: digestBoundaryCount ≤ boundaryCount.

    **Proof**: Direct application of digestBoundaryCount_aux_le_boundaryCount_aux.
-/
theorem digestBoundaryCount_le_boundaryCount
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    : digestBoundaryCount L C hist ≤ boundaryCount L C hist := by
  unfold digestBoundaryCount boundaryCount
  exact digestBoundaryCount_aux_le_boundaryCount_aux L C hist.states

/-- **Initial state** of execution history (first snapshot). -/
noncomputable def ExecutionHistory.initial (hist : ExecutionHistory L) : ExecutionPrefixReal L :=
  hist.states.head (List.ne_nil_of_length_pos (by
    have : hist.states.length > 0 := List.length_pos_iff.mpr hist.h_nonempty
    exact this))

/-- **Final state** of execution history (last snapshot). -/
noncomputable def ExecutionHistory.final (hist : ExecutionHistory L) : ExecutionPrefixReal L :=
  hist.states.getLast hist.h_nonempty

/-! ## Key Structural Lemmas -/

/-- **Refutation growth implies boundary**: If refutationCount grows, there's a boundary.

    This is the key lemma from SegmentReduction.lean that we'll use inductively.
-/
theorem growth_implies_boundary_exists
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_prefix : isPrefixOf L π₁ π₂)
    (h_growth : refutationCount L C π₁ < refutationCount L C π₂)
    : SegmentBoundary L C π₁ π₂ :=
  -- This theorem exists in SegmentReduction.lean in this file
  refutation_growth_implies_boundaries L C π₁ π₂ h_prefix h_growth

/-! ## Main Theorems -/

/-! ### Helper Lemmas for Chain Reasoning -/

/-- **Time monotonicity from isPrefixOf**: Earlier states have ≤ time. -/
theorem isPrefixOf_time_mono {π₁ π₂ : ExecutionPrefixReal L}
    (h : isPrefixOf L π₁ π₂) : π₁.time ≤ π₂.time :=
  h.1

/-- **Transitive time monotonicity**: Time is monotonic across execution chains.

    **Proof**: By induction on list structure. Uses isPrefixOf_time_mono for adjacent
    elements and Nat.le_trans for transitivity. -/
theorem time_mono_chain
    (states : List (ExecutionPrefixReal L))
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (π : ExecutionPrefixReal L)
    (h_mem : π ∈ states)
    : π.time ≤ (states.getLast h_nonempty).time := by
  -- Generalize π and induct on the list
  induction states generalizing π with
  | nil => contradiction
  | cons π₀ rest IH =>
      cases rest with
      | nil =>
          -- Base case: single element [π₀]
          -- π must equal π₀
          have : π = π₀ := by
            cases h_mem with
            | head => rfl
            | tail _ h => cases h
          simp [List.getLast, this]
      | cons π₁ rest' =>
          -- Inductive case: π₀ :: π₁ :: rest'
          have h_prefix : isPrefixOf L π₀ π₁ := by
            cases h_chain with | cons_cons h_rel _ => exact h_rel

          have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest') := by
            cases h_chain with | cons_cons _ h_rest => exact h_rest

          have h_tail_nonempty : π₁ :: rest' ≠ [] := by simp

          -- last of full list = last of tail
          have h_last_eq : (π₀ :: π₁ :: rest').getLast h_nonempty = (π₁ :: rest').getLast h_tail_nonempty := by
            simp [List.getLast]

          -- Split on whether π = π₀ or π ∈ tail
          by_cases h_eq : π = π₀
          case pos =>
              -- π = π₀
              have IH_π₁ : π₁.time ≤ ((π₁ :: rest').getLast h_tail_nonempty).time :=
                IH h_tail_chain h_tail_nonempty π₁ List.mem_cons_self

              calc π.time
                  = π₀.time := by rw [h_eq]
                _ ≤ π₁.time := isPrefixOf_time_mono h_prefix
                _ ≤ ((π₁ :: rest').getLast h_tail_nonempty).time := IH_π₁
                _ = ((π₀ :: π₁ :: rest').getLast h_nonempty).time := by rw [←h_last_eq]

          case neg =>
              -- π ≠ π₀, so π ∈ (π₁ :: rest')
              have h_mem_tail : π ∈ (π₁ :: rest') := by
                cases h_mem with
                | head => contradiction
                | tail _ h => exact h

              have IH_π : π.time ≤ ((π₁ :: rest').getLast h_tail_nonempty).time :=
                IH h_tail_chain h_tail_nonempty π h_mem_tail

              calc π.time
                  ≤ ((π₁ :: rest').getLast h_tail_nonempty).time := IH_π
                _ = ((π₀ :: π₁ :: rest').getLast h_nonempty).time := by rw [←h_last_eq]

/-- **Total eliminations are monotonic**: More observations → more world eliminations.

    This is the foundational monotonicity property. refutationCount (which counts only
    digest refutations) is NOT monotonic because worlds can move from "refuted by digest"
    to "excluded by bits". But totalEliminations IS monotonic.

    **Proof**: More constraints → fewer surviving worlds → more total eliminations.

    **Bit determinism requirement**: This theorem requires bit observation determinism
    (Property 4 from executionPrefix_compatible_with_planted axiom) to prove that
    reconstructedCfg is consistent when revealedBits form a prefix. In planted instance
    contexts (e.g., PlantedBoundaryDiversity.lean), this is available via
    `revealedBit_value_unique_at_position`. -/
theorem totalEliminations_monotone
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_prefix : isPrefixOf L π₁ π₂)
    (h_bit_determinism : ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
        (h_complete₁ : completeAt L C π₁ v h_v)
        (h_complete₂ : completeAt L C π₂ v h_v),
        reconstructedCfg L C π₁ v h_v h_complete₁ =
        reconstructedCfg L C π₂ v h_v h_complete₂)
    : totalEliminations L C π₁ ≤ totalEliminations L C π₂ := by
  -- **Key insight**: totalEliminations = |univ| - |feasible|
  -- Proving elim₁ ≤ elim₂ is equivalent to proving |feasible₂| ≤ |feasible₁|
  -- Which follows from: more observations → smaller feasible set

  -- Unfold totalEliminations definition
  unfold totalEliminations

  -- Explicit let bindings
  let nf₁ := ConstraintNF L C π₁
  let nf₂ := ConstraintNF L C π₂

  let init₁ := NormalForm.FeasibleUnder nf₁.bitDeterminations
  let init₂ := NormalForm.FeasibleUnder nf₂.bitDeterminations

  let final₁ := wcExecute L C nf₁.bitDeterminations nf₁.digestMatches init₁
  let final₂ := wcExecute L C nf₂.bitDeterminations nf₂.digestMatches init₂

  -- Goal: |univ| - |final₁.feasible| ≤ |univ| - |final₂.feasible|
  -- Equivalent to: |final₂.feasible| ≤ |final₁.feasible|

  suffices h_card : final₂.feasible.card ≤ final₁.feasible.card by
    -- Arithmetic: (u - a ≤ u - b) follows from (b ≤ a) when both ≤ u
    -- Since final₂.feasible.card ≤ final₁.feasible.card, we get the reverse inequality after subtracting from univ
    let u := (Finset.univ : Finset (CutWorld L C)).card
    have h₁ : final₁.feasible.card ≤ u := Finset.card_le_card (Finset.subset_univ _)
    have h₂ : final₂.feasible.card ≤ u := Finset.card_le_card (Finset.subset_univ _)
    -- omega handles nat subtraction arithmetic
    show u - final₁.feasible.card ≤ u - final₂.feasible.card
    omega

  -- Prove feasible₂ ⊆ feasible₁ (more constraints → fewer worlds)
  suffices h_subset : final₂.feasible ⊆ final₁.feasible by
    exact Finset.card_le_card h_subset

  -- Step 1: Extract constraint subset property from isPrefixOf
  have h_bits_prefix := h_prefix.2.1  -- List.IsPrefix π₁.revealedBits π₂.revealedBits
  have h_configs_prefix := h_prefix.2.2  -- List.IsPrefix π₁.computedConfigs π₂.computedConfigs

  -- Step 2: Show extractConstraints(π₂) ⊇ extractConstraints(π₁)
  have h_constraints_subset : ∀ c ∈ extractConstraints L C π₁, c ∈ extractConstraints L C π₂ := by
    intro c hc
    unfold extractConstraints at hc ⊢
    -- extractConstraints = bits ++ configs ++ synthetics (3 parts)
    rw [List.mem_append, List.mem_append, or_assoc] at hc ⊢
    cases hc with
    | inl h_bit =>
        left
        -- c from bit constraints, use filterMap_prefix_subset
        exact filterMap_prefix_subset _ h_bits_prefix c h_bit
    | inr h_rest =>
        right
        cases h_rest with
        | inl h_config =>
            left
            -- c from config constraints, use filterMap_prefix_subset
            exact filterMap_prefix_subset _ h_configs_prefix c h_config
        | inr h_synth =>
            right
            -- c from synthetic constraints
            -- Synthetic configs depend only on revealedBits, which is a prefix

            -- Step 1: completeAt is prefix-monotone
            have completeAt_mono : ∀ (v : Fin L.dag.n) (h_v : v ∈ C),
                completeAt L C π₁ v h_v → completeAt L C π₂ v h_v := by
              intro v h_v h_complete₁
              unfold completeAt at *
              intro idx
              obtain ⟨bit, h_bit_in, h_bit_node, h_bit_idx⟩ := h_complete₁ idx
              use bit
              constructor
              · exact List.IsPrefix.subset h_bits_prefix bit h_bit_in
              · exact ⟨h_bit_node, h_bit_idx⟩

            -- Step 2: Show c ∈ extractSyntheticConfigs L C π₂
            unfold extractSyntheticConfigs at h_synth ⊢
            rw [List.mem_filterMap] at h_synth ⊢
            obtain ⟨v_synth, h_v_synth_in_list, h_synth_some⟩ := h_synth

            -- Split on v_synth ∈ C in hypothesis
            split at h_synth_some
            case isTrue h_v_synth =>
              -- Split on completeAt π₁ in hypothesis
              split at h_synth_some
              case isTrue h_complete₁ =>
                injection h_synth_some with h_c_eq

                -- Show c ∈ extractSyntheticConfigs L C π₂
                use v_synth, h_v_synth_in_list

                split
                case isTrue h_v_synth' =>
                  have h_complete₂ := completeAt_mono v_synth h_v_synth' h_complete₁
                  split
                  case isTrue h_complete₂' =>
                    -- Goal: ConfigMatch v_synth h_v_synth' (reconstructedCfg ... π₂ ...) = c
                    -- We have: c = ConfigMatch v_synth h_v_synth (reconstructedCfg ... π₁ ...)
                    --
                    -- The issue: reconstructedCfg may differ due to dependent types even though
                    -- the underlying bit values are the same (when revealedBits form a prefix).
                    --
                    -- This requires bit observation determinism (Property 4), which states:
                    -- if the same (node, bitIndex) is observed twice, the values must be equal.
                    --
                    -- Use the hypothesis h_bit_determinism to bridge this gap
                    have h_cfg_eq := h_bit_determinism v_synth h_v_synth h_complete₁ h_complete₂'
                    rw [← h_c_eq, h_cfg_eq]
                  case isFalse => contradiction
                case isFalse => contradiction
              case isFalse => cases h_synth_some
            case isFalse => cases h_synth_some

  -- Step 3: Normalization preserves subset (from NormalForm.lean)
  have h_bits_subset : ∀ b ∈ nf₁.bitDeterminations, b ∈ nf₂.bitDeterminations := by
    show ∀ b ∈ (ConstraintNF L C π₁).bitDeterminations, b ∈ (ConstraintNF L C π₂).bitDeterminations
    unfold ConstraintNF
    exact NormalForm.normalize_bitDeterminations_subset _ _ h_constraints_subset

  have h_digests_subset : ∀ d ∈ nf₁.digestMatches, d ∈ nf₂.digestMatches := by
    show ∀ d ∈ (ConstraintNF L C π₁).digestMatches, d ∈ (ConstraintNF L C π₂).digestMatches
    unfold ConstraintNF
    exact NormalForm.normalize_digestMatches_subset _ _ h_constraints_subset

  -- Step 4: More bit constraints → smaller initial feasible
  have h_init_subset : init₂ ⊆ init₁ := by
    show NormalForm.FeasibleUnder nf₂.bitDeterminations ⊆ NormalForm.FeasibleUnder nf₁.bitDeterminations
    intro ω hω
    -- FeasibleUnder is {ω | (bits.all (fun c => Satisfies ω c)) = true}
    -- hω says ω satisfies all bits in nf₂
    -- Need to show ω satisfies all bits in nf₁
    -- Since nf₁.bits ⊆ nf₂.bits, this follows
    simp [NormalForm.FeasibleUnder] at hω ⊢
    intro c hc
    exact hω c (h_bits_subset c hc)

  -- Step 5: Apply wcExecute contravariance
  -- More digests + smaller initial → smaller final
  show (wcExecute L C nf₂.bitDeterminations nf₂.digestMatches init₂).feasible ⊆
       (wcExecute L C nf₁.bitDeterminations nf₁.digestMatches init₁).feasible
  exact wcExecute_feasible_monotone_contravariant L C
    nf₁.bitDeterminations nf₁.digestMatches nf₂.digestMatches
    init₁ init₂ h_digests_subset h_init_subset

/-! ### WC-1 Protocol Property (W = 1)

**Key Insight**: The WorldCommit protocol forces W = 1 (one world per boundary).

**From world_commit_refutation_excludes_one theorem**:
```lean
theorem world_commit_refutation_excludes_one :
  |Feasible_before| = |Feasible_after| + 1
```

**Why W = 1 (not information-theoretic)**:
- One digest mathematically identifies many wrong configs (2^{R_v} possibilities)
- But protocol forces sequential checking: propose ω*, check, refute, repeat
- Each boundary adds UnitRefute(ω*), which excludes exactly ω* by definition
- **This is computational, not information-theoretic!**

**Proof Strategy** (when connecting to TMToExecutionPrefix):
The property "each boundary refutes exactly 1 world" is captured by the h_wc1
hypothesis in boundaries_equal_refutations_wc1 and refutations_to_time_proven.

When these theorems are applied in TMToExecutionPrefix.lean, h_wc1 is proven by:
1. world_commit_refutation_excludes_one (see WorldCommit.lean) gives W = 1 for protocol steps
2. Showing ExecutionPrefixReal transitions correspond to protocol steps
3. Therefore: boundary + growth → refutation_count increases by exactly 1

This connection is the "bridge" that happens in TMToExecutionPrefix.lean, not here.
-/

/-- **Transitive totalEliminations monotonicity** (proven - not axiom)

    This theorem uses the PROVEN totalEliminations_monotone from SegmentReduction.lean,
    not the FALSE axiom refutationCount_monotone.

    **Proof**: Identical structure to refutationCount_mono_chain, but uses
    totalEliminations_monotone (proven) instead of the false axiom.

    **This enables AIRTIGHT proof chain** without false axioms! -/
theorem totalEliminations_mono_chain
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (states : List (ExecutionPrefixReal L))
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (π : ExecutionPrefixReal L)
    (h_mem : π ∈ states)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ states → π₂ ∈ states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    : totalEliminations L C π ≤ totalEliminations L C (states.getLast h_nonempty) := by
  -- IDENTICAL proof structure to refutationCount_mono_chain
  -- but uses totalEliminations_monotone (proven in SegmentReduction.lean)
  induction states generalizing π with
  | nil => contradiction
  | cons π₀ rest IH =>
      cases rest with
      | nil =>
          have : π = π₀ := by
            cases h_mem with
            | head => rfl
            | tail _ h => cases h
          simp [List.getLast, this]
      | cons π₁ rest' =>
          have h_prefix : isPrefixOf L π₀ π₁ := by
            cases h_chain with | cons_cons h_rel _ => exact h_rel

          have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest') := by
            cases h_chain with | cons_cons _ h_rest => exact h_rest

          have h_tail_nonempty : π₁ :: rest' ≠ [] := by simp

          have h_last_eq : (π₀ :: π₁ :: rest').getLast h_nonempty =
                           (π₁ :: rest').getLast h_tail_nonempty := by
            simp [List.getLast]

          -- Thread bit determinism for tail
          have h_bit_det_tail : ∀ (πₐ πᵦ : ExecutionPrefixReal L),
              πₐ ∈ (π₁ :: rest') → πᵦ ∈ (π₁ :: rest') →
              isPrefixOf L πₐ πᵦ →
              ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
                (h_completeₐ : completeAt L C πₐ v h_v)
                (h_completeᵦ : completeAt L C πᵦ v h_v),
                reconstructedCfg L C πₐ v h_v h_completeₐ =
                reconstructedCfg L C πᵦ v h_v h_completeᵦ := by
            intros πₐ πᵦ h_memₐ h_memᵦ h_pref v h_v h_cₐ h_cᵦ
            exact h_bit_determinism πₐ πᵦ
              (List.mem_cons_of_mem π₀ h_memₐ)
              (List.mem_cons_of_mem π₀ h_memᵦ)
              h_pref v h_v h_cₐ h_cᵦ

          by_cases h_eq : π = π₀
          case pos =>
              have IH_π₁ : totalEliminations L C π₁ ≤
                           totalEliminations L C ((π₁ :: rest').getLast h_tail_nonempty) :=
                IH h_tail_chain h_tail_nonempty π₁ List.mem_cons_self h_bit_det_tail

              have h_mem₀ : π₀ ∈ (π₀ :: π₁ :: rest') := List.mem_cons_self
              have h_mem₁ : π₁ ∈ (π₀ :: π₁ :: rest') := List.mem_cons_of_mem π₀ List.mem_cons_self

              calc totalEliminations L C π
                  = totalEliminations L C π₀ := by rw [h_eq]
                _ ≤ totalEliminations L C π₁ := totalEliminations_monotone L C π₀ π₁ h_prefix
                    (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem₀ h_mem₁ h_prefix v h_v h_c₀ h_c₁)
                _ ≤ totalEliminations L C ((π₁ :: rest').getLast h_tail_nonempty) := IH_π₁
                _ = totalEliminations L C ((π₀ :: π₁ :: rest').getLast h_nonempty) := by rw [←h_last_eq]

          case neg =>
              have h_mem_tail : π ∈ (π₁ :: rest') := by
                cases h_mem with
                | head => contradiction
                | tail _ h => exact h

              have IH_π : totalEliminations L C π ≤
                          totalEliminations L C ((π₁ :: rest').getLast h_tail_nonempty) :=
                IH h_tail_chain h_tail_nonempty π h_mem_tail h_bit_det_tail

              calc totalEliminations L C π
                  ≤ totalEliminations L C ((π₁ :: rest').getLast h_tail_nonempty) := IH_π
                _ = totalEliminations L C ((π₀ :: π₁ :: rest').getLast h_nonempty) := by rw [←h_last_eq]

/-! ### Auxiliary lemma for boundaries ≥ eliminations (Sound Version)

This is the sound version using totalEliminations (proven monotonic),
not refutationCount (which can decrease).

Same structure as the deprecated boundaryCount_ge_refutation_diff_aux, but uses
totalEliminations_monotone (proven) instead of refutationCount_monotone (false).

We use a `mutual...end` block to solve Lean 4 elaboration order issues.
-/

mutual

/-- **Auxiliary lemma for boundaries ≥ eliminations** (enables structural recursion).

    This lemma is separated out to allow Lean 4 to recognize the structural recursion pattern. -/
theorem boundaryCount_ge_eliminations_diff_aux
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (states : List (ExecutionPrefixReal L))
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (h_wc1_elim : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ states → π₂ ∈ states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        totalEliminations L C π₁ < totalEliminations L C π₂ →
        totalEliminations L C π₂ = totalEliminations L C π₁ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ states → π₂ ∈ states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    : boundaryCount.aux L C states ≥
      totalEliminations L C (states.getLast h_nonempty) -
      totalEliminations L C (states.head (List.ne_nil_of_length_pos (List.length_pos_iff.mpr h_nonempty)))
    := by
  -- IDENTICAL structure to boundaryCount_ge_refutation_diff_aux
  -- but uses totalEliminations throughout (proven monotonic)
  match states with
  | [] => contradiction
  | [π₀] =>
      simp [boundaryCount.aux]
  | π₀ :: π₁ :: rest =>
      have h_prefix : isPrefixOf L π₀ π₁ := by
        cases h_chain with | cons_cons h_rel _ => exact h_rel

      have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest) := by
        cases h_chain with | cons_cons _ h_rest => exact h_rest

      have h_tail_nonempty : π₁ :: rest ≠ [] := by simp

      have h_mem₀ : π₀ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_self
      have h_mem₁ : π₁ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_of_mem π₀ List.mem_cons_self

      have h_wc1_tail : ∀ πₐ πᵦ : ExecutionPrefixReal L,
          πₐ ∈ (π₁ :: rest) → πᵦ ∈ (π₁ :: rest) →
          isPrefixOf L πₐ πᵦ →
          SegmentBoundary L C πₐ πᵦ →
          totalEliminations L C πₐ < totalEliminations L C πᵦ →
          totalEliminations L C πᵦ = totalEliminations L C πₐ + 1 := by
        intros πₐ πᵦ h_ma h_mb h_pref h_seg h_grow
        apply h_wc1_elim πₐ πᵦ
        · exact List.mem_cons_of_mem π₀ h_ma
        · exact List.mem_cons_of_mem π₀ h_mb
        · exact h_pref
        · exact h_seg
        · exact h_grow

      have h_bit_det_tail : ∀ (πₐ πᵦ : ExecutionPrefixReal L),
          πₐ ∈ (π₁ :: rest) → πᵦ ∈ (π₁ :: rest) →
          isPrefixOf L πₐ πᵦ →
          ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
            (h_completeₐ : completeAt L C πₐ v h_v)
            (h_completeᵦ : completeAt L C πᵦ v h_v),
            reconstructedCfg L C πₐ v h_v h_completeₐ =
            reconstructedCfg L C πᵦ v h_v h_completeᵦ := by
        intros πₐ πᵦ h_memₐ h_memᵦ h_pref v h_v h_cₐ h_cᵦ
        exact h_bit_determinism πₐ πᵦ
          (List.mem_cons_of_mem π₀ h_memₐ)
          (List.mem_cons_of_mem π₀ h_memᵦ)
          h_pref v h_v h_cₐ h_cᵦ

      have IH := boundaryCount_ge_eliminations_diff_aux L C (π₁ :: rest) h_tail_chain h_tail_nonempty h_wc1_tail h_bit_det_tail

      have h_last_eq : (π₀ :: π₁ :: rest).getLast h_nonempty = (π₁ :: rest).getLast h_tail_nonempty := by
        cases rest with
        | nil => rfl
        | cons _ _ => rfl

      unfold boundaryCount.aux
      by_cases h_boundary : SegmentBoundary L C π₀ π₁

      case pos =>
        simp [h_boundary]
        by_cases h_growth : totalEliminations L C π₀ < totalEliminations L C π₁

        case pos =>
          have h_incr := h_wc1_elim π₀ π₁ h_mem₀ h_mem₁ h_prefix h_boundary h_growth

          have h_mono_π₀_π₁ : totalEliminations L C π₀ ≤ totalEliminations L C π₁ :=
            totalEliminations_monotone L C π₀ π₁ h_prefix
              (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem₀ h_mem₁ h_prefix v h_v h_c₀ h_c₁)
          have h_mono_π₁_last : totalEliminations L C π₁ ≤ totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) :=
            totalEliminations_mono_chain L C (π₁ :: rest) h_tail_chain h_tail_nonempty π₁ List.mem_cons_self h_bit_det_tail
          have h_mono : totalEliminations L C π₀ ≤ totalEliminations L C ((π₀ :: π₁ :: rest).getLast h_nonempty) := by
            rw [h_last_eq]
            exact Nat.le_trans h_mono_π₀_π₁ h_mono_π₁_last

          have h_π₁_eq_head : π₁ = (π₁ :: rest).head (by simp : π₁ :: rest ≠ []) := by rfl
          rw [←h_π₁_eq_head] at IH

          have IH_additive : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                             boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
            omega

          calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
              ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_additive
            _ = boundaryCount.aux L C (π₁ :: rest) + (totalEliminations L C π₀ + 1) := by rw [h_incr]
            _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ + 1 := by omega
            _ = 1 + boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by omega

        case neg =>
          push_neg at h_growth
          have h_mono := totalEliminations_monotone L C π₀ π₁ h_prefix
            (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem₀ h_mem₁ h_prefix v h_v h_c₀ h_c₁)
          have h_eq := Nat.le_antisymm h_growth h_mono

          have h_π₁_eq_head : π₁ = (π₁ :: rest).head (by simp : π₁ :: rest ≠ []) := by rfl
          rw [←h_π₁_eq_head] at IH

          have IH_additive : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                             boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
            omega

          calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
              ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_additive
            _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by rw [h_eq]
            _ ≤ 1 + boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by omega

      case neg =>
        simp [h_boundary]
        -- No boundary means ConstraintNF is same, so totalEliminations is same
        have h_mono := totalEliminations_monotone L C π₀ π₁ h_prefix
          (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem₀ h_mem₁ h_prefix v h_v h_c₀ h_c₁)

        -- If there were growth, there would be a boundary (contrapositive)
        have h_no_growth : ¬(totalEliminations L C π₀ < totalEliminations L C π₁) := by
          intro h_growth
          -- Growth in totalEliminations implies ConstraintNF changed (which is a boundary)
          -- Proof: totalEliminations is determined by ConstraintNF
          -- If ConstraintNF(π₀) = ConstraintNF(π₁), then totalEliminations(π₀) = totalEliminations(π₁)
          -- Contrapositive: If totalEliminations differ, then ConstraintNF differ
          have h_nf_ne : ConstraintNF L C π₀ ≠ ConstraintNF L C π₁ := by
            intro h_eq
            -- If NFs are equal, totalEliminations are equal
            unfold totalEliminations at h_growth
            simp only [h_eq] at h_growth
            -- But h_growth says they're different - contradiction
            omega
          -- But h_nf_ne is exactly SegmentBoundary
          unfold SegmentBoundary at h_boundary
          exact h_boundary h_nf_ne

        push_neg at h_no_growth
        have h_eq := Nat.le_antisymm h_no_growth h_mono

        have h_π₁_eq_head : π₁ = (π₁ :: rest).head (by simp : π₁ :: rest ≠ []) := by rfl
        rw [←h_π₁_eq_head] at IH

        have IH_additive : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                           boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
          omega

        calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
            ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_additive
          _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by rw [h_eq]

/-- **Auxiliary lemma: time increases through boundary chain**.

    This helper proves that time accumulates across all boundaries in the history.
    Uses structural recursion on the state list. -/
theorem time_ge_boundary_count_aux
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (states : List (ExecutionPrefixReal L))
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ states → π₂ ∈ states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : (states.getLast h_nonempty).time ≥ (states.head (List.ne_nil_of_length_pos (List.length_pos_iff.mpr h_nonempty))).time +
      boundaryCount.aux L C states := by
  -- Structural recursion
  match states with
  | [] => contradiction
  | [π₀] =>
      simp [List.getLast, boundaryCount.aux, List.head]
  | π₀ :: π₁ :: rest =>
      have h_prefix : isPrefixOf L π₀ π₁ := by
        cases h_chain with | cons_cons h_rel _ => exact h_rel

      have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest) := by
        cases h_chain with | cons_cons _ h_rest => exact h_rest

      have h_tail_nonempty : π₁ :: rest ≠ [] := by simp

      -- Last element equality
      have h_last : (π₀ :: π₁ :: rest).getLast h_nonempty = (π₁ :: rest).getLast h_tail_nonempty := by
        cases rest with | nil => rfl | cons _ _ => rfl

      -- h_time_boundary for tail
      have h_time_tail : ∀ πₐ πᵦ : ExecutionPrefixReal L,
          πₐ ∈ (π₁ :: rest) → πᵦ ∈ (π₁ :: rest) →
          isPrefixOf L πₐ πᵦ →
          SegmentBoundary L C πₐ πᵦ →
          πᵦ.time ≥ πₐ.time + 1 := by
        intros πₐ πᵦ h_ma h_mb h_pref h_seg
        apply h_time_boundary πₐ πᵦ
        · exact List.mem_cons_of_mem π₀ h_ma
        · exact List.mem_cons_of_mem π₀ h_mb
        · exact h_pref
        · exact h_seg

      -- Recursive call
      have IH := time_ge_boundary_count_aux L C (π₁ :: rest) h_tail_chain h_tail_nonempty h_time_tail

      -- Membership
      have h_mem₀ : π₀ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_self
      have h_mem₁ : π₁ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_of_mem π₀ List.mem_cons_self

      -- Unfold aux and split on boundary
      unfold boundaryCount.aux
      by_cases h_boundary : SegmentBoundary L C π₀ π₁

      case pos =>
        simp [h_boundary]
        -- There's a boundary: time increases by at least 1
        have h_time_incr := h_time_boundary π₀ π₁ h_mem₀ h_mem₁ h_prefix h_boundary

        -- Time monotonicity from π₁ to final
        have h_time_mono : π₁.time ≤ ((π₁ :: rest).getLast h_tail_nonempty).time := by
          exact time_mono_chain (π₁ :: rest) h_tail_chain h_tail_nonempty π₁ List.mem_cons_self

        calc ((π₀ :: π₁ :: rest).getLast h_nonempty).time
            = ((π₁ :: rest).getLast h_tail_nonempty).time := by rw [h_last]
          _ ≥ π₁.time + boundaryCount.aux L C (π₁ :: rest) := IH
          _ ≥ (π₀.time + 1) + boundaryCount.aux L C (π₁ :: rest) := by omega
          _ = π₀.time + (1 + boundaryCount.aux L C (π₁ :: rest)) := by omega

      case neg =>
        simp [h_boundary]
        -- No boundary: just use monotonicity
        have h_time_mono₀₁ : π₀.time ≤ π₁.time := isPrefixOf_time_mono h_prefix

        calc ((π₀ :: π₁ :: rest).getLast h_nonempty).time
            = ((π₁ :: rest).getLast h_tail_nonempty).time := by rw [h_last]
          _ ≥ π₁.time + boundaryCount.aux L C (π₁ :: rest) := IH
          _ ≥ π₀.time + boundaryCount.aux L C (π₁ :: rest) := by omega

theorem boundaries_equal_eliminations_wc1
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (h_wc1_elim : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        totalEliminations L C π₁ < totalEliminations L C π₂ →
        totalEliminations L C π₂ = totalEliminations L C π₁ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    : boundaryCount L C hist ≥
      totalEliminations L C hist.final - totalEliminations L C hist.initial := by
  unfold boundaryCount ExecutionHistory.final ExecutionHistory.initial
  exact boundaryCount_ge_eliminations_diff_aux L C hist.states hist.h_chain hist.h_nonempty h_wc1_elim h_bit_determinism

theorem time_from_boundaries
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : hist.final.time ≥ hist.initial.time + boundaryCount L C hist := by
  unfold ExecutionHistory.final ExecutionHistory.initial boundaryCount
  exact time_ge_boundary_count_aux L C hist.states hist.h_chain hist.h_nonempty h_time_boundary

-- ### Adjacent-Pair Variants (require WC-1 only for consecutive states)
--
-- These variants reflect how boundary counting structurally calls the WC-1 step:
-- it only ever inspects consecutive pairs (π₀, π₁) at the head of the list or in
-- the tail during recursion. Therefore, it suffices to assume the WC-1 increment
-- property for adjacent pairs only.

/-- Auxiliary: boundaries ≥ eliminations (adjacent-pair assumption). -/
theorem boundaryCount_ge_eliminations_diff_aux_adjacent
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (full_states : List (ExecutionPrefixReal L))  -- Original full list
    (states : List (ExecutionPrefixReal L))
    (h_suffix : states <:+ full_states)  -- states is suffix of full_states
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (h_wc1_head : ∀ (l : List (ExecutionPrefixReal L)) {π₀ π₁ rest},
        l = π₀ :: π₁ :: rest →
        l <:+ full_states →  -- Suffix witness available in callback
        isPrefixOf L π₀ π₁ →  -- Prefix relationship from chain
        SegmentBoundary L C π₀ π₁ →
        totalEliminations L C π₀ < totalEliminations L C π₁ →
        totalEliminations L C π₁ = totalEliminations L C π₀ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ full_states → π₂ ∈ full_states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    : boundaryCount.aux L C states ≥
      totalEliminations L C (states.getLast h_nonempty) -
      totalEliminations L C (states.head (List.ne_nil_of_length_pos (List.length_pos_iff.mpr h_nonempty))) := by
  -- Structural recursion on states
  cases states with
  | nil => contradiction
  | cons π₀ states_t =>
      cases states_t with
      | nil =>
          -- Single element: no boundaries; difference is zero
          simp [boundaryCount.aux]
      | cons π₁ rest =>
          -- Extract chain pieces
          have h_prefix : isPrefixOf L π₀ π₁ := by
            cases h_chain with | cons_cons h_rel _ => exact h_rel

          have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest) := by
            cases h_chain with | cons_cons _ h_rest => exact h_rest

          have h_tail_nonempty : π₁ :: rest ≠ [] := by simp

          -- Suffix witness for tail: (π₁ :: rest) <:+ full_states
          have h_tail_suffix : (π₁ :: rest) <:+ full_states := by
            -- states = π₀ :: π₁ :: rest, so tail = π₁ :: rest
            -- Since states <:+ full_states, we have (π₁ :: rest) <:+ full_states
            exact suffix_tail h_suffix

          -- IH over the tail
          have IH := boundaryCount_ge_eliminations_diff_aux_adjacent L C full_states (π₁ :: rest) h_tail_suffix h_tail_chain h_tail_nonempty
            (by
              intro l πa πb r h_eq h_suf h_pref h_seg h_grow
              have : l = πa :: πb :: r := h_eq
              exact @h_wc1_head l πa πb r this h_suf h_pref h_seg h_grow)
            h_bit_determinism

          have h_last_eq : (π₀ :: π₁ :: rest).getLast h_nonempty = (π₁ :: rest).getLast h_tail_nonempty := by
            cases rest with
            | nil => rfl
            | cons _ _ => rfl

          -- Suffix witness for current position
          have h_current_suffix : (π₀ :: π₁ :: rest) <:+ full_states := by
            -- states = π₀ :: π₁ :: rest from pattern match
            -- states <:+ full_states by assumption
            exact h_suffix

          -- Membership proofs for bit determinism
          have h_mem_π₀ : π₀ ∈ full_states :=
            List.IsSuffix.subset h_current_suffix List.mem_cons_self

          have h_mem_π₁ : π₁ ∈ full_states :=
            List.IsSuffix.subset h_current_suffix (List.mem_cons_of_mem π₀ List.mem_cons_self)

          -- Split on boundary at head
          unfold boundaryCount.aux
          by_cases h_boundary : SegmentBoundary L C π₀ π₁
          · simp [h_boundary]
            -- Split on growth at head
            by_cases h_growth : totalEliminations L C π₀ < totalEliminations L C π₁
            · -- WC-1 increment at head (adjacent pair assumption)
              have h_incr := h_wc1_head (π₀ :: π₁ :: rest) rfl h_current_suffix h_prefix h_boundary h_growth

              -- Monotonic steps identical to the non-adjacent proof
              have h_mono_π₀_π₁ : totalEliminations L C π₀ ≤ totalEliminations L C π₁ :=
                totalEliminations_monotone L C π₀ π₁ h_prefix
                  (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem_π₀ h_mem_π₁ h_prefix v h_v h_c₀ h_c₁)

              -- For mono_chain, need bit determinism for (π₁ :: rest) sublist
              have h_bit_det_tail : ∀ (πₐ πᵦ : ExecutionPrefixReal L),
                  πₐ ∈ (π₁ :: rest) → πᵦ ∈ (π₁ :: rest) →
                  isPrefixOf L πₐ πᵦ →
                  ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
                    (h_cₐ : completeAt L C πₐ v h_v)
                    (h_cᵦ : completeAt L C πᵦ v h_v),
                    reconstructedCfg L C πₐ v h_v h_cₐ =
                    reconstructedCfg L C πᵦ v h_v h_cᵦ := by
                intros πₐ πᵦ h_memₐ h_memᵦ h_pref v h_v h_cₐ h_cᵦ
                have h_memₐ_full : πₐ ∈ full_states :=
                  List.IsSuffix.subset h_tail_suffix h_memₐ
                have h_memᵦ_full : πᵦ ∈ full_states :=
                  List.IsSuffix.subset h_tail_suffix h_memᵦ
                exact h_bit_determinism πₐ πᵦ h_memₐ_full h_memᵦ_full h_pref v h_v h_cₐ h_cᵦ

              have h_mono_π₁_last : totalEliminations L C π₁ ≤ totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) :=
                totalEliminations_mono_chain L C (π₁ :: rest) h_tail_chain h_tail_nonempty π₁ List.mem_cons_self h_bit_det_tail

              have IH_add : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                            boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
                -- Use IH and the fact that (π₁ :: rest).head = π₁
                simp only [List.head_cons] at IH
                omega

              calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
                  ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_add
                _ = boundaryCount.aux L C (π₁ :: rest) + (totalEliminations L C π₀ + 1) := by rw [h_incr]
                _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ + 1 := by omega
                _ = 1 + boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by omega

            · -- No growth at head
              push_neg at h_growth
              have h_mono := totalEliminations_monotone L C π₀ π₁ h_prefix
                (fun v h_v h_c₀ h_c₁ => h_bit_determinism π₀ π₁ h_mem_π₀ h_mem_π₁ h_prefix v h_v h_c₀ h_c₁)
              have h_eq := Nat.le_antisymm h_growth h_mono

              have IH_add : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                            boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
                -- Use IH and the fact that (π₁ :: rest).head = π₁
                simp only [List.head_cons] at IH
                omega

              calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
                  ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_add
                _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by rw [h_eq]
                _ ≤ 1 + boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by omega

          · -- No boundary at head
            simp [h_boundary]
            -- In no-boundary case, totalEliminations cannot change (no new eliminations)
            have h_eq : totalEliminations L C π₀ = totalEliminations L C π₁ := by
              -- ¬SegmentBoundary means ConstraintNF didn't change
              have h_nf_eq : ConstraintNF L C π₀ = ConstraintNF L C π₁ := by
                simp [SegmentBoundary] at h_boundary
                exact h_boundary
              -- totalEliminations is defined in terms of ConstraintNF, so equal NFs → equal eliminations
              simp only [totalEliminations, h_nf_eq]
            have IH_add : totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty) ≤
                          boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := by
              simp only [List.head_cons] at IH
              omega
            calc totalEliminations L C ((π₁ :: rest).getLast h_tail_nonempty)
                ≤ boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₁ := IH_add
              _ = boundaryCount.aux L C (π₁ :: rest) + totalEliminations L C π₀ := by rw [← h_eq]

/-- Boundaries ≥ eliminations (adjacent-pair version). -/
theorem boundaries_equal_eliminations_wc1_adjacent
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (h_wc1_head : ∀ (l : List (ExecutionPrefixReal L)) {π₀ π₁ rest},
        l = π₀ :: π₁ :: rest →
        l <:+ hist.states →  -- Add suffix witness
        isPrefixOf L π₀ π₁ →  -- Prefix relationship
        SegmentBoundary L C π₀ π₁ →
        totalEliminations L C π₀ < totalEliminations L C π₁ →
        totalEliminations L C π₁ = totalEliminations L C π₀ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    : boundaryCount L C hist ≥
      totalEliminations L C hist.final - totalEliminations L C hist.initial := by
  unfold boundaryCount ExecutionHistory.final ExecutionHistory.initial
  exact boundaryCount_ge_eliminations_diff_aux_adjacent L C hist.states hist.states (suffix_refl hist.states) hist.h_chain hist.h_nonempty
    (by
      intro l π₀ π₁ rest h_eq h_suf h_pref h_seg h_grow
      exact h_wc1_head l h_eq h_suf h_pref h_seg h_grow)
    h_bit_determinism

/-- Eliminations → time (adjacent-pair version). -/
theorem eliminations_to_time_proven_adjacent
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (R : Nat)
    (h_eliminations : totalEliminations L C hist.final ≥ R)
    (h_initial_zero : totalEliminations L C hist.initial = 0)
    (h_initial_time_zero : hist.initial.time = 0)
    (h_wc1_head : ∀ (l : List (ExecutionPrefixReal L)) {π₀ π₁ rest},
        l = π₀ :: π₁ :: rest →
        l <:+ hist.states →  -- Suffix witness
        isPrefixOf L π₀ π₁ →  -- Prefix relationship
        SegmentBoundary L C π₀ π₁ →
        totalEliminations L C π₀ < totalEliminations L C π₁ →
        totalEliminations L C π₁ = totalEliminations L C π₀ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : hist.final.time ≥ R := by
  -- Step 1: Boundaries from eliminations (adjacent-pair WC-1)
  have h_boundaries : boundaryCount L C hist ≥ R := by
    have h_bound := boundaries_equal_eliminations_wc1_adjacent L C hist
      (by
        intro l π₀ π₁ rest h_eq h_suf h_pref h_seg h_grow
        exact h_wc1_head l h_eq h_suf h_pref h_seg h_grow)
      h_bit_determinism
    calc boundaryCount L C hist
        ≥ totalEliminations L C hist.final - totalEliminations L C hist.initial := h_bound
      _ = totalEliminations L C hist.final - 0 := by rw [h_initial_zero]
      _ = totalEliminations L C hist.final := Nat.sub_zero _
      _ ≥ R := h_eliminations

  -- Step 2: Time from boundaries
  have h_time_bound : hist.final.time ≥ hist.initial.time + boundaryCount L C hist :=
    time_from_boundaries L C hist h_time_boundary

  calc hist.final.time
      ≥ hist.initial.time + boundaryCount L C hist := h_time_bound
    _ = 0 + boundaryCount L C hist := by rw [h_initial_time_zero]
    _ = boundaryCount L C hist := Nat.zero_add _
    _ ≥ R := h_boundaries

/-- **Main theorem**: eliminations → time (no false axioms)

    Eliminates false axiom by using totalEliminations (proven monotonic)
    instead of refutationCount (false monotonicity).

    See documentation below (after mutual block) for full details. -/
theorem eliminations_to_time_proven
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (R : Nat)
    (h_eliminations : totalEliminations L C hist.final ≥ R)
    (h_initial_zero : totalEliminations L C hist.initial = 0)
    (h_initial_time_zero : hist.initial.time = 0)
    (h_wc1_elim : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        totalEliminations L C π₁ < totalEliminations L C π₂ →
        totalEliminations L C π₂ = totalEliminations L C π₁ + 1)
    (h_bit_determinism : ∀ (π₁ π₂ : ExecutionPrefixReal L),
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        ∀ (v : Fin L.dag.n) (h_v : v ∈ C)
          (h_complete₁ : completeAt L C π₁ v h_v)
          (h_complete₂ : completeAt L C π₂ v h_v),
          reconstructedCfg L C π₁ v h_v h_complete₁ =
          reconstructedCfg L C π₂ v h_v h_complete₂)
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        SegmentBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : hist.final.time ≥ R := by
  -- Step 1: Bound boundaries from eliminations (W = 1 from WC-1)
  have h_boundaries : boundaryCount L C hist ≥ R := by
    have h_bound := boundaries_equal_eliminations_wc1 L C hist h_wc1_elim h_bit_determinism
    calc boundaryCount L C hist
        ≥ totalEliminations L C hist.final - totalEliminations L C hist.initial := h_bound
      _ = totalEliminations L C hist.final - 0 := by rw [h_initial_zero]
      _ = totalEliminations L C hist.final := Nat.sub_zero _
      _ ≥ R := h_eliminations

  -- Step 2: Time from boundaries
  have h_time_bound : hist.final.time ≥ hist.initial.time + boundaryCount L C hist :=
    time_from_boundaries L C hist h_time_boundary

  calc hist.final.time
      ≥ hist.initial.time + boundaryCount L C hist := h_time_bound
    _ = 0 + boundaryCount L C hist := by rw [h_initial_time_zero]
    _ = boundaryCount L C hist := Nat.zero_add _
    _ ≥ R := h_boundaries

end  -- mutual

/-! ### Main Theorem: eliminations_to_time_proven

**This theorem replaces refutations_to_time_proven with a sound version
that does not rely on the false axiom `refutationCount_monotone`.**

**Statement**: eliminations ≥ R → time ≥ R (with W = 1 from WC-1)

**Proof chain** (all steps proven, no false axioms):
```
eliminations ≥ R                             [hypothesis]
    ↓ (boundaries_equal_eliminations_wc1: W = 1 from WC-1)
boundaries ≥ R                               [this file, proven]
    ↓ (time_from_boundaries: each boundary = 1 time step)
time ≥ initial_time + R                      [this file, proven]
```

Zero false axioms, zero admits.

**Key difference from refutations_to_time_proven**: Uses totalEliminations
(proven monotonic in SegmentReduction.lean) instead of refutationCount
(which relies on false axiom refutationCount_monotone).

**NOTE**: The theorem is defined inside the mutual block above (see above)
to avoid Lean 4 elaboration ordering issues.
-/

/-! ## Usage Note for TMToExecutionPrefix.lean

To use this theorem to eliminate the axiom:

1. Build ExecutionHistory from TM execution
2. Prove h_wc1 from WorldCommit protocol properties:
   - WorldCommit.world_commit_refutation_excludes_one (see WorldCommit.lean)
   - Shows each protocol step refutes exactly 1 world (W = 1)
3. Prove h_time_boundary from observation model:
   - Each segment boundary corresponds to an observation
   - Each observation takes at least one TM step
   - Therefore: boundary → time increases by ≥ 1
4. Apply refutations_to_time_proven
5. Conclusion: time ≥ refutations
-/

/-! ## Digest Boundary Theorems (for W=1 Proof)

**PURPOSE**: Time accumulation for digest boundaries only.

**CLONE of**: time_ge_boundary_count_aux + time_from_boundaries

**DIFFERENCE**: Uses DigestBoundary instead of SegmentBoundary predicate.

**WHY NEEDED**: Bit boundaries can eliminate many worlds, but digest boundaries
correspond to WC-1 refutations (exactly 1 world per boundary when growth occurs).
-/

/-- **Auxiliary lemma: time increases through DIGEST boundary chain**.

    **Clone of**: time_ge_boundary_count_aux (see above)

    **Proof**: Identical structure - structural recursion on states list.
-/
theorem time_ge_digest_boundary_count_aux
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (states : List (ExecutionPrefixReal L))
    (h_chain : states.IsChain (isPrefixOf L))
    (h_nonempty : states ≠ [])
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ states → π₂ ∈ states →
        isPrefixOf L π₁ π₂ →
        DigestBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : (states.getLast h_nonempty).time ≥ (states.head (List.ne_nil_of_length_pos (List.length_pos_iff.mpr h_nonempty))).time +
      digestBoundaryCount.aux L C states := by
  match states with
  | [] => contradiction
  | [π₀] =>
      simp [List.getLast, digestBoundaryCount.aux, List.head]
  | π₀ :: π₁ :: rest =>
      have h_prefix : isPrefixOf L π₀ π₁ := by
        cases h_chain with | cons_cons h_rel _ => exact h_rel

      have h_tail_chain : List.IsChain (isPrefixOf L) (π₁ :: rest) := by
        cases h_chain with | cons_cons _ h_rest => exact h_rest

      have h_tail_nonempty : π₁ :: rest ≠ [] := by simp

      have h_last : (π₀ :: π₁ :: rest).getLast h_nonempty = (π₁ :: rest).getLast h_tail_nonempty := by
        cases rest with | nil => rfl | cons _ _ => rfl

      have h_time_tail : ∀ πₐ πᵦ : ExecutionPrefixReal L,
          πₐ ∈ (π₁ :: rest) → πᵦ ∈ (π₁ :: rest) →
          isPrefixOf L πₐ πᵦ →
          DigestBoundary L C πₐ πᵦ →
          πᵦ.time ≥ πₐ.time + 1 := by
        intros πₐ πᵦ h_memₐ h_memᵦ h_pre h_bound
        apply h_time_boundary
        · exact List.mem_cons_of_mem π₀ h_memₐ
        · exact List.mem_cons_of_mem π₀ h_memᵦ
        · exact h_pre
        · exact h_bound

      have IH := time_ge_digest_boundary_count_aux L C (π₁ :: rest) h_tail_chain h_tail_nonempty h_time_tail

      have h_mem₀ : π₀ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_self
      have h_mem₁ : π₁ ∈ (π₀ :: π₁ :: rest) := List.mem_cons_of_mem π₀ List.mem_cons_self

      unfold digestBoundaryCount.aux
      by_cases h_boundary : DigestBoundary L C π₀ π₁
      · simp [h_boundary]
        have h_time_incr := h_time_boundary π₀ π₁ h_mem₀ h_mem₁ h_prefix h_boundary
        calc ((π₀ :: π₁ :: rest).getLast h_nonempty).time
            = ((π₁ :: rest).getLast h_tail_nonempty).time := by rw [h_last]
          _ ≥ π₁.time + digestBoundaryCount.aux L C (π₁ :: rest) := IH
          _ ≥ (π₀.time + 1) + digestBoundaryCount.aux L C (π₁ :: rest) := by omega
          _ = π₀.time + (1 + digestBoundaryCount.aux L C (π₁ :: rest)) := by omega
      · simp [h_boundary]
        calc ((π₀ :: π₁ :: rest).getLast h_nonempty).time
            = ((π₁ :: rest).getLast h_tail_nonempty).time := by rw [h_last]
          _ ≥ π₁.time + digestBoundaryCount.aux L C (π₁ :: rest) := IH
          _ ≥ π₀.time + digestBoundaryCount.aux L C (π₁ :: rest) := by
              have : π₀.time ≤ π₁.time := h_prefix.1
              omega

/-- **Wrapper: Time from digest boundaries**.

    **Clone of**: time_from_boundaries
-/
theorem time_from_digest_boundaries
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (hist : ExecutionHistory L)
    (h_time_boundary : ∀ π₁ π₂ : ExecutionPrefixReal L,
        π₁ ∈ hist.states → π₂ ∈ hist.states →
        isPrefixOf L π₁ π₂ →
        DigestBoundary L C π₁ π₂ →
        π₂.time ≥ π₁.time + 1)
    : hist.final.time ≥ hist.initial.time + digestBoundaryCount L C hist := by
  unfold ExecutionHistory.final ExecutionHistory.initial digestBoundaryCount
  exact time_ge_digest_boundary_count_aux L C hist.states hist.h_chain hist.h_nonempty h_time_boundary

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms ExecutionHistory
#print axioms growth_implies_boundary_exists
#print axioms totalEliminations_monotone
#print axioms world_commit_refutation_excludes_one
#print axioms totalEliminations_mono_chain
#print axioms boundaries_equal_eliminations_wc1
#print axioms time_from_boundaries
#print axioms eliminations_to_time_proven_adjacent
#print axioms time_from_digest_boundaries

end LStar.StructuralOWF.Foundations
