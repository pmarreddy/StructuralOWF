import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction
import Layer3_InformationBounds.ConstraintSystem.NormalForm
import Layer3_InformationBounds.SegmentReduction.SegmentBoundaries
import Layer3_InformationBounds.Keyedness.PlantedInstanceConsistency
import Layer3_InformationBounds.Keyedness.AcceptanceUniqueness
import Layer3_InformationBounds.SegmentReduction.SegmentReduction

/-! ## PlantedFGDiversity: FG Diversity Bounds via Residual Formula

**Main Lemmas**: Cardinality bounds for feasible worlds under bit-determination at singleton cuts.

**Key Bounds**:
1. **fg_singleton_bits_card_le_pow_residual**: |FeasibleUnder| ≤ 2^{R_v - revealedBits}
2. **fg_singleton_bits_card_le_two_of_residual_le_one**: residual ≤ 1 → |FeasibleUnder| ≤ 2
3. **fg_singleton_bit_constraints_bound_configs**: Wrapper (backward compat)

**Residual Formula**: Bound depends on unrevealed bits (R_v - revealedBits), not planted structure.

**Examples**:
```
All R_v bits revealed: residual = 0 → exactly 1 world (fully determined)
R_v - 1 bits revealed: residual = 1 → at most 2 worlds
```

**Follows from**: SegmentReduction's `bits_only_cardinality_exact`

**Trust Boundary**: Proven theorems (no axioms).

**Paper**: Appendix C "FG Diversity Bounds", §7 "Residual Formula"

See Layer3_InformationBounds/Layer3_README.md for residual formula and segment reduction context.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

/-- **Planted world satisfies bit-determination constraints** (with consistency hypothesis).

For planted instances, the world constructed via `worldFromWitness` satisfies
all bit-determination constraints derived from an execution prefix, PROVIDED that
the prefix's observations are consistent with the planted world.

**Key insight**: This lemma needs a consistency hypothesis! The planted world ω
uses r.assignment, but π's observations could come from ANY execution. We must
require that π's revealedBits match what ω would produce.

**Consistency hypothesis**: For every revealed bit in π, the planted world's
bit value at that coordinate matches the observed value.

**Proof strategy**:
1. Unfold FeasibleUnder (ω satisfies all constraints in bitDeterminations)
2. For each BitDetermination constraint c in bitDeterminations:
   - c comes from some RevealedBit rb in π.revealedBits (via extractBitConstraints)
   - c says: extractBit (ω.assignment v h_in) bitIndex = rb.value
   - By h_consistent: ω's bit at (rb.node, rb.bitIndex) = rb.value
   - Therefore c.Satisfies ω ✓
-/
lemma worldFromWitness_satisfies_bit_constraints
    {L : LStarInstanceFG}
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_L_eq : L = plant_n n φ r h_nvars h_dgLen)
    (h_wf : WellFormedRandomness φ r)
    (C : Finset (Fin L.dag.n))
    (w : Witness)
    (π : ExecutionPrefixReal L)
    -- PLANTED PROPERTY: planted instances have no revealed bits
    (h_revealedBits_empty : π.revealedBits = [])
    -- POSITIVE EMERGENCE: Required by extractConstraints_two_part_for_planted
    (h_positive_R : ∀ v ∈ C, 0 < L.R v)
    -- CONSISTENCY HYPOTHESIS (robust, minimal):
    -- "π's observations match what worldFromWitness produces"
    (h_consistent : ∀ (rb : RevealedBit L),
        rb ∈ π.revealedBits →
        rb.node ∈ C →
        let ω := worldFromWitness L w n φ r h_nvars h_dgLen h_L_eq h_wf C
        ∃ (h_in : rb.node ∈ C) (h_idx : rb.bitIndex < L.R rb.node),
          CutConstraint.extractBit (ω.assignment rb.node h_in) ⟨rb.bitIndex, h_idx⟩ = rb.value)
    : let ω := worldFromWitness L w n φ r h_nvars h_dgLen h_L_eq h_wf C
      let nf := ConstraintNF L C π
      ω ∈ NormalForm.FeasibleUnder nf.bitDeterminations := by
  intro ω nf
  -- Goal: ω ∈ FeasibleUnder nf.bitDeterminations
  -- This means: ω satisfies all bit constraints in nf.bitDeterminations

  unfold NormalForm.FeasibleUnder
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.all_eq_true]
  intro c hc

  -- c ∈ nf.bitDeterminations is a BitDetermination constraint
  -- Need to show: c.Satisfies ω

  -- Strategy: Show c came from some RevealedBit rb, then use h_consistent

  -- c is in bitDeterminations = (extractConstraints.filter isBitDetermination).dedup.toFinset.toList
  -- So c is in extractConstraints.filter isBitDetermination
  have h_c_in_filtered : c ∈ (extractConstraints L C π).filter NormalForm.isBitDetermination := by
    -- nf.bitDeterminations comes from normalize (extractConstraints L C π)
    -- which filters for isBitDetermination, dedups, toFinset, toList
    -- The chain: extractConstraints → filter → dedup → toFinset → toList
    -- So membership in toList implies membership in filter
    have h_in_toFinset : c ∈ ((extractConstraints L C π).filter NormalForm.isBitDetermination).dedup.toFinset := by
      -- hc: c ∈ nf.bitDeterminations
      -- nf = ConstraintNF L C π, so nf.bitDeterminations = (ConstraintNF L C π).bitDeterminations
      -- which is the toList of the toFinset
      exact Finset.mem_toList.mp hc
    have h_in_dedup : c ∈ ((extractConstraints L C π).filter NormalForm.isBitDetermination).dedup :=
      List.mem_toFinset.mp h_in_toFinset
    exact List.mem_dedup.mp h_in_dedup

  -- c is in extractConstraints
  have h_c_in_extracted : c ∈ extractConstraints L C π := by
    exact List.mem_of_mem_filter h_c_in_filtered

  -- extractConstraints = extractBitConstraints ++ extractConfigConstraints (for planted instances)
  -- c is a BitDetermination, so it's from extractBitConstraints
  have h_c_from_bits : c ∈ extractBitConstraints L C π.revealedBits := by
    -- Use planted property (revealedBits = []) to simplify extractConstraints
    rw [extractConstraints_two_part_for_planted L C π h_revealedBits_empty h_positive_R] at h_c_in_extracted
    rw [List.mem_append] at h_c_in_extracted
    cases h_c_in_extracted with
    | inl h => exact h  -- c from extractBitConstraints ✓
    | inr h =>
      -- c from extractConfigConstraints
      -- But c is BitDetermination, extractConfigConstraints only produces ConfigMatch!
      -- This is a contradiction
      exfalso
      unfold extractConfigConstraints at h
      -- extractConfigConstraints = computedConfigs.filterMap (... ConfigMatch ...)
      simp only [List.mem_filterMap] at h
      obtain ⟨cfg, _, h_some⟩ := h
      -- h_some: some (ConfigMatch ...) = some c
      split at h_some <;> try contradiction
      -- After split: h_some says ConfigMatch = c
      injection h_some with h_eq
      -- But c is BitDetermination (from h_c_in_filtered)
      have h_is_bit : NormalForm.isBitDetermination c = true := by
        exact List.mem_filter.mp h_c_in_filtered |>.2
      -- And ConfigMatch has isBitDetermination = false
      rw [← h_eq] at h_is_bit
      unfold NormalForm.isBitDetermination at h_is_bit
      -- ConfigMatch case evaluates to false
      contradiction

  -- Now c came from extractBitConstraints
  -- extractBitConstraints maps RevealedBit → BitDetermination
  unfold extractBitConstraints at h_c_from_bits
  simp only [List.mem_filterMap] at h_c_from_bits
  obtain ⟨rb, h_rb_in, h_some⟩ := h_c_from_bits

  -- Unfold the filterMap logic
  split at h_some <;> try contradiction
  next h_in =>
    split at h_some <;> try contradiction
    next h_idx =>
      -- h_some: some (BitDetermination rb.node h_in ⟨rb.bitIndex, h_idx⟩ rb.value) = some c
      injection h_some with h_eq

      -- So c = BitDetermination rb.node h_in ⟨rb.bitIndex, h_idx⟩ rb.value
      rw [← h_eq]

      -- Goal: (BitDetermination rb.node h_in ⟨rb.bitIndex, h_idx⟩ rb.value).Satisfies ω
      -- Satisfies uses decide for decidability
      unfold CutConstraint.Satisfies

      -- Goal: decide (CutConstraint.extractBit (ω.assignment rb.node h_in) ⟨rb.bitIndex, h_idx⟩ = rb.value) = true

      -- Apply h_consistent!
      have h_cons := h_consistent rb h_rb_in h_in
      obtain ⟨h_in', h_idx', h_bit_eq⟩ := h_cons

      -- h_bit_eq: CutConstraint.extractBit (ω.assignment rb.node h_in') ⟨rb.bitIndex, h_idx'⟩ = rb.value
      -- Need to show: decide (... h_in ...) = true

      -- First show the inner equality
      have h_extract_eq : CutConstraint.extractBit (ω.assignment rb.node h_in) ⟨rb.bitIndex, h_idx⟩ = rb.value := by
        -- Use proof irrelevance to rewrite h_in → h_in', h_idx → h_idx'
        have : ω.assignment rb.node h_in = ω.assignment rb.node h_in' := rfl  -- proof irrelevance
        have : (⟨rb.bitIndex, h_idx⟩ : Fin (L.R rb.node)) = ⟨rb.bitIndex, h_idx'⟩ := rfl  -- val equality
        simp only [this]
        exact h_bit_eq

      -- Then convert to decide = true
      simp [h_extract_eq]

/-- **General residual-based bound for singleton cuts**.

For singleton C = {v}, the number of feasible worlds under bit determinations
is bounded by 2^(residual), where residual = R_v - (revealed bits at v).

**Proof strategy**: Use SegmentReduction's exact formula:
- FeasibleUnder ⊆ BitsOnlyWorlds (bit constraints subset)
- |BitsOnlyWorlds| = 2^(ρ - s) where ρ = Σ R_v, s = revealed count
- For singleton, this simplifies to 2^(R_v - revealedBitsPerNode)

**Infrastructure**: Relies on SegmentReduction.bits_only_cardinality_exact -/
lemma fg_singleton_bits_card_le_pow_residual
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_C_eq : C = {v})
    (π : ExecutionPrefixReal L)
    (h_wf : WellFormedPrefix L π)
    : (NormalForm.FeasibleUnder (ConstraintNF L C π).bitDeterminations).card
      ≤ 2^(L.R v - revealedBitsPerNode L C π ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩) := by
  -- Abbreviation
  let nf := ConstraintNF L C π

  -- Step 1: FeasibleUnder nf.bitDeterminations = BitsOnlyWorlds L C π
  -- This is because bitDeterminations come from extractBitConstraints via dedup
  -- and dedup preserves FeasibleUnder semantics
  have h_eq : NormalForm.FeasibleUnder nf.bitDeterminations = BitsOnlyWorlds L C π := by
    -- Strategy: Use extensionality - show both sets contain the same worlds
    unfold BitsOnlyWorlds
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, NormalForm.FeasibleUnder]
    constructor
    · -- Direction 1: nf.bitDeterminations → extractBitConstraints
      intro h_nf
      rw [List.all_eq_true] at h_nf ⊢
      intro b hb
      -- b ∈ extractBitConstraints, need to show ω satisfies b
      -- Key: b is in the toFinset of extractBitConstraints, and toFinset/dedup preserve membership
      -- So b (or equal constraint) is in nf.bitDeterminations

      -- Since extractConstraints = extractBitConstraints ++ extractConfigConstraints ++ extractSyntheticConfigs,
      -- and b ∈ extractBitConstraints, we have b ∈ extractConstraints
      have h_b_in_extracted : b ∈ extractConstraints L C π := by
        unfold extractConstraints
        apply List.mem_append_left
        apply List.mem_append_left
        exact hb

      -- b is a BitDetermination (extractBitConstraints only produces BitDetermination)
      have h_b_is_bit : NormalForm.isBitDetermination b = true := by
        -- extractBitConstraints only produces BitDetermination constructors
        unfold extractBitConstraints at hb
        simp only [List.mem_filterMap] at hb
        obtain ⟨rb, _, h_some⟩ := hb
        -- Case split on the if conditions in filterMap
        split at h_some <;> try contradiction
        split at h_some <;> try contradiction
        -- h_some : some (...BitDetermination...) = some b
        injection h_some with h_eq
        rw [← h_eq]
        rfl

      -- Therefore b ∈ (extractConstraints.filter isBitDetermination)
      have h_b_filtered : b ∈ (extractConstraints L C π).filter NormalForm.isBitDetermination := by
        exact List.mem_filter.mpr ⟨h_b_in_extracted, h_b_is_bit⟩

      -- And b ∈ the dedup/toFinset/toList transformation
      have h_b_in_nf : b ∈ (ConstraintNF L C π).bitDeterminations := by
        unfold ConstraintNF NormalForm.normalize
        simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup]
        exact h_b_filtered

      -- ω satisfies all nf.bitDeterminations, so it satisfies b
      exact h_nf b h_b_in_nf
    · -- Direction 2: extractBitConstraints → nf.bitDeterminations
      intro h_extract
      rw [List.all_eq_true] at h_extract ⊢
      intro b hb
      -- b ∈ nf.bitDeterminations, need to show ω satisfies b
      -- Inline bit_in_nf_from_extract_bits (private lemma)
      -- Unwrap: nf.bitDeterminations = (extractConstraints.filter isBit).dedup.toFinset.toList
      have h_b_in_extract : b ∈ extractBitConstraints L C π.revealedBits := by
        -- Expand nf and unfold definitions
        show b ∈ extractBitConstraints L C π.revealedBits
        have hb' : b ∈ (ConstraintNF L C π).bitDeterminations := hb
        unfold ConstraintNF NormalForm.normalize at hb'
        simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup] at hb'
        -- hb' : b ∈ (extractConstraints L C π).filter NormalForm.isBitDetermination
        have h_filtered := List.mem_filter.mp hb'
        -- b ∈ extractConstraints and isBitDetermination b
        have h_b_in_extracted := h_filtered.1
        -- extractConstraints = extractBitConstraints ++ extractConfigConstraints ++ extractSyntheticConfigs
        unfold extractConstraints at h_b_in_extracted
        simp only [List.mem_append] at h_b_in_extracted
        cases h_b_in_extracted with
        | inl h_in_bits_or_rest =>
            cases h_in_bits_or_rest with
            | inl h_in_bits => exact h_in_bits  -- b ∈ extractBitConstraints ✓
            | inr h_in_configs =>
                -- b ∈ extractConfigConstraints, but these are ConfigMatch, not BitDetermination
                -- This contradicts h_filtered.2 : isBitDetermination b = true
                exfalso
                unfold extractConfigConstraints at h_in_configs
                simp only [List.mem_filterMap] at h_in_configs
                obtain ⟨⟨v, cfg⟩, _, h_some⟩ := h_in_configs
                split at h_some <;> try contradiction
                injection h_some with h_eq
                rw [← h_eq] at h_filtered
                unfold NormalForm.isBitDetermination at h_filtered
                cases h_filtered.2
        | inr h_in_synthetic =>
            -- b ∈ extractSyntheticConfigs, but these are ConfigMatch, not BitDetermination
            exfalso
            unfold extractSyntheticConfigs at h_in_synthetic
            simp only [List.mem_filterMap] at h_in_synthetic
            obtain ⟨v, _, h_some⟩ := h_in_synthetic
            split at h_some <;> try contradiction
            split at h_some <;> try contradiction
            injection h_some with h_eq
            rw [← h_eq] at h_filtered
            unfold NormalForm.isBitDetermination at h_filtered
            cases h_filtered.2
      -- ω satisfies all extractBitConstraints, so it satisfies b
      exact h_extract b h_b_in_extract

  -- Step 2: Cardinality equality
  have h_card_eq : (NormalForm.FeasibleUnder nf.bitDeterminations).card
                   = (BitsOnlyWorlds L C π).card :=
    by rw [h_eq]

  -- Step 3: Use exact cardinality formula for BitsOnlyWorlds
  have h_exact : (BitsOnlyWorlds L C π).card =
                 2^(C.sum (fun w => L.R w) - effectiveRevealedCount L C π) :=
    bits_only_cardinality_exact L C π h_wf

  -- Step 4: Simplify for singleton C = {v}
  -- C.sum R = R_v for singleton
  have h_sum_singleton : C.sum (fun w => L.R w) = L.R v := by
    rw [h_C_eq]
    simp [Finset.sum_singleton]

  -- effectiveRevealedCount = revealedBitsPerNode for singleton
  have h_revealed_singleton : effectiveRevealedCount L C π =
                               revealedBitsPerNode L C π ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ := by
    -- For singleton C = {v}, all coords in C are from v
    -- So distinctRevealedCoords (all in C) = distinctRevealedCoords (filtered to v)
    unfold effectiveRevealedCount revealedBitsPerNode
    congr 1
    -- Show: filtering by node = v is identity when C = {v}
    ext ⟨n, i⟩
    simp only [Finset.mem_filter]
    constructor
    · intro h
      -- If ⟨n, i⟩ ∈ distinctRevealedCoords, then n ∈ C = {v}, so n = v
      refine ⟨h, ?_⟩
      unfold distinctRevealedCoords at h
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at h
      obtain ⟨rb, ⟨_, h_node_in_C⟩, h_eq⟩ := h
      -- Extract node equality from dependent pair equality
      have h_node : rb.node = n := by cases h_eq; rfl
      -- rb.node ∈ C (from decide equality)
      have h_rb_in_C : rb.node ∈ C := by simpa using h_node_in_C
      -- C = {v}, so rb.node = v
      rw [h_C_eq] at h_rb_in_C
      have : rb.node = v := Finset.mem_singleton.mp h_rb_in_C
      -- Therefore n = v
      rw [← h_node]
      exact this
    · intro ⟨h, _⟩
      exact h

  -- Combine everything (using equality, which implies ≤)
  calc (NormalForm.FeasibleUnder nf.bitDeterminations).card
      = (BitsOnlyWorlds L C π).card := h_card_eq
    _ = 2^(C.sum (fun w => L.R w) - effectiveRevealedCount L C π) := h_exact
    _ = 2^(L.R v - effectiveRevealedCount L C π) := by rw [h_sum_singleton]
    _ = 2^(L.R v - revealedBitsPerNode L C π ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩) := by rw [h_revealed_singleton]
    _ ≤ 2^(L.R v - revealedBitsPerNode L C π ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩) := le_refl _

/-- **Corollary: When residual ≤ 1, at most 2 worlds are feasible**.

This is the "all but one bit revealed" case that gives the ≤ 2 bound.

**When this holds**:
- Residual = 0 (all bits revealed): exactly 1 world
- Residual = 1 (all but one bit revealed): at most 2 worlds -/
lemma fg_singleton_bits_card_le_two_of_residual_le_one
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_C_eq : C = {v})
    (π : ExecutionPrefixReal L)
    (h_wf : WellFormedPrefix L π)
    (h_residual_le_one : L.R v - revealedBitsPerNode L C π
                          ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ ≤ 1)
    : (NormalForm.FeasibleUnder (ConstraintNF L C π).bitDeterminations).card ≤ 2 := by
  have h_gen := fg_singleton_bits_card_le_pow_residual L v C h_C_eq π h_wf
  calc (NormalForm.FeasibleUnder (ConstraintNF L C π).bitDeterminations).card
      ≤ 2^(L.R v - revealedBitsPerNode L C π ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩)
        := h_gen
    _ ≤ 2^1 := by apply Nat.pow_le_pow_right; omega; exact h_residual_le_one
    _ = 2 := by norm_num

/-- **Backward-compatible wrapper with explicit residual hypothesis**.

Original name preserved for existing call sites. Now requires:
- WellFormedPrefix (for SegmentReduction theorems)
- Residual ≤ 1 hypothesis (all but one bit revealed)

**Note**: Planted structure (h_planted) is not actually needed for the bound itself,
only for proving residual ≤ 1 at specific call sites. -/
lemma fg_singleton_bit_constraints_bound_configs
    (L : LStarInstanceFG)
    (h_planted : IsPlantedWithWellFormedRandomness L)
    (v : Fin L.dag.n)
    (C : Finset (Fin L.dag.n))
    (h_C_eq : C = {v})
    (bit_constraints : List (CutConstraint L C))
    (h_from_observation : ∃ π, bit_constraints = (ConstraintNF L C π).bitDeterminations)
    (h_wf : ∃ π, bit_constraints = (ConstraintNF L C π).bitDeterminations ∧ WellFormedPrefix L π)
    (h_residual_le_one : ∃ π, bit_constraints = (ConstraintNF L C π).bitDeterminations ∧
                          L.R v - revealedBitsPerNode L C π
                            ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ ≤ 1)
    : (NormalForm.FeasibleUnder bit_constraints).card ≤ 2 := by
  -- Use π'' directly since it has both WellFormedPrefix and residual ≤ 1
  -- We need to show h_wf and h_residual_le_one give us the same π (or compatible π's)

  -- Extract witnesses
  obtain ⟨π', h_eq', h_wf'⟩ := h_wf
  obtain ⟨π'', h_eq'', h_residual⟩ := h_residual_le_one

  -- Key insight: Both π' and π'' produce bit_constraints
  -- So (ConstraintNF L C π').bitDeterminations = bit_constraints = (ConstraintNF L C π'').bitDeterminations

  -- Rewrite goal to use bit_constraints = (ConstraintNF L C π'').bitDeterminations
  rw [h_eq'']

  -- Now we can directly apply the corollary with π''!
  -- But wait - we need WellFormedPrefix for π'', not just the residual

  -- Check if π'' has WellFormedPrefix
  -- Problem: h_residual_le_one doesn't give us WellFormedPrefix for π''!

  -- So we're back to needing the transfer...
  -- But maybe we can show: if bit_constraints come from some WellFormed prefix π',
  -- then any π'' producing the same constraints must also reveal the same info

  -- CLEAN SIMPLIFICATION: Use π' directly!
  --
  -- Key insight: We don't actually need the full bijection proof!
  -- We just need to transfer the residual bound from π'' to π'.
  --
  -- Strategy:
  -- 1. Use cardinality equality: |FeasibleUnder π'| = |FeasibleUnder π''|
  -- 2. |FeasibleUnder π''| ≤ 2 (by residual bound on π'')
  -- 3. Therefore |FeasibleUnder π'| ≤ 2

  -- Step 1: Equal bitDeterminations via transitivity
  have h_bitDets_eq :
      (ConstraintNF L C π').bitDeterminations = (ConstraintNF L C π'').bitDeterminations := by
    calc (ConstraintNF L C π').bitDeterminations
        = bit_constraints := h_eq'.symm
      _ = (ConstraintNF L C π'').bitDeterminations := h_eq''

  -- Step 2: Equal bitDeterminations → equal FeasibleUnder sets
  have h_feasible_eq :
      NormalForm.FeasibleUnder (ConstraintNF L C π').bitDeterminations =
      NormalForm.FeasibleUnder (ConstraintNF L C π'').bitDeterminations := by
    -- Equal constraint lists → equal filtered worlds
    rw [h_bitDets_eq]

  -- Step 3: Equal sets → equal cardinalities
  have h_card_eq :
      (NormalForm.FeasibleUnder (ConstraintNF L C π').bitDeterminations).card =
      (NormalForm.FeasibleUnder (ConstraintNF L C π'').bitDeterminations).card := by
    rw [h_feasible_eq]

  -- Step 3: Bound on π' using transferred residual
  have h_bound_π' :
      (NormalForm.FeasibleUnder (ConstraintNF L C π').bitDeterminations).card ≤ 2 := by
    -- Apply the corollary to π' (which HAS WellFormedPrefix)
    -- Transfer the residual bound from π'' to π' via revealed equality

    -- BIJECTION PROOF: revealedBitsPerNode π' = revealedBitsPerNode π''
    --
    -- Strategy:
    -- 1. bitDeterminations come from revealedBits via extractBitConstraints
    -- 2. extractBitConstraints maps (node, bitIndex, value) → BitDetermination
    -- 3. revealedBitsPerNode counts distinct (node, bitIndex) pairs where node = v
    -- 4. Equal bitDeterminations (after dedup) → equal (node, bitIndex) pairs
    -- 5. For singleton C = {v}, all revealed bits have node = v
    -- 6. Therefore revealedBitsPerNode counts are equal

    have h_revealed_eq :
        revealedBitsPerNode L C π' ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ =
        revealedBitsPerNode L C π'' ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ := by
      unfold revealedBitsPerNode

      -- Both count |{(node, idx) ∈ distinctRevealedCoords | node = v}|
      -- Need to show: distinctRevealedCoords from π' and π'' are equal (when filtered by v)

      -- For singleton C = {v}, ALL revealed coords have node = v (only node in C)
      -- So this simplifies to: |distinctRevealedCoords π'| = |distinctRevealedCoords π''|

      -- Key: BitDeterminations uniquely identify coordinates
      -- Equal BitDeterminations → equal coordinate sets

      -- Since C = {v}, the filter is actually identity (all coords are for node v)
      congr 1

      -- Need: distinctRevealedCoords L C π' = distinctRevealedCoords L C π''
      -- This follows from equal bitDeterminations

      -- Both create coordinates from revealedBits: (rb.node, rb.bitIndex)
      -- bitDeterminations are deduped by (node, bitIndex) pairs
      -- So equal bitDeterminations (as sets) → equal revealed coordinates (as sets)

      -- BIJECTION PROOF: BitDeterminations encode coordinates uniquely
      -- Equal bitDeterminations → equal revealed (node, bitIndex) coordinate sets
      ext ⟨n, i⟩

      -- Characterization: (n,i) is revealed iff ∃ value v such that BitDetermination exists
      -- Key: BitDeterminations uniquely identify coordinates via (node, bitIndex), regardless of value

      constructor
      · -- Direction: π' → π'' (if coordinate in π', then in π'')
        intro h_in_π'
        -- h_in_π': (n,i) ∈ distinctRevealedCoords L C π'

        -- Work with unfolded form directly
        unfold distinctRevealedCoords at h_in_π' ⊢

        -- After unfold, h_in_π' has form: (n,i) ∈ {x ∈ (map ...).toFinset | filter by v}
        -- Extract from Finset.filter
        simp only [Finset.mem_filter] at h_in_π' ⊢
        obtain ⟨h_in_map, h_n_eq_v⟩ := h_in_π'

        -- Extract from the map toFinset
        rw [List.mem_toFinset, List.mem_map] at h_in_map
        obtain ⟨rb', h_rb'_in_filter, h_pair_eq⟩ := h_in_map

        -- Extract from the filter
        rw [List.mem_filter] at h_rb'_in_filter
        obtain ⟨h_rb', h_node_in_C'⟩ := h_rb'_in_filter
        simp at h_node_in_C'

        -- Extract node and index equalities from pair equality
        -- h_pair_eq : ⟨rb'.node, ⟨rb'.bitIndex, _⟩⟩ = ⟨n, i⟩
        have h_node : rb'.node = n := by
          cases h_pair_eq
          rfl
        have h_idx : rb'.bitIndex = i.val := by
          cases h_pair_eq
          rfl

        -- We need to show ∃ rb'' ∈ π''.revealedBits with rb''.node = n, rb''.bitIndex = i, rb''.node ∈ C
        -- This follows from bitDeterminations equality:
        -- - rb' (if valid) creates BitDetermination n h ⟨i, h_idx⟩ rb'.value in π'.bitDeterminations
        -- - By h_bitDets_eq, this BitDetermination is also in π''.bitDeterminations
        -- - BitDeterminations come from extractBitConstraints on π''.revealedBits
        -- - Therefore ∃ rb'' with matching (n, i)

        -- Use decidable membership to construct the witness
        -- The key: if BitDetermination exists in π'', it came from some RevealedBit
        by_cases h_valid : n ∈ C ∧ i < L.R n
        · -- Valid case: rb' creates a BitDetermination
          obtain ⟨h_n_in_C, h_i_lt⟩ := h_valid

          -- The BitDetermination from rb' is in π'.bitDeterminations
          have h_bitDet_in_π' : ∃ val, CutConstraint.BitDetermination n h_n_in_C ⟨i, h_i_lt⟩ val ∈ (ConstraintNF L C π').bitDeterminations := by
            use rb'.value
            -- Show rb' generates this BitDetermination via extractBitConstraints
            unfold ConstraintNF NormalForm.normalize
            simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup, List.mem_filter]
            constructor
            · -- In extractConstraints
              unfold extractConstraints
              rw [List.mem_append, List.mem_append]
              left; left  -- In extractBitConstraints (first of 3 parts)
              unfold extractBitConstraints
              simp only [List.mem_filterMap]
              use rb'
              constructor
              · exact h_rb'
              · -- Show filterMap produces the BitDetermination
                -- extractBitConstraints checks: if rb.node ∈ C then if rb.bitIndex < L.R rb.node then some (BitDetermination ...)
                -- We have rb' with rb'.node = n (h_node), rb'.bitIndex = i (h_idx)
                -- Convert to decide form
                have h_rb'_in_C : rb'.node ∈ C := by rw [h_node]; exact h_n_in_C
                have h_rb'_idx_lt : rb'.bitIndex < L.R rb'.node := by rw [h_node, h_idx]; exact h_i_lt
                -- Now show the filterMap condition evaluates to the BitDetermination
                rw [dif_pos h_rb'_in_C, dif_pos h_rb'_idx_lt]
                -- Use subst for node, rw for bitIndex (to handle coercions)
                subst h_node
                -- Goal: some (BitDetermination n _ ⟨rb'.bitIndex, _⟩ _) = some (BitDetermination n _ ⟨i, _⟩ _)
                congr 1
                congr 1
                apply Fin.ext
                simp
                exact h_idx
            · -- Is BitDetermination
              rfl

          -- By h_bitDets_eq, it's also in π''.bitDeterminations
          obtain ⟨val, h_bitDet_in_π'_val⟩ := h_bitDet_in_π'
          -- Transfer from π' to π'' using h_bitDets_eq
          rw [h_bitDets_eq] at h_bitDet_in_π'_val

          -- Now unwrap to extract rb'' from π''.revealedBits
          -- h_bitDet_in_π'_val: BitDetermination n h_n_in_C ⟨i, h_i_lt⟩ val ∈ (ConstraintNF L C π'').bitDeterminations
          unfold ConstraintNF NormalForm.normalize at h_bitDet_in_π'_val
          simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup, List.mem_filter] at h_bitDet_in_π'_val
          unfold extractConstraints at h_bitDet_in_π'_val
          rw [List.mem_append, List.mem_append] at h_bitDet_in_π'_val

          cases h_bitDet_in_π'_val.1 with
          | inl h_in_bits_or_rest =>
              cases h_in_bits_or_rest with
              | inl h_in_bits =>
                  -- BitDetermination comes from extractBitConstraints on π''.revealedBits
                  unfold extractBitConstraints at h_in_bits
                  simp only [List.mem_filterMap] at h_in_bits
                  obtain ⟨rb'', h_rb'', h_some⟩ := h_in_bits

                  -- Extract rb''.node and rb''.bitIndex from the filterMap
                  split at h_some <;> try contradiction
                  next h_n_in_C'' =>
                    split at h_some <;> try contradiction
                    next h_i_lt'' =>
                      injection h_some with h_eq

                      -- Extract equalities (rb''.node = n and rb''.bitIndex = i)
                      have h_node_rb'' : rb''.node = n := by
                        -- Use congrArg to extract the node field from BitDetermination equality
                        have h_node := congrArg (fun c => match c with
                          | CutConstraint.BitDetermination node _ _ _ => node
                          | _ => rb''.node) h_eq
                        exact h_node
                      have h_idx_rb'' : rb''.bitIndex = i.val := by
                        -- Extract bitIndex field from BitDetermination equality
                        -- First substitute h_node_rb'' to align the dependent types
                        subst h_node_rb''
                        -- Now both have type Fin (L.R n), so we can use congrArg
                        have h_idx := congrArg (fun c => match c with
                          | CutConstraint.BitDetermination _ _ bitIndex _ => bitIndex.val
                          | _ => rb''.bitIndex) h_eq
                        exact h_idx

                      -- Construct the witness for goal: (n, i) ∈ distinctRevealedCoords L C π''
                      constructor
                      · -- Show (n, i) in the mapped coords
                        rw [List.mem_toFinset, List.mem_map]
                        use rb''
                        constructor
                        · -- rb'' in filtered revealedBits
                          rw [List.mem_filter]
                          constructor
                          · exact h_rb''
                          · simp only [decide_eq_true_eq]; exact h_n_in_C''
                        · -- pair equality: ⟨rb''.node, ⟨rb''.bitIndex, _⟩⟩ = ⟨n, i⟩
                          subst h_node_rb''
                          congr 1
                          apply Fin.ext
                          simp
                          exact h_idx_rb''
                      · -- Show n = v (from singleton C = {v})
                        have h_n_in_C : n ∈ C := h_n_in_C
                        rw [h_C_eq] at h_n_in_C
                        exact Finset.mem_singleton.mp h_n_in_C
              | inr h_in_configs =>
                  -- BitDetermination from extractConfigConstraints - contradiction
                  exfalso
                  unfold extractConfigConstraints at h_in_configs
                  simp only [List.mem_filterMap] at h_in_configs
                  obtain ⟨⟨_, _⟩, _, h_some⟩ := h_in_configs
                  split at h_some <;> try contradiction
                  injection h_some with h_eq
                  rw [← h_eq] at h_bitDet_in_π'_val
                  exact absurd h_bitDet_in_π'_val.2 (by unfold NormalForm.isBitDetermination; contradiction)
          | inr h_in_synthetic =>
              -- BitDetermination from extractSyntheticConfigs - contradiction
              exfalso
              unfold extractSyntheticConfigs at h_in_synthetic
              simp only [List.mem_filterMap] at h_in_synthetic
              obtain ⟨v, _, h_some⟩ := h_in_synthetic
              split at h_some <;> try contradiction
              split at h_some <;> try contradiction
              injection h_some with h_eq
              rw [← h_eq] at h_bitDet_in_π'_val
              exact absurd h_bitDet_in_π'_val.2 (by unfold NormalForm.isBitDetermination; contradiction)
        · -- Invalid case: contradiction (h_in_π' says n ∈ C and i < L.R n)
          exfalso
          push_neg at h_valid
          -- h_valid : n ∈ C → L.R n ≤ i (negation of n ∈ C ∧ i < L.R n)
          have h_n_in_C : n ∈ C := by rw [← h_node]; exact h_node_in_C'
          have h_ge : L.R n ≤ i := h_valid h_n_in_C
          -- But i < L.R n (from i : Fin (L.R n))
          have h_lt : i.val < L.R n := i.isLt
          omega

      · -- Direction: π'' → π' (symmetric - proof by swapping π' and π'')
        intro h_in_π''
        -- h_in_π'': (n,i) ∈ distinctRevealedCoords L C π''

        -- Work with unfolded form directly
        unfold distinctRevealedCoords at h_in_π'' ⊢

        -- Extract from Finset.filter
        simp only [Finset.mem_filter] at h_in_π'' ⊢
        obtain ⟨h_in_map, h_n_eq_v⟩ := h_in_π''

        -- Extract from the map toFinset
        rw [List.mem_toFinset, List.mem_map] at h_in_map
        obtain ⟨rb'', h_rb''_in_filter, h_pair_eq⟩ := h_in_map

        -- Extract from the filter
        rw [List.mem_filter] at h_rb''_in_filter
        obtain ⟨h_rb'', h_node_in_C''⟩ := h_rb''_in_filter
        simp at h_node_in_C''

        -- Extract node and index equalities from pair equality
        -- h_pair_eq : ⟨rb''.node, ⟨rb''.bitIndex, _⟩⟩ = ⟨n, i⟩
        have h_node : rb''.node = n := by
          cases h_pair_eq
          rfl
        have h_idx : rb''.bitIndex = i.val := by
          cases h_pair_eq
          rfl

        by_cases h_valid : n ∈ C ∧ i < L.R n
        · obtain ⟨h_n_in_C, h_i_lt⟩ := h_valid

          have h_bitDet_in_π'' : ∃ val, CutConstraint.BitDetermination n h_n_in_C ⟨i, h_i_lt⟩ val ∈ (ConstraintNF L C π'').bitDeterminations := by
            use rb''.value
            unfold ConstraintNF NormalForm.normalize
            simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup, List.mem_filter]
            constructor
            · unfold extractConstraints
              rw [List.mem_append, List.mem_append]
              left; left
              unfold extractBitConstraints
              simp only [List.mem_filterMap]
              use rb''
              constructor
              · exact h_rb''
              · -- Show filterMap produces the BitDetermination
                have h_rb''_in_C : rb''.node ∈ C := by rw [h_node]; exact h_n_in_C
                have h_rb''_idx_lt : rb''.bitIndex < L.R rb''.node := by rw [h_node, h_idx]; exact h_i_lt
                rw [dif_pos h_rb''_in_C, dif_pos h_rb''_idx_lt]
                -- Use subst for node, rw for bitIndex (to handle coercions)
                subst h_node
                -- Goal: some (BitDetermination n _ ⟨rb''.bitIndex, _⟩ _) = some (BitDetermination n _ ⟨i, _⟩ _)
                congr 1
                congr 1
                apply Fin.ext
                simp
                exact h_idx
            · rfl

          obtain ⟨val, h_bitDet_in_π''_val⟩ := h_bitDet_in_π''
          rw [← h_bitDets_eq] at h_bitDet_in_π''_val  -- π'' → π'

          unfold ConstraintNF NormalForm.normalize at h_bitDet_in_π''_val
          simp only [Finset.mem_toList, List.mem_toFinset, List.mem_dedup, List.mem_filter] at h_bitDet_in_π''_val
          unfold extractConstraints at h_bitDet_in_π''_val
          rw [List.mem_append, List.mem_append] at h_bitDet_in_π''_val
          cases h_bitDet_in_π''_val.1 with
          | inl h_in_bits_or_rest =>
              cases h_in_bits_or_rest with
              | inl h_in_bits =>
                  unfold extractBitConstraints at h_in_bits
                  simp only [List.mem_filterMap] at h_in_bits
                  obtain ⟨rb', h_rb', h_some⟩ := h_in_bits

                  split at h_some <;> try contradiction
                  next h_n_in_C' =>
                    split at h_some <;> try contradiction
                    next h_i_lt' =>
                      injection h_some with h_eq
                      -- h_eq: BitDetermination rb'.node h_n_in_C' ⟨rb'.bitIndex, h_i_lt'⟩ rb'.value =
                      --       BitDetermination n h_n_in_C ⟨i, h_i_lt⟩ val
                      -- This implies rb'.node = n and rb'.bitIndex = i
                      -- Extract node and bitIndex equalities from BitDetermination equality
                      -- Extract node and bitIndex equalities from BitDetermination constructor equality
                      have h_node_rb' : rb'.node = n := by
                        -- Use congrArg to extract the node field from BitDetermination equality
                        have h_node := congrArg (fun c => match c with
                          | CutConstraint.BitDetermination node _ _ _ => node
                          | _ => rb'.node) h_eq
                        exact h_node
                      have h_idx_rb' : rb'.bitIndex = i.val := by
                        -- Extract bitIndex field from BitDetermination equality
                        -- First substitute h_node_rb' to align the dependent types
                        subst h_node_rb'
                        -- Now both have type Fin (L.R n), so we can use congrArg
                        have h_idx := congrArg (fun c => match c with
                          | CutConstraint.BitDetermination _ _ bitIndex _ => bitIndex.val
                          | _ => rb'.bitIndex) h_eq
                        exact h_idx

                      -- Construct the witness for goal (already unfolded)
                      constructor
                      · -- Show (n, i) in the mapped coords
                        rw [List.mem_toFinset, List.mem_map]
                        use rb'
                        constructor
                        · -- rb' in filtered revealedBits
                          rw [List.mem_filter]
                          constructor
                          · exact h_rb'
                          · simp only [decide_eq_true_eq]; exact h_n_in_C'
                        · -- pair equality
                          -- Goal: ⟨rb'.node, ⟨rb'.bitIndex, _⟩⟩ = ⟨n, i⟩
                          -- Use h_node_rb' : rb'.node = n and h_idx_rb' : rb'.bitIndex = i.val
                          subst h_node_rb'
                          -- Now goal: ⟨n, ⟨rb'.bitIndex, _⟩⟩ = ⟨n, i⟩
                          congr 1
                          -- Goal: ⟨rb'.bitIndex, _⟩ = i
                          ext
                          exact h_idx_rb'
                      · -- Show n = v (from singleton C = {v})
                        -- h_n_in_C' : rb'.node ∈ C, h_node_rb' : rb'.node = n
                        have h_n_in_C : n ∈ C := by rw [← h_node_rb']; exact h_n_in_C'
                        rw [h_C_eq] at h_n_in_C
                        exact Finset.mem_singleton.mp h_n_in_C
              | inr h_in_configs =>
                  exfalso
                  unfold extractConfigConstraints at h_in_configs
                  simp only [List.mem_filterMap] at h_in_configs
                  obtain ⟨⟨_, _⟩, _, h_some⟩ := h_in_configs
                  split at h_some <;> try contradiction
                  injection h_some with h_eq
                  rw [← h_eq] at h_bitDet_in_π''_val
                  exact absurd h_bitDet_in_π''_val.2 (by unfold NormalForm.isBitDetermination; contradiction)
          | inr h_in_synthetic =>
              exfalso
              unfold extractSyntheticConfigs at h_in_synthetic
              simp only [List.mem_filterMap] at h_in_synthetic
              obtain ⟨v, _, h_some⟩ := h_in_synthetic
              split at h_some <;> try contradiction
              split at h_some <;> try contradiction
              injection h_some with h_eq
              rw [← h_eq] at h_bitDet_in_π''_val
              exact absurd h_bitDet_in_π''_val.2 (by unfold NormalForm.isBitDetermination; contradiction)
        · exfalso
          push_neg at h_valid
          -- h_valid : n ∈ C → L.R n ≤ i (negation of n ∈ C ∧ i < L.R n)
          have h_n_in_C : n ∈ C := by rw [← h_node]; exact h_node_in_C''
          have h_ge : L.R n ≤ i := h_valid h_n_in_C
          -- But i < L.R n (from i : Fin (L.R n))
          have h_lt : i.val < L.R n := i.isLt
          omega

    -- Now we have revealedBitsPerNode π' = revealedBitsPerNode π''
    -- So residual for π' = residual for π''
    have h_residual_π' : L.R v - revealedBitsPerNode L C π' ⟨v, by rw [h_C_eq]; exact Finset.mem_singleton_self v⟩ ≤ 1 := by
      rw [h_revealed_eq]
      exact h_residual

    -- Apply the corollary with π' (which has WellFormedPrefix)
    exact fg_singleton_bits_card_le_two_of_residual_le_one L v C h_C_eq π' h_wf' h_residual_π'

  -- Step 4: Transfer bound from π' to goal (which is already rewritten to π'' in this file)
  -- Mathematical content: |FeasibleUnder π''| = |FeasibleUnder π'| (h_card_eq)
  -- And |FeasibleUnder π'| ≤ 2 (h_bound_π')
  -- Therefore |FeasibleUnder π''| ≤ 2
  calc (NormalForm.FeasibleUnder (ConstraintNF L C π'').bitDeterminations).card
      = (NormalForm.FeasibleUnder (ConstraintNF L C π').bitDeterminations).card := h_card_eq.symm
    _ ≤ 2 := h_bound_π'

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms worldFromWitness_satisfies_bit_constraints
#print axioms fg_singleton_bits_card_le_pow_residual
#print axioms fg_singleton_bits_card_le_two_of_residual_le_one
#print axioms fg_singleton_bit_constraints_bound_configs

end LStar.StructuralOWF.Foundations

