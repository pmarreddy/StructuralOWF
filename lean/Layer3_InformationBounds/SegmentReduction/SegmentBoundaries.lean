import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction
import Layer3_InformationBounds.ConstraintSystem.NormalForm
import Mathlib.Data.List.Basic

/-! ## SegmentBoundaries: Detect Segment Boundaries via ConstraintNF

**Purpose**: Track when normalized constraints change → segment boundaries.

**Core idea**: ConstraintNF equality detects information gain.
- NF(π₁) = NF(π₂) → same segment (no new info)
- NF(π₁) ≠ NF(π₂) → boundary (algorithm learned)

**Key definitions**:
- ConstraintNF: Canonical representation via normalize(extractConstraints)
- SegmentBoundary: NF changed between execution points
- DigestBoundary: Digest constraints changed (refinement for WC-1 proof)

**Minimal version**: Avoids universe constraints by deferring full partition algorithm.

**Trust boundary**: 2 axiom audits - digestBoundary_implies_segmentBoundary, bitDeterminations_unchanged_when_only_configs_change

See Layer3_InformationBounds/Layer3_README.md §Segment Reduction.
-/

namespace LStar.StructuralOWF.Foundations

open Classical NormalForm

/-! ## Constraint NF (Canonical Representation)

**DEFINITION**: The normalized form of constraints at a given execution point.

**Why "Constraint NF" not "ConstraintDigest"**:
- Paper uses ConstraintDigest_C (see above) with hashing
- We use structural canonical NormalForm (no hash needed)
- Achieves same goal: detect when constraints change
-/

/-- **Constraint Normal Form**: Canonical representation of current knowledge.

    **Computation**:
    ```
    ConstraintNF(π) = normalize(extractConstraints(π, C))
    ```

    **Properties**:
    - Deterministic: same π → same NF (by normalize_unique)
    - Conservative: NF represents at most what π contains (by normalize_conservative)
    - Canonical: equality is structural, no hashing

    **Usage**: Two snapshots π₁, π₂ have same NF ⟺ they represent same information
    (modulo redundancy/ordering).

    **Example**:
    ```
    π₁: revealedBits = [(v=5, i=2, b=1)]
    π₂: revealedBits = [(v=5, i=2, b=1), (v=5, i=2, b=1)]  -- duplicate!

    ConstraintNF(π₁) = ConstraintNF(π₂)  -- dedup removes redundancy
    ```
-/
noncomputable def ConstraintNF (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L) : NormalForm L C :=
  normalize (extractConstraints L C π)

/-! ## Segment Boundary Detection

**DEFINITION**: A boundary occurs when ConstraintNF changes.

**Intuition**: If NF is the same, algorithm is still exploring within the same
information state. When NF changes, algorithm has learned something new → boundary!

**Why this is correct** (from paper's CDT-1'):
"No unbacked consequences: if ConstraintDigest_C unchanged and no new designated
reads, then feasible worlds unchanged."

Contrapositive: If feasible worlds changed, then either ConstraintDigest_C changed
OR new designated read occurred. Both are captured by ConstraintNF change.
-/

/-- **Segment boundary**: ConstraintNF changed between two execution points.

    **Definition**: π₁ and π₂ are at a segment boundary iff their constraint
    normal forms differ.

    **Interpretation**:
    - SegmentBoundary π₁ π₂ → algorithm learned new info between π₁ and π₂
    - ¬SegmentBoundary π₁ π₂ → same segment (NF unchanged)

    **Note**: This is a *local* definition (between two snapshots).
    Full segment partition algorithm deferred.

    **Example**:
    ```
    π₁: revealedBits = [(v=5, i=2, b=1)]
    π₂: revealedBits = [(v=5, i=2, b=1), (v=7, i=0, b=0)]

    SegmentBoundary π₁ π₂ = true  -- π₂ has extra bit, NF changed
    ```
-/
def SegmentBoundary (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L) : Prop :=
  ConstraintNF L C π₁ ≠ ConstraintNF L C π₂

/-! ## Digest-Only Boundaries (for W=1 Proof)

**PURPOSE**: Separate digest observations from bit observations to enable clean W=1 proof.

**KEY INSIGHT**: Only digest observations correspond to WorldCommit eliminations.
- Digest boundary: New gate config computed → WC protocol eliminates ≤ 1 world (WC-1)
- Bit boundary: New bit revealed → only filters initial_feasible (no eliminations)

**WHY NEEDED**: Bit boundaries can eliminate many worlds at once (when bit filters
initial set), but WC-1 only guarantees W=1 for digest-based eliminations.

By counting only digest boundaries, we get clean W=1 from the WorldCommit protocol.
-/

/-- **Digest Boundary**: Detect when digest constraints change.

    **Definition**: π₁ and π₂ have a digest boundary if their digest constraint
    lists differ.

    **Refinement of SegmentBoundary**: DigestBoundary π₁ π₂ → SegmentBoundary π₁ π₂
    (digest change implies NF change), but not conversely (bit-only changes don't
    create digest boundaries).

    **Used for**: W=1 proof via WorldCommit protocol.
-/
def DigestBoundary (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L) : Prop :=
  (ConstraintNF L C π₁).digestMatches ≠ (ConstraintNF L C π₂).digestMatches

/-- **Digest boundary implies segment boundary**.

    **Statement**: If digest constraints changed, then NF changed.

    **Proof**: digestMatches is a component of ConstraintNF.
-/
theorem digestBoundary_implies_segmentBoundary
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L)
    (h : DigestBoundary L C π₁ π₂)
    : SegmentBoundary L C π₁ π₂ := by
  unfold DigestBoundary SegmentBoundary at *
  intro h_eq
  -- If NF equal, then components equal
  have : (ConstraintNF L C π₁).digestMatches = (ConstraintNF L C π₂).digestMatches := by
    rw [h_eq]
  exact h this

/-! ## Key Properties

**These properties follow directly from constraint extraction and normalization:**

1. **NF is canonical** (from normalize_unique theorem):
   Same constraints → same NF

2. **Constraints are monotone** (from constraints_monotone theorem):
   Later time → more constraints (never fewer)

3. **Boundary implies new information**:
   If SegmentBoundary π₁ π₂, then algorithm learned something new
   (new bit revealed OR new gate digest computed)

**Proof**: By contradiction:
- If NF(π₁) ≠ NF(π₂), then constraints(π₁) ≠ constraints(π₂) (by normalize_unique)
- By constraints_monotone, if π₁ earlier than π₂, constraints only grew
- Therefore: new constraint appeared → new information learned ∎

These properties are sufficient for the CDT lemmas.
The full partition algorithm can wait until we need to count segments.
-/

/-! ## Infrastructure Lemmas

**Purpose**: Support PlantedBoundaryDiversity by showing that bitDeterminations are
unchanged when only computedConfigs change (not revealedBits).

**Key Insight**: ConstraintNF.bitDeterminations comes from extractBitConstraints,
which depends only on revealedBits. Therefore, changing computedConfigs cannot
affect bitDeterminations.
-/

/-- **Lemma**: bitDeterminations unchanged when only computedConfigs differ.

    **Statement**: If two execution prefixes π₀ and π₁ have:
    - Same revealedBits
    - Different computedConfigs (e.g., π₁ adds one ConfigMatch)
    Then their normalized bitDeterminations are identical.

    **Why needed**: Proves `h_bits_unchanged` hypothesis in PlantedBoundaryDiversity.lean.

    **Proof strategy**: BitDeterminations come from extractBitConstraints, which
    depends only on revealedBits (by extractBitConstraints_depends_only_on_revealedBits).
    Since revealedBits are equal, bit Determinations must be equal.
-/
theorem bitDeterminations_unchanged_when_only_configs_change
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π₀ π₁ : ExecutionPrefixReal L)
    (h_bits_eq : π₀.revealedBits = π₁.revealedBits)
    : (ConstraintNF L C π₀).bitDeterminations = (ConstraintNF L C π₁).bitDeterminations := by
  -- Unfold definitions
  unfold ConstraintNF extractConstraints
  -- Key: extractBitConstraints produces same result when revealedBits are equal
  have h_bit_constraints_eq : extractBitConstraints L C π₀.revealedBits =
                               extractBitConstraints L C π₁.revealedBits := by
    apply extractBitConstraints_depends_only_on_revealedBits
    exact h_bits_eq
  -- Rewrite to make bit constraints equal
  rw [h_bit_constraints_eq]
  -- Now both sides have: normalize (extractBitConstraints ... π₁.revealedBits ++ extractConfigConstraints ... π_i.computedConfigs)
  -- Since normalize filters by isBitDetermination, and only extractBitConstraints produces BitDetermination constraints,
  -- the bitDeterminations field depends only on extractBitConstraints, which is now equal.

  -- Use NormalForm.normalize definition: it filters for isBitDetermination
  -- Both sides filter the same extractBitConstraints, so results are equal
  simp only [NormalForm.normalize]
  -- Both sides now have same bitConstraints appended with different configConstraints
  -- But filter isBitDetermination only extracts BitDetermination constraints
  -- extractBitConstraints produces only BitDetermination, extractConfigConstraints produces only ConfigMatch
  -- Therefore filtering gives same result

  -- Explicit: (a ++ b₀).filter f = (a ++ b₁).filter f when f filters out all of b₀ and b₁
  have key : ∀ (a : List (CutConstraint L C)) (b₀ b₁ : List (CutConstraint L C)),
      (∀ c ∈ b₀, NormalForm.isBitDetermination c = false) →
      (∀ c ∈ b₁, NormalForm.isBitDetermination c = false) →
      (a ++ b₀).filter NormalForm.isBitDetermination = (a ++ b₁).filter NormalForm.isBitDetermination := by
    intros a b₀ b₁ h₀ h₁
    rw [List.filter_append, List.filter_append]
    congr 1
    ·  -- Both filters on config constraints yield []
      have h_filter₀ : b₀.filter NormalForm.isBitDetermination = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c h_c
        have := h₀ c h_c
        simp [this]
      have h_filter₁ : b₁.filter NormalForm.isBitDetermination = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c h_c
        have := h₁ c h_c
        simp [this]
      rw [h_filter₀, h_filter₁]

  -- Key insight: filter isBitDetermination only sees bit constraints, not configs or synthetics
  -- So we need to handle the 3-part structure: bits ++ configs ++ synthetics

  -- First, show that synthetic configs don't contain BitDeterminations
  have h_synth₀_no_bit : ∀ c ∈ extractSyntheticConfigs L C π₀, isBitDetermination c = false := by
    intro c h_c
    unfold extractSyntheticConfigs at h_c
    simp only [List.mem_filterMap] at h_c
    obtain ⟨v, _, h_c_eq⟩ := h_c
    split at h_c_eq <;> try contradiction
    · split at h_c_eq <;> try contradiction
      simp only [Option.some.injEq] at h_c_eq
      subst h_c_eq
      rfl  -- ConfigMatch is not a BitDetermination

  have h_synth₁_no_bit : ∀ c ∈ extractSyntheticConfigs L C π₁, isBitDetermination c = false := by
    intro c h_c
    unfold extractSyntheticConfigs at h_c
    simp only [List.mem_filterMap] at h_c
    obtain ⟨v, _, h_c_eq⟩ := h_c
    split at h_c_eq <;> try contradiction
    · split at h_c_eq <;> try contradiction
      simp only [Option.some.injEq] at h_c_eq
      subst h_c_eq
      rfl  -- ConfigMatch is not a BitDetermination

  -- Now apply key twice: first for configs, then for synthetics
  have h_key_configs := key (extractBitConstraints L C π₁.revealedBits)
    (extractConfigConstraints L C π₀.computedConfigs)
    (extractConfigConstraints L C π₁.computedConfigs)
    (by  -- extractConfigConstraints π₀.computedConfigs contains no BitDetermination
      intro c h_c
      unfold extractConfigConstraints at h_c
      simp only [List.mem_filterMap] at h_c
      obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_c
      split at h_c_eq <;> try contradiction
      simp only [Option.some.injEq] at h_c_eq
      subst h_c_eq
      rfl)  -- ConfigMatch is not a BitDetermination
    (by  -- extractConfigConstraints π₁.computedConfigs contains no BitDetermination
      intro c h_c
      unfold extractConfigConstraints at h_c
      simp only [List.mem_filterMap] at h_c
      obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_c
      split at h_c_eq <;> try contradiction
      simp only [Option.some.injEq] at h_c_eq
      subst h_c_eq
      rfl)  -- ConfigMatch is not a BitDetermination

  -- Apply key again for synthetics
  have h_key_synth := key (extractBitConstraints L C π₁.revealedBits ++ extractConfigConstraints L C π₁.computedConfigs)
    (extractSyntheticConfigs L C π₀)
    (extractSyntheticConfigs L C π₁)
    h_synth₀_no_bit
    h_synth₁_no_bit

  -- Combine using list associativity
  have h_assoc₀ : extractBitConstraints L C π₁.revealedBits ++ extractConfigConstraints L C π₀.computedConfigs ++ extractSyntheticConfigs L C π₀
    = extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₀.computedConfigs ++ extractSyntheticConfigs L C π₀) := by
    rw [List.append_assoc]

  have h_assoc₁ : extractBitConstraints L C π₁.revealedBits ++ extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₁
    = extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₁) := by
    rw [List.append_assoc]

  -- Now apply congruence to lift equality through normalize.bitDeterminations
  -- Goal: normalize (bits ++ configs₀ ++ synth₀).bitDeterminations = normalize (bits ++ configs₁ ++ synth₁).bitDeterminations
  -- We have:
  -- h_key_configs: (bits ++ configs₀).filter isBit = (bits ++ configs₁).filter isBit
  -- h_key_synth: ((bits ++ configs₁) ++ synth₀).filter isBit = ((bits ++ configs₁) ++ synth₁).filter isBit
  -- Use associativity to rewrite and chain equalities
  rw [h_assoc₀, h_assoc₁]
  -- After associativity, need to show (filter ...).dedup.toFinset.toList are equal
  -- Strategy: Show filtered lists are equal, then lift through dedup.toFinset.toList
  have h_combined : (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₀.computedConfigs ++ extractSyntheticConfigs L C π₀)).filter NormalForm.isBitDetermination =
                    (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₁)).filter NormalForm.isBitDetermination := by
    -- Strategy: Use key lemma twice, then chain with transitivity
    -- Step 1: (bits ++ (configs₀ ++ synth₀)).filter = (bits ++ (configs₁ ++ synth₀)).filter
    -- Step 2: (bits ++ (configs₁ ++ synth₀)).filter = (bits ++ (configs₁ ++ synth₁)).filter

    -- Apply key to configs₀ ++ synth₀ vs configs₁ ++ synth₀
    have h_step1 : (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₀.computedConfigs ++ extractSyntheticConfigs L C π₀)).filter NormalForm.isBitDetermination =
                   (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₀)).filter NormalForm.isBitDetermination := by
      apply key
      · intro c h_c
        simp only [List.mem_append] at h_c
        cases h_c with
        | inl h_config =>
          unfold extractConfigConstraints at h_config
          simp only [List.mem_filterMap] at h_config
          obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_config
          split at h_c_eq <;> try contradiction
          simp only [Option.some.injEq] at h_c_eq
          subst h_c_eq
          rfl
        | inr h_synth =>
          exact h_synth₀_no_bit c h_synth
      · intro c h_c
        simp only [List.mem_append] at h_c
        cases h_c with
        | inl h_config =>
          unfold extractConfigConstraints at h_config
          simp only [List.mem_filterMap] at h_config
          obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_config
          split at h_c_eq <;> try contradiction
          simp only [Option.some.injEq] at h_c_eq
          subst h_c_eq
          rfl
        | inr h_synth =>
          exact h_synth₀_no_bit c h_synth

    -- Apply key to configs₁ ++ synth₀ vs configs₁ ++ synth₁
    have h_step2 : (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₀)).filter NormalForm.isBitDetermination =
                   (extractBitConstraints L C π₁.revealedBits ++ (extractConfigConstraints L C π₁.computedConfigs ++ extractSyntheticConfigs L C π₁)).filter NormalForm.isBitDetermination := by
      apply key
      · intro c h_c
        simp only [List.mem_append] at h_c
        cases h_c with
        | inl h_config =>
          unfold extractConfigConstraints at h_config
          simp only [List.mem_filterMap] at h_config
          obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_config
          split at h_c_eq <;> try contradiction
          simp only [Option.some.injEq] at h_c_eq
          subst h_c_eq
          rfl
        | inr h_synth =>
          exact h_synth₀_no_bit c h_synth
      · intro c h_c
        simp only [List.mem_append] at h_c
        cases h_c with
        | inl h_config =>
          unfold extractConfigConstraints at h_config
          simp only [List.mem_filterMap] at h_config
          obtain ⟨⟨v, cfg⟩, _, h_c_eq⟩ := h_config
          split at h_c_eq <;> try contradiction
          simp only [Option.some.injEq] at h_c_eq
          subst h_c_eq
          rfl
        | inr h_synth =>
          exact h_synth₁_no_bit c h_synth

    -- Chain with transitivity
    exact Eq.trans h_step1 h_step2
  -- Goal is (filter ...).dedup.toFinset.toList = (filter ...).dedup.toFinset.toList
  -- h_combined gives filter equality, so rewrite with it
  rw [h_combined]

/-! ## Summary

**Provided definitions**:

- **ConstraintNF**: Canonical representation of current knowledge
- **SegmentBoundary**: Detects when algorithm learns new info
- **Key properties**: Follow from constraint extraction and normalization
- **Infrastructure lemma**: bitDeterminations unchanged when only configs change

**Deferred components**:
- InformationSegment structure
- Partition algorithm
- Segment counting theorems

**Rationale**:
- CDT lemmas only need SegmentBoundary predicate
- Segment counting will need full partition algorithm
- By deferring complex theorems, we avoid universe constraint issues
- Core concepts are fully defined and ready to use

**CDT lemma support**:
- CDT-1': No boundary + no reads → feasible worlds unchanged
- CDT-2': Boundary → some world excluded
- CDT-3: Boundary → Ω(n/W_min) work done

**Why this architecture works**:
- NF equality is structural (no hashing!)
- normalize_unique makes equality canonical
- extractConstraints + constraints_monotone ensure soundness
- Direct path to segment counting: boundaries = NF changes

-/

/-! ## Axiom Elimination: singleton_cut_implies_observed

**THEOREM**: Complete bit observation → ConfigMatch exists (eliminates axiom!)

This theorem replaces the `singleton_cut_implies_observed` axiom from
PlantedBoundaryDiversity.lean by providing a constructive proof via
synthetic ConfigMatch generation.

**Key insight**: Complete bit information is informationally equivalent
to config observation, so we can synthesize the ConfigMatch constraint
rather than axiomatizing that it was observed.

**Trust boundary**: Zero axioms (uses configFromBits round-trip property).
-/

/-- **THEOREM**: Singleton cut + complete observation → ConfigMatch exists.

    **Purpose**: Eliminate `singleton_cut_implies_observed` axiom (proven in PlantedBoundaryDiversity.lean).

    **Statement**: If all R_v bits at singleton cut node v are revealed,
    then ConstraintNF contains a ConfigMatch for v (synthesized constructively).

    **Proof**: Compose two lemmas:
    1. synthetic_configmatch_in_extracted: completeness → ConfigMatch in extractConstraints
    2. normalize preserves ConfigMatch → appears in digestMatches

    **Usage**: Call sites supply completeness evidence (derivable from correctness
    via fg_correctness_requires_complete_observation).

    **Trust Boundary**: Zero custom axioms (only Lean stdlib + proven lemmas).

    **Achievement**: Reduces QP profile from 3 to 2 axioms! 
-/
theorem singleton_cut_implies_observed_from_complete
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) (h_C_singleton : C.card = 1)
    (v : Fin L.dag.n) (h_v : v ∈ C)
    (π₀ : ExecutionPrefixReal L)
    (h_complete : completeAt L C π₀ v h_v)
    : ∃ (expectedCfg : Fin (2^(L.R v))),
        CutConstraint.ConfigMatch v h_v expectedCfg ∈ (ConstraintNF L C π₀).digestMatches := by
  -- Witness: reconstructed config from complete bits
  use reconstructedCfg L C π₀ v h_v h_complete

  -- Step 1: Show ConfigMatch is in extractConstraints (via synthetic generation)
  have h_in_extracted := synthetic_configmatch_in_extracted L C v h_v π₀ h_complete

  -- Step 2: ConstraintNF = normalize ∘ extractConstraints
  unfold ConstraintNF

  -- Step 3: Show normalize preserves ConfigMatch in digestMatches
  -- normalize filters by isConfigMatch and puts results in digestMatches field
  unfold NormalForm.normalize
  simp only []

  -- ConfigMatch passes isConfigMatch filter
  have h_is_configmatch : NormalForm.isConfigMatch
      (CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π₀ v h_v h_complete)) = true := by
    unfold NormalForm.isConfigMatch
    rfl

  have h_in_filtered : CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π₀ v h_v h_complete)
      ∈ List.filter NormalForm.isConfigMatch (extractConstraints L C π₀) := by
    apply List.mem_filter.mpr
    exact ⟨h_in_extracted, h_is_configmatch⟩

  -- Survives dedup
  have h_in_dedup : CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π₀ v h_v h_complete)
      ∈ List.dedup (List.filter NormalForm.isConfigMatch (extractConstraints L C π₀)) := by
    apply List.mem_dedup.mpr
    exact h_in_filtered

  -- Survives toFinset
  have h_in_finset : CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π₀ v h_v h_complete)
      ∈ (List.dedup (List.filter NormalForm.isConfigMatch (extractConstraints L C π₀))).toFinset := by
    apply List.mem_toFinset.mpr
    exact h_in_dedup

  -- Appears in toList (digestMatches field)
  apply Finset.mem_toList.mpr
  exact h_in_finset

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced (and we just eliminated one!)
-/

#print axioms digestBoundary_implies_segmentBoundary
#print axioms bitDeterminations_unchanged_when_only_configs_change
#print axioms singleton_cut_implies_observed_from_complete

end LStar.StructuralOWF.Foundations
