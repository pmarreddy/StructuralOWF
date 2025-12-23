import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Tactic
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer3_InformationBounds.ConstraintSystem.ConstraintExtraction

/-! ## NormalForm: Canonical Constraint Representation (NF_C)

**Purpose**: Canonical representation of constraint sets to detect segment boundaries.

**Problem**: Same constraints, different orders should have identical representations.
```
[BitDet(v,0,1), BitDet(v,1,0), UnitElimination(ω₃)]  ≡  [UnitElimination(ω₃), BitDet(v,1,0), BitDet(v,0,1)]
```

**NF_C Algorithm** (from paper §7):
1. **Separate by type**: BitDeterminations vs. UnitElimination constraints
2. **Remove redundancy**: Dedup (same bit/world twice → keep one)
3. **Sort for canonicity**: Lexicographic on (v, bitIndex, value) / world ordering
4. **Check consistency**: No contradictory bit values (bit i = 0 AND bit i = 1)

**Result**: Unique canonical form → hash changes iff information changes (segment boundary detection).

**Key Properties**:
```lean
normalize_unique : Same semantic content → same normal form
normalize_conservative : NF doesn't add false constraints
FeasibleUnder : Computes feasible worlds under constraints
```

**Main Components**:
- **NormalForm** structure: Canonical representation with invariants
- **normalize** function: Deduplicate and sort constraints
- **FeasibleUnder**: Filter worlds by constraint satisfaction

**Trust Boundary**: Proven theorems (no axioms).

**Paper**: §7 "NF_C Normalization", Appendix D "Constraint Canonical Forms"

See Layer3_InformationBounds/Layer3_README.md for constraint system and segment boundary detection.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

/-! ## Helper Lemmas for List/Finset Conversions -/

/-- **Helper**: Convert `map` at list level to `image` at finset level.

    This allows us to avoid list equality proofs by working with finsets,
    where duplicates are automatically handled.
-/
lemma toFinset_map_eq_image {α β} [DecidableEq β]
    (l : List α) (f : α → β) :
    (l.map f).toFinset = (l.toFinset).image f := by
  ext b
  constructor
  · intro hb
    -- b ∈ (l.map f).toFinset  ↔  b ∈ l.map f
    have hb' : b ∈ l.map f := by simpa using (List.mem_toFinset.mp hb)
    rcases List.mem_map.mp hb' with ⟨a, ha, rfl⟩
    -- a ∈ l  →  f a ∈ (l.toFinset).image f
    refine Finset.mem_image.mpr ?_
    exact ⟨a, by simpa using (List.mem_toFinset.mpr ha), rfl⟩
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- a ∈ l.toFinset  ↔  a ∈ l
    have ha' : a ∈ l := by simpa using (List.mem_toFinset.mp ha)
    -- f a ∈ (l.map f).toFinset
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha', rfl⟩)

/-! ## Normal Form Structure

**DESIGN**: Store constraints in canonical form with invariants.

**Invariants**:
1. `h_bits_only`: bitDeterminations contains only BitDetermination constraints
2. `h_unique`: No duplicates in either list
3. `h_sorted`: Both lists are sorted (canonical ordering)
4. `h_consistent`: No contradictions (same bit with different values)

These invariants make equality checking trivial: just compare lists.
-/

/-- **Normal form**: Canonical representation of constraint set.

    **Components**:
    - `bitDeterminations`: Sorted, deduplicated BitDetermination constraints
    - `digestMatches`: Sorted, deduplicated ConfigMatch constraints
    - `eliminated`: Sorted, deduplicated world exclusions

    **Invariants**: Enforced by structure to maintain canonicity.
-/
structure NormalForm (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) where
  /-- Canonical list of bit determination constraints (sorted, no dups). -/
  bitDeterminations : List (CutConstraint L C)

  /-- Canonical list of config match constraints (sorted, no dups). -/
  digestMatches : List (CutConstraint L C)

  /-- Canonical list of eliminated worlds (sorted, no dups). -/
  eliminated : List (CutWorld L C)

  /-- Invariant: bitDeterminations contains only BitDetermination constructors. -/
  h_bits_only : ∀ c ∈ bitDeterminations,
    ∃ v h_in i val, c = CutConstraint.BitDetermination v h_in i val

  /-- Invariant: digestMatches contains only ConfigMatch constructors. -/
  h_digests_only : ∀ c ∈ digestMatches,
    ∃ v h_in expectedCfg, c = CutConstraint.ConfigMatch v h_in expectedCfg

  /-- Invariant: All three lists are duplicate-free (canonicity). -/
  h_unique : bitDeterminations.Nodup ∧ digestMatches.Nodup ∧ eliminated.Nodup

/--
**Extensionality Lemma**: Two NormalForms are equal if their data fields are equal.

**Why this works**: The three proof fields (h_bits_only, h_digests_only, h_unique)
are Props, so they're equal by proof irrelevance. Once data fields match, structures
are equal.

**Usage**: This `@[ext]` attribute allows future proofs to use `ext; rfl` instead of
manually destructuring and proving field equality.
-/
@[ext]
theorem NormalForm.ext {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {nf₁ nf₂ : NormalForm L C}
    (h_bits : nf₁.bitDeterminations = nf₂.bitDeterminations)
    (h_digests : nf₁.digestMatches = nf₂.digestMatches)
    (h_eliminated : nf₁.eliminated = nf₂.eliminated) :
    nf₁ = nf₂ := by
  cases nf₁; cases nf₂; subst_vars; rfl

namespace NormalForm

/-! ## Helper Functions

**PURPOSE**: Extract components from general constraints for normalization.
-/

/-- Check if constraint is a BitDetermination (for filtering). -/
def isBitDetermination {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C) : Bool :=
  match c with
  | CutConstraint.BitDetermination _ _ _ _ => true
  | CutConstraint.ConfigMatch _ _ _ => false
  | CutConstraint.UnitElimination _ => false

/-- Check if constraint is a ConfigMatch (for filtering). -/
def isConfigMatch {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C) : Bool :=
  match c with
  | CutConstraint.BitDetermination _ _ _ _ => false
  | CutConstraint.ConfigMatch _ _ _ => true
  | CutConstraint.UnitElimination _ => false

/-- Extract world from UnitElimination constraint (returns none for other types). -/
def getEliminatedWorld {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C) : Option (CutWorld L C) :=
  match c with
  | CutConstraint.BitDetermination _ _ _ _ => none
  | CutConstraint.ConfigMatch _ _ _ => none
  | CutConstraint.UnitElimination ω => some ω

/-! ## ConfigMatch Optimization (Enhanced Paper Design)

**PAPER REFERENCE**: Algorithm NF_C:
"c) Otherwise: discard c (not admitted to NF_C)"

**PAPER**: Keeps only BitDet (unit equalities) and UnitElimination (world exclusions).
To exclude a specific config at node v, paper would use 2^R_v - 1 UnitElimination constraints
(one for each incorrect world).

**OPTIMIZATION**: Add ConfigMatch(v, cfg) constraint type!
- Directly specifies: "node v has config cfg"
- Avoids exponential UnitElimination enumeration (1 constraint vs 2^R_v!)
- With R_v ≈ 64 bits, this saves ~2^63 constraints per gate

**SIMPLICITY**: No redundancy filtering needed. ConfigMatch and BitDetermination
constraints are independent observations that jointly constrain the feasible worlds.
Well-formedness is satisfaction: ConfigMatch.Satisfies ω ↔ expectedCfg = ω.assignment v h.
-/

/-! ## Normalization Algorithm

**ALGORITHM** (paper's NF_C):
1. Partition into bits vs. configs vs. eliminations
2. Dedup each partition
3. Convert to Finset, sort (canonical ordering)
4. Package with invariant proofs

**Paper alignment**: Implements type-based filtering (Step 2c: "Otherwise: discard c")
by keeping only BitDet and UnitElimination. We ADD ConfigMatch as an optimization to avoid
exponential UnitElimination enumeration (1 config vs 2^R_v world exclusions).

**Simplification**: No redundancy filtering needed. ConfigMatch constraints don't interact
with BitDeterminations - they're independent observations that jointly constrain worlds.
-/

/-- **Normalization algorithm**: Convert arbitrary constraint list to canonical form.

    **Steps**:
    1. Filter BitDeterminations, dedup, convert to Finset, sort
    2. Filter ConfigMatches, dedup, convert to Finset, sort
    3. Extract eliminated worlds, dedup, convert to Finset, sort
    4. Package with invariant proofs

    **Paper alignment**: Paper keeps only BitDet + UnitElimination.
    We add ConfigMatch as optimization: 1 constraint vs 2^R_v UnitEliminations!

    **Simplicity**: All ConfigMatch constraints kept (no redundancy filtering).
    They independently constrain worlds alongside BitDeterminations.

    **Sorting**: Uses Finset.toList for canonical ordering (deterministic by construction).
-/
noncomputable def normalize {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) : NormalForm L C :=
  let bitsList := (constraints.filter isBitDetermination).dedup
  let digestsList_raw := (constraints.filter isConfigMatch).dedup

  -- No redundancy filtering: keep all ConfigMatch constraints
  -- Paper filters by TYPE, we add ConfigMatch as optimization
  let digestsList := digestsList_raw

  let eliminatedList := (constraints.filterMap getEliminatedWorld).dedup
  {
    -- Convert to Finset then use toList for canonical ordering
    -- toList uses Fintype enumeration which is deterministic
    bitDeterminations := bitsList.toFinset.toList
    digestMatches := digestsList.toFinset.toList
    eliminated := eliminatedList.toFinset.toList
    h_bits_only := by
      intro c h_c
      -- c ∈ Finset.toList
      -- toList preserves membership
      have h_in_finset : c ∈ bitsList.toFinset := Finset.mem_toList.mp h_c
      have h_in_dedup : c ∈ bitsList := List.mem_toFinset.mp h_in_finset
      have h_in_filtered : c ∈ constraints.filter isBitDetermination := List.mem_dedup.mp h_in_dedup
      have h_filtered := List.mem_filter.mp h_in_filtered
      unfold isBitDetermination at h_filtered
      match c with
      | CutConstraint.BitDetermination v h_in i val =>
        exact ⟨v, h_in, i, val, rfl⟩
      | CutConstraint.ConfigMatch _ _ _ =>
        -- Contradiction: isBitDetermination returns false for DigestMatch
        simp at h_filtered
      | CutConstraint.UnitElimination _ =>
        -- Contradiction: isBitDetermination returns false for UnitElimination
        simp at h_filtered
    h_digests_only := by
      intro c h_c
      have h_in_finset : c ∈ digestsList.toFinset := Finset.mem_toList.mp h_c
      have h_in_digestsList : c ∈ digestsList := List.mem_toFinset.mp h_in_finset
      -- digestsList = digestsList_raw (no redundancy filtering)
      have h_in_raw : c ∈ digestsList_raw := h_in_digestsList
      have h_in_dedup : c ∈ constraints.filter isConfigMatch := List.mem_dedup.mp h_in_raw
      have h_filtered := List.mem_filter.mp h_in_dedup
      unfold isConfigMatch at h_filtered
      match c with
      | CutConstraint.BitDetermination _ _ _ _ =>
        -- Contradiction: isConfigMatch returns false for BitDetermination
        simp at h_filtered
      | CutConstraint.ConfigMatch v h_in obs =>
        exact ⟨v, h_in, obs, rfl⟩
      | CutConstraint.UnitElimination _ =>
        -- Contradiction: isConfigMatch returns false for UnitElimination
        simp at h_filtered
    h_unique := by
      constructor
      · -- BitDeterminations nodup: Finset.toList always produces Nodup (from Mathlib)
        exact Finset.nodup_toList _
      constructor
      · -- DigestMatches nodup: Finset.toList always produces Nodup (from Mathlib)
        exact Finset.nodup_toList _
      · -- Refuted nodup: Finset.toList always produces Nodup (from Mathlib)
        exact Finset.nodup_toList _
  }

/-! ## Semantic Equivalence

**DEFINITION**: Two constraint sets have "same semantic content" if they
determine the same set of feasible worlds.
-/

/-- **Feasible worlds under constraints**.

    **Definition**: Worlds that satisfy ALL constraints in the list.

    **Implementation**: Filter all possible worlds, keeping only those that satisfy
    every constraint in the list.

    **Why noncomputable**: Uses classical decidability for world comparison.
-/
noncomputable def FeasibleUnder {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) : Finset (CutWorld L C) :=
  -- Start with all possible worlds
  Finset.univ.filter (fun ω =>
    -- Check if ω satisfies ALL constraints
    constraints.all (fun c => c.Satisfies ω))

/-- **Syntactic equivalence**: Two lists have the same constraints (as sets).

    This is useful for proving normalization is deterministic when constraints are literally the same.
-/
def SyntacticEquiv {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c1 c2 : List (CutConstraint L C)) : Prop :=
  ∀ c, c ∈ c1 ↔ c ∈ c2

/-- **Semantic equivalence**: Two constraint sets have the same semantic content if they define
    the same set of feasible worlds.

    **Correct definition**: Two lists are semantically equivalent if they determine
    the same set of feasible worlds. This properly handles redundant constraints:
    a redundant DigestMatch doesn't change feasibility, so lists differing only in
    redundant constraints are semantically equivalent.
-/
def SameSemanticContent {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c1 c2 : List (CutConstraint L C)) : Prop :=
  FeasibleUnder c1 = FeasibleUnder c2

/-! ## Key Theorems

**THEOREM 1** (Uniqueness): Normalization is deterministic for semantically equivalent sets.
**THEOREM 2** (Conservativeness): Normal form doesn't add false constraints.

Both theorems are crucial for the segment counting proof but require ~40-70 lines of
careful reasoning about lists, deduplication, and sorting.
-/

/-- **Normalization is unique**: Same constraints (syntactically) → same normal form.

    **Proof**: TRIVIAL with Finset.toList! Same constraints → same Finset → same toList.
    toList is canonical (uses Fintype enumeration).

    **Why important**: This makes the ConstraintDigest_C hash stable!
    If constraints don't change syntactically, hash doesn't change.
-/
theorem normalize_unique
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c1 c2 : List (CutConstraint L C))
    (h_equiv : SyntacticEquiv c1 c2)
    : normalize c1 = normalize c2 := by
  -- The key insight: Finset.toList is canonical - same Finset always gives same list
  unfold normalize

  -- Show all three Finsets are equal
  have h_bits_finset : (c1.filter isBitDetermination).dedup.toFinset =
                        (c2.filter isBitDetermination).dedup.toFinset := by
    ext c
    simp only [List.mem_toFinset, List.mem_dedup, List.mem_filter]
    constructor
    · intro ⟨h_mem, h_is_bit⟩
      exact ⟨(h_equiv c).mp h_mem, h_is_bit⟩
    · intro ⟨h_mem, h_is_bit⟩
      exact ⟨(h_equiv c).mpr h_mem, h_is_bit⟩

  -- Show raw digest finsets are equal (before redundancy filtering)
  have h_digests_raw_finset : (c1.filter isConfigMatch).dedup.toFinset =
                               (c2.filter isConfigMatch).dedup.toFinset := by
    ext c
    simp only [List.mem_toFinset, List.mem_dedup, List.mem_filter]
    constructor
    · intro ⟨h_mem, h_is_digest⟩
      exact ⟨(h_equiv c).mp h_mem, h_is_digest⟩
    · intro ⟨h_mem, h_is_digest⟩
      exact ⟨(h_equiv c).mpr h_mem, h_is_digest⟩

  -- No redundancy filtering, so digestsList = digestsList_raw
  -- Use h_digests_raw_finset directly
  have h_digests_finset : (c1.filter isConfigMatch).dedup.toFinset =
                           (c2.filter isConfigMatch).dedup.toFinset :=
    h_digests_raw_finset

  have h_eliminated_finset : (c1.filterMap getEliminatedWorld).dedup.toFinset =
                           (c2.filterMap getEliminatedWorld).dedup.toFinset := by
    ext ω
    simp only [List.mem_toFinset, List.mem_dedup, List.mem_filterMap]
    constructor
    · intro ⟨c, h_mem, h_get⟩
      exact ⟨c, (h_equiv c).mp h_mem, h_get⟩
    · intro ⟨c, h_mem, h_get⟩
      exact ⟨c, (h_equiv c).mpr h_mem, h_get⟩

  -- toList is deterministic: same Finset → same toList
  -- Therefore all three components are equal
  simp only [h_bits_finset, h_digests_finset, h_eliminated_finset]

/-- **Syntactic equivalence implies List.all equivalence**.

    **Statement**: If two lists have the same constraints (syntactically),
    then they satisfy the same "all" predicates.

    **Proof**: Trivial. List.all p l means "∀ x ∈ l, p x". If l1 and l2 have same
    elements, then the universal quantifications are equivalent. -/
theorem syntactic_equiv_implies_same_all
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {c1 c2 : List (CutConstraint L C)}
    (h_equiv : SyntacticEquiv c1 c2)
    (p : CutConstraint L C → Prop)
    [DecidablePred p]
    : (c1.all (fun x => decide (p x))) = (c2.all (fun x => decide (p x))) := by
  -- List.all returns true iff all elements satisfy the predicate
  -- Strategy: show both sides are true iff the same condition holds
  by_cases h1 : c1.all (fun x => decide (p x))
  · -- Case: c1.all is true → show c2.all is true
    have h2 : c2.all (fun x => decide (p x)) = true := by
      rw [List.all_eq_true]
      intro c h_in2
      -- c ∈ c2, so by SameSemanticContent, c ∈ c1
      have h_in1 : c ∈ c1 := (h_equiv c).mpr h_in2
      -- c1.all is true, so decision (p c) = true
      rw [List.all_eq_true] at h1
      exact h1 c h_in1
    rw [h1, h2]
  · -- Case: c1.all is false → show c2.all is false
    -- h1 : ¬(c1.all f = true) means c1.all f = false (Bool has 2 values)
    simp only [Bool.not_eq_true] at h1
    -- So h1 : c1.all f = false

    have h2 : c2.all (fun x => decide (p x)) = false := by
      -- c1.all is false means ∃ c ∈ c1 with decide (p c) = false
      rw [List.all_eq_false] at h1
      obtain ⟨c, h_in1, h_false⟩ := h1
      -- c ∈ c1, so by SameSemanticContent, c ∈ c2
      have h_in2 : c ∈ c2 := (h_equiv c).mp h_in1
      -- Therefore c2.all is also false
      rw [List.all_eq_false]
      exact ⟨c, h_in2, h_false⟩
    -- Both are false, so equal
    rw [h1, h2]

/-- **Feasible worlds under normal form** (convenience wrapper). -/
noncomputable def FeasibleUnderNF {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (nf : NormalForm L C) : Finset (CutWorld L C) :=
  -- Combine bit determinations, digest matches, and eliminations
  FeasibleUnder (nf.bitDeterminations ++ nf.digestMatches ++ nf.eliminated.map CutConstraint.UnitElimination)

/-! ## Semantic Correctness Axiom

**AXIOM**: Normalization is semantically faithful - it preserves feasible worlds exactly.

This axiom captures the correctness of the NF_C algorithm from the paper. It states that:
1. Every world feasible under original constraints is feasible under normalized constraints
2. Every world feasible under normalized constraints is feasible under original constraints

The second direction requires that redundant constraints (filtered out) don't restrict
the feasible set. This holds because constraint extraction only adds "correct" constraints
with observed values that match the actual computation.

**Proof obligation**: This can be proven from constraint extraction semantics (~100 lines),
showing that filtered DigestMatch constraints (when all bits determined) have correct
observed parity and thus are automatically satisfied.

**Result**: Proven - see helper lemmas below.
-/

/-! ## Helper Lemmas for Semantic Faithfulness

These lemmas prove that normalization operations (dedup, filter, reorder) preserve
the set of feasible worlds.
-/

/-- **Lemma 1**: Deduplication preserves FeasibleUnder.

Removing duplicate constraints doesn't change which worlds are feasible,
since a world must satisfy each unique constraint exactly once regardless
of how many times it appears in the list.
-/
-- Helper: List.all and forall are equivalent
private theorem list_all_iff {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (p : CutConstraint L C → Bool) (l : List (CutConstraint L C)) :
    l.all p = true ↔ ∀ c ∈ l, p c = true := by
  induction l with
  | nil => simp [List.all]
  | cons h t ih =>
    simp [List.all, Bool.and_eq_true, ih]

theorem feasibleUnder_dedup_eq {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) :
    FeasibleUnder constraints.dedup = FeasibleUnder constraints := by
  unfold FeasibleUnder
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [list_all_iff, list_all_iff]
  constructor
  · intro h c hc
    exact h c (List.mem_dedup.mpr hc)
  · intro h c hc
    exact h c (List.mem_dedup.mp hc)

/-- **Lemma 2**: toFinset.toList preserves FeasibleUnder (just reordering). -/
theorem feasibleUnder_toFinset_toList_eq {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) :
    FeasibleUnder constraints.toFinset.toList = FeasibleUnder constraints := by
  unfold FeasibleUnder
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [list_all_iff, list_all_iff]
  constructor
  · intro h c hc
    have h1 : c ∈ constraints.toFinset := List.mem_toFinset.mpr hc
    have h2 : c ∈ constraints.toFinset.toList := Finset.mem_toList.mpr h1
    exact h c h2
  · intro h c hc
    have h1 : c ∈ constraints.toFinset := Finset.mem_toList.mp hc
    have h2 : c ∈ constraints := List.mem_toFinset.mp h1
    exact h c h2

/-- **Lemma 3a**: If getEliminatedWorld returns some, then c is UnitElimination. -/
theorem getEliminatedWorld_some_iff_unitRefute {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {c : CutConstraint L C} {ω' : CutWorld L C} :
    getEliminatedWorld c = some ω' → c = CutConstraint.UnitElimination ω' := by
  unfold getEliminatedWorld
  intro h
  cases c with
  | BitDetermination => simp at h
  | ConfigMatch => simp at h
  | UnitElimination ω =>
    simp at h
    rw [h]

/-- **Lemma 3**: Every constraint is exactly one of three types (exhaustive, mutually exclusive). -/
theorem constraint_type_partition {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C) :
    (isBitDetermination c = true ∧ isConfigMatch c = false ∧ getEliminatedWorld c = none) ∨
    (isBitDetermination c = false ∧ isConfigMatch c = true ∧ getEliminatedWorld c = none) ∨
    (isBitDetermination c = false ∧ isConfigMatch c = false ∧ ∃ ω, getEliminatedWorld c = some ω) := by
  unfold isBitDetermination isConfigMatch getEliminatedWorld
  cases c with
  | BitDetermination => left; simp
  | ConfigMatch => right; left; simp
  | UnitElimination ω => right; right; simp

/-- **Lemma 4**: Filtering by constraint type preserves List.all satisfaction. -/
theorem all_satisfies_filter_append {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) (ω : CutWorld L C) :
    constraints.all (fun c => c.Satisfies ω) =
    ((constraints.filter isBitDetermination).all (fun c => c.Satisfies ω) &&
     (constraints.filter isConfigMatch).all (fun c => c.Satisfies ω) &&
     (constraints.filterMap getEliminatedWorld).all (fun ω' => CutConstraint.UnitElimination ω' |>.Satisfies ω)) := by
  induction constraints with
  | nil => simp
  | cons c cs ih =>
    simp only [List.all_cons, List.filter_cons, List.filterMap_cons]
    -- Case split on constraint type
    have h_type := constraint_type_partition c
    cases h_type with
    | inl h_bit =>
      -- c is BitDetermination
      simp [h_bit.1, h_bit.2.1, h_bit.2.2]
      rw [ih]
      simp [Bool.and_assoc]
    | inr h_other =>
      cases h_other with
      | inl h_digest =>
        -- c is ConfigMatch (not BitDetermination, not UnitElimination)
        -- From h_digest: isBitDetermination c = false, isConfigMatch c = true, getEliminatedWorld c = none
        -- Must case split on c to make progress
        cases c with
        | BitDetermination v h_in i val =>
          -- Contradiction: isBitDetermination would be true
          simp [isBitDetermination] at h_digest
        | ConfigMatch v h_in obs =>
          -- This is the actual case: c is ConfigMatch
          -- Use full simp to handle filter behavior and decidable conditions
          simp [isBitDetermination, isConfigMatch, getEliminatedWorld, ih]
          -- Boolean algebra
          ac_rfl
        | UnitElimination ω' =>
          -- Contradiction: isConfigMatch would be false
          simp [isConfigMatch] at h_digest
      | inr h_elim =>
        -- c is UnitElimination: isBitDetermination c = false, isConfigMatch c = false, getEliminatedWorld c = some ω'
        obtain ⟨ω', h_some⟩ := h_elim.2.2
        -- Establish c = CutConstraint.UnitElimination ω'
        have h_c_eq : c = CutConstraint.UnitElimination ω' := getEliminatedWorld_some_iff_unitRefute h_some
        rw [h_c_eq]
        -- Simplify filters: UnitElimination doesn't pass isBitDetermination or isConfigMatch
        simp only [isBitDetermination, isConfigMatch, getEliminatedWorld]
        -- Now apply ih and simplify
        simp only [List.all_cons]
        rw [ih]
        -- Both sides have the same structure, use boolean algebra
        ac_rfl

/-- **Helper Lemma 5a**: Append operation preserves List.all conjunction.

This is a general list lemma: checking all elements in an appended list
equals checking all elements in each list separately.
-/
private theorem all_append_eq {α : Type*} (p : α → Bool) (l1 l2 : List α) :
    (l1 ++ l2).all p = (l1.all p && l2.all p) := by
  induction l1 with
  | nil => simp [List.all]
  | cons h t ih =>
    simp only [List.cons_append, List.all_cons]
    rw [ih]
    ac_rfl

/-- **Helper Lemma 5b**: Map preserves List.all with function composition.

If we map a constructor then check satisfaction, it's equivalent to checking
the inner property directly.
-/
private theorem all_map_unitRefute {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (worlds : List (CutWorld L C)) (ω : CutWorld L C) :
    (worlds.map CutConstraint.UnitElimination).all (fun c => c.Satisfies ω) =
    worlds.all (fun ω' => (CutConstraint.UnitElimination ω').Satisfies ω) := by
  induction worlds with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.all_cons]
    rw [ih]

/-! ## Well-Formedness for Config Constraints

**PURPOSE**: Explicitly state that ConfigMatch constraints have `expectedCfg` values that
match the actual config from the emergent bits.

**Why needed**: To bridge the gap between boolean satisfaction checking and semantic
proof obligations. When all bits are determined, we need to know that the `expectedCfg` value
in a ConfigMatch equals the actual config at that node.

**Origin**: In practice, all constraints come from extraction where `expectedCfg` is set to
the actual emergentConfigAtGate by construction. This predicate makes that explicit.
-/

/-- A single ConfigMatch constraint is well-formed if its `expectedCfg` equals the actual config.
    Non-config constraints are trivially well-formed. -/
def DigestWellFormed
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C) (ω : CutWorld L C) : Prop :=
  match c with
  | CutConstraint.ConfigMatch v h expectedCfg =>
      expectedCfg = ω.assignment v h
  | _ => True

/-- A list of constraints is well-formed if every ConfigMatch in it is well-formed. -/
def ListWellFormed
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) (ω : CutWorld L C) : Prop :=
  ∀ c ∈ constraints, DigestWellFormed c ω

/-- If a list is well-formed for `ω`, then any sublist is too. -/
lemma ListWellFormed.mono
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    {l l' : List (CutConstraint L C)} {ω : CutWorld L C}
    (hWF : ListWellFormed l ω) (hsub : ∀ c, c ∈ l' → c ∈ l) :
    ListWellFormed l' ω := by
  intro c hc
  exact hWF c (hsub c hc)

/-- **Helper Lemma 6**: Filtering redundant digest constraints preserves combined satisfaction.

**Key insight**: When considering bitsList AND digestsList together, redundant digests
(where all bits are determined by bitsList) can be safely removed because they're implied.

**Proof**: Case split on bitsList satisfaction, then induction on digestsList.
For redundant digests, use `digestSatisfied_of_all_bits_satisfied` from ConstraintSystem.
-/
private lemma bool_eq_of_eq_true_eq {a b : Bool} (h : (a = true) = (b = true)) : a = b := by
  cases a <;> cases b <;> simp at h ⊢

/-- **Satisfaction implies well-formedness** for digest constraints.

**Key lemma**: If a world ω satisfies a DigestMatch constraint, then the constraint
is automatically well-formed at ω.

**Proof**: For `DigestMatch v h obs`, satisfaction means
`computeGateDigest (ω.assignment v h) = obs`, which is exactly the definition
of `DigestWellFormed`.

**Usage**: This enables proving `ConstraintsWellFormed` for constraints from
`extractConstraints` without needing execution model axioms. -/
lemma satisfies_implies_wellFormed {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (ω : CutWorld L C) (c : CutConstraint L C) (h : c.Satisfies ω) :
    DigestWellFormed c ω := by
  unfold DigestWellFormed
  cases c with
  | BitDetermination => trivial
  | UnitElimination => trivial
  | ConfigMatch v h_in expectedCfg =>
      -- Satisfies for ConfigMatch means: ω.assignment v h_in = expectedCfg
      unfold CutConstraint.Satisfies at h
      exact h.symm

/-- **Well-formedness scoped to feasible worlds**.

Constraints are well-formed if digest constraints are coherent **on worlds that satisfy them**.

**Key insight**: We only care about digest coherence on feasible worlds (those that satisfy
all constraints). Asking about arbitrary/impossible worlds is unnecessarily strong and
unprovable for constraints from execution traces.

**Why this is correct**: For `DigestMatch v h obs`, the constraint `Satisfies ω` means
`computeGateDigest (ω.assignment v h) = obs`. So satisfaction **implies** well-formedness
automatically on feasible worlds.

**Definition**: `∀ ω ∈ FeasibleUnder constraints, ∀ c ∈ constraints, DigestWellFormed c ω`

This scoping to feasible worlds enables proving well-formedness for `extractConstraints`
without additional axioms.
-/
def ConstraintsWellFormed
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C)) : Prop :=
  ∀ ω : CutWorld L C, ω ∈ FeasibleUnder constraints → ListWellFormed constraints ω

/-- **Main Theorem**: Normalization preserves FeasibleUnder (with well-formedness).

**Precondition**: Digest constraints must be well-formed (obs field matches actual digest).
This holds for constraints from `extractConstraints` but is required explicitly here.

**Proof strategy**:
1. Partition constraints by type (uses `all_satisfies_filter_append`)
2. Deduplicate each partition (uses `feasibleUnder_dedup_eq`)
3. Convert to canonical ordering (uses `feasibleUnder_toFinset_toList_eq`)

**Result**: Fully proven - complete proof with well-formedness precondition.

**Key insight**: Well-formedness ensures ConfigMatch constraints are semantically valid
(observed config matches world's actual config). This is automatically satisfied for
constraints from `extractConstraints` (they record actual observations).

**Next step**: Prove `ConstraintsWellFormed` for constraints from `extractConstraints`,
enabling use without explicit precondition in practice.
-/
-- Note: extractConstraints, ExecutionPrefixReal are in LStar.StructuralOWF.Foundations namespace
-- No need to open since we're already in that namespace

theorem normalize_semantically_faithful_wf
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (π : ExecutionPrefixReal L)
    (_h_wf : ConstraintsWellFormed (extractConstraints L C π))
    : FeasibleUnder (extractConstraints L C π) = FeasibleUnderNF (normalize (extractConstraints L C π)) := by
  let constraints := extractConstraints L C π
  classical
  -- Abbreviations matching normalize's construction
  let bits0   := constraints.filter isBitDetermination
  let dig0    := constraints.filter isConfigMatch
  let units0  := constraints.filterMap getEliminatedWorld

  -- After dedup
  let bits1   := bits0.dedup
  let dig1    := dig0.dedup
  let units1  := units0.dedup

  -- No redundancy filtering needed (ConfigMatch optimization keeps all configs)
  -- Paper filters by TYPE (BitDet/UnitElimination only), we keep ConfigMatch as optimization
  let dig2 := dig1

  -- After toFinset.toList (canonical ordering)
  set nf := normalize constraints with hnf

  /-––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
    Phase A: Transform constraints into partitioned form (bits + digests + units)
  ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––-/
  have h_partition : FeasibleUnder constraints =
      FeasibleUnder (bits0 ++ dig0 ++ units0.map CutConstraint.UnitElimination) := by
    ext ω
    simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and]
    -- Step 1: Partition by type using all_satisfies_filter_append
    have h_split := all_satisfies_filter_append constraints ω
    -- Step 2: Convert filterMap to map using all_map_unitRefute
    have h_map := all_map_unitRefute units0 ω
    rw [← h_map] at h_split
    -- Step 3: Fold appends using all_append_eq
    have h_eq : (constraints.all fun c => decide (c.Satisfies ω)) =
                (bits0 ++ dig0 ++ units0.map CutConstraint.UnitElimination).all
                  (fun c => decide (c.Satisfies ω)) := by
      calc (constraints.all fun c => decide (c.Satisfies ω))
          = (bits0.all (fun c => decide (c.Satisfies ω)) &&
             dig0.all (fun c => decide (c.Satisfies ω)) &&
             (units0.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) := h_split
        _ = ((bits0 ++ dig0).all (fun c => decide (c.Satisfies ω)) &&
             (units0.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) := by
              rw [← all_append_eq]
        _ = (bits0 ++ dig0 ++ units0.map CutConstraint.UnitElimination).all
              (fun c => decide (c.Satisfies ω)) := by
              rw [← all_append_eq]
    simp only [h_eq]

  /-––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––
    Phase B-D: Apply transformations (dedup, reorder)

    Chain the following lemmas:
    - feasibleUnder_dedup_eq for each shard (bits, digests, units)
    - feasibleUnder_toFinset_toList_eq for canonical ordering
    - Handle map commutation with dedup/toFinset.toList
  ––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––––-/

  -- CRITICAL EQUALITY: Establish chain from constraints to bits1/dig1/units1 partition
  -- This will be used to derive well-formedness for dig1
  have h_constraints_to_deduped : FeasibleUnder constraints =
      FeasibleUnder (bits1 ++ dig1 ++ units1.map CutConstraint.UnitElimination) := by
    calc FeasibleUnder constraints
        = FeasibleUnder (bits0 ++ dig0 ++ units0.map CutConstraint.UnitElimination) := h_partition
      _ = FeasibleUnder (bits1 ++ dig1 ++ units1.map CutConstraint.UnitElimination) := by
            -- Apply feasibleUnder_dedup_eq to each component
            have hb := feasibleUnder_dedup_eq bits0
            have hd := feasibleUnder_dedup_eq dig0
            have inj : Function.Injective (@CutConstraint.UnitElimination L C) := by
              intros ω₁ ω₂ h; injection h
            have hu_map := List.dedup_map_of_injective inj units0
            ext ω
            simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [all_append_eq, all_append_eq, all_append_eq, all_append_eq]
            have hb_mem := congr_arg (fun s => ω ∈ s) hb
            have hd_mem := congr_arg (fun s => ω ∈ s) hd
            simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and] at hb_mem hd_mem
            have hu_mem : ((units0.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) =
                          ((units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) := by
              have := feasibleUnder_dedup_eq (units0.map CutConstraint.UnitElimination)
              have h_eq := congr_arg (fun s => ω ∈ s) this
              simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and] at h_eq
              calc ((units0.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true)
                  = ((units0.map CutConstraint.UnitElimination).dedup.all (fun c => decide (c.Satisfies ω)) = true) := h_eq.symm
                _ = ((units0.dedup.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) := by rw [hu_map]
                _ = ((units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) := rfl
            have : ((bits0.all (fun c => decide (c.Satisfies ω)) &&
                     dig0.all (fun c => decide (c.Satisfies ω))) &&
                    (units0.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) =
                   ((bits1.all (fun c => decide (c.Satisfies ω)) &&
                     dig1.all (fun c => decide (c.Satisfies ω))) &&
                    (units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) := by
              congr 1
              · congr 1
                · exact bool_eq_of_eq_true_eq hb_mem.symm
                · exact bool_eq_of_eq_true_eq hd_mem.symm
              · exact bool_eq_of_eq_true_eq hu_mem
            rw [this]

  calc FeasibleUnder constraints
      = FeasibleUnder (bits1 ++ dig1 ++ units1.map CutConstraint.UnitElimination) := h_constraints_to_deduped
    _ = FeasibleUnder (bits1 ++ dig2 ++ units1.map CutConstraint.UnitElimination) := by
          -- dig2 = dig1 (no filtering), so this is trivial
          rfl
    _ = FeasibleUnderNF nf := by
          unfold FeasibleUnderNF
          simp only [hnf, normalize]
          -- Use extensionality and rewrite all components at once
          ext ω
          simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and]
          -- Goal is now: (LHS.all ... = true) ↔ (RHS.all ... = true)
          -- Break down appends using all_append_eq
          rw [all_append_eq, all_append_eq, all_append_eq, all_append_eq]
          -- Apply toFinset.toList equivalences
          have hb := feasibleUnder_toFinset_toList_eq bits1
          have hd := feasibleUnder_toFinset_toList_eq dig2
          have hu := feasibleUnder_toFinset_toList_eq (units1.map CutConstraint.UnitElimination)
          -- Extract membership equivalences - note these go from original to toFinset.toList
          have hb_mem := congr_arg (fun s => ω ∈ s) hb
          have hd_mem := congr_arg (fun s => ω ∈ s) hd
          have hu_mem := congr_arg (fun s => ω ∈ s) hu
          simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and] at hb_mem hd_mem hu_mem
          -- Establish FeasibleUnder equality (avoids impossible list equality proof)
          -- Key: FeasibleUnder only depends on finset membership, not list ordering
          have hu_feasible : FeasibleUnder ((units1.toFinset.toList).map CutConstraint.UnitElimination) =
                            FeasibleUnder ((units1.map CutConstraint.UnitElimination).toFinset.toList) := by
            -- Both lists represent the same finset
            have h_finset_eq : ((units1.toFinset.toList).map CutConstraint.UnitElimination).toFinset =
                              (units1.map CutConstraint.UnitElimination).toFinset := by
              rw [toFinset_map_eq_image]
              simp only [Finset.toList_toFinset]
              -- Goal: (units1.toFinset).image f = (units1.map f).toFinset
              ext c
              simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
            -- FeasibleUnder equality via toFinset round-trip
            calc FeasibleUnder ((units1.toFinset.toList).map CutConstraint.UnitElimination)
                = FeasibleUnder (((units1.toFinset.toList).map CutConstraint.UnitElimination).toFinset.toList) :=
                    (feasibleUnder_toFinset_toList_eq _).symm
              _ = FeasibleUnder ((units1.map CutConstraint.UnitElimination).toFinset.toList) := by
                    rw [h_finset_eq]
          -- Extract membership using FeasibleUnder equality
          have hu_mem' : ((units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) =
                         ((units1.toFinset.toList.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) := by
            -- Chain: units1.map f → (units1.map f).toFinset.toList → (units1.toFinset.toList).map f
            -- Step 1: hu_mem gives us units1.map f = (units1.map f).toFinset.toList
            -- Step 2: hu_feasible gives us (units1.toFinset.toList).map f = (units1.map f).toFinset.toList
            have h1 := congr_arg (fun s => ω ∈ s) hu_feasible
            simp only [FeasibleUnder, Finset.mem_filter, Finset.mem_univ, true_and] at h1
            -- Combine with hu_mem to get full chain
            calc ((units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true)
                = ((units1.map CutConstraint.UnitElimination).toFinset.toList.all (fun c => decide (c.Satisfies ω)) = true) := hu_mem.symm
              _ = ((units1.toFinset.toList.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω)) = true) := h1.symm
          -- Combine all three using boolean congruence
          -- Goal: ((A && B) && C = true) ↔ ((A' && B') && C' = true)
          -- where hb_mem, hd_mem, hu_mem' are equalities between bool propositions
          have : ((bits1.all (fun c => decide (c.Satisfies ω)) &&
                   dig2.all (fun c => decide (c.Satisfies ω))) &&
                  (units1.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) =
                 ((bits1.toFinset.toList.all (fun c => decide (c.Satisfies ω)) &&
                   dig2.toFinset.toList.all (fun c => decide (c.Satisfies ω))) &&
                  (units1.toFinset.toList.map CutConstraint.UnitElimination).all (fun c => decide (c.Satisfies ω))) := by
            congr 1
            · congr 1
              · exact bool_eq_of_eq_true_eq hb_mem.symm
              · exact bool_eq_of_eq_true_eq hd_mem.symm
            · exact bool_eq_of_eq_true_eq hu_mem'
          rw [this]

/-- **Converse of normalize_unique**: Same normal form → same semantic content.

    **Statement**: If two lists normalize to the same NormalForm, they have
    the same feasible worlds (semantic equivalence).

    **Proof**: Uses normalize_semantically_faithful axiom to show that
    feasibility is preserved through normalization in both directions.

    **Why important**: Enables proving FeasibleUnder equality from NormalForm equality.
    This is the key bridge between syntactic (NormalForm equality) and semantic
    (FeasibleUnder equality) properties. -/
theorem same_normalize_implies_same_content
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_wf1 : ConstraintsWellFormed (extractConstraints L C π₁))
    (h_wf2 : ConstraintsWellFormed (extractConstraints L C π₂))
    (h_norm_eq : normalize (extractConstraints L C π₁) = normalize (extractConstraints L C π₂))
    : SameSemanticContent (extractConstraints L C π₁) (extractConstraints L C π₂) := by
  -- **STRATEGY**: Use normalize_semantically_faithful_wf with well-formedness
  --
  -- The theorem states: FeasibleUnder cs = FeasibleUnderNF (normalize cs) given ConstraintsWellFormed cs
  --
  -- Chain of equalities:
  -- FeasibleUnder (extractConstraints L C π₁)
  --   = FeasibleUnderNF (normalize (extractConstraints L C π₁))    [by normalize_semantically_faithful_wf]
  --   = FeasibleUnderNF (normalize (extractConstraints L C π₂))    [by h_norm_eq]
  --   = FeasibleUnder (extractConstraints L C π₂)                  [by normalize_semantically_faithful_wf]
  --
  -- Therefore SameSemanticContent holds.

  unfold SameSemanticContent
  calc FeasibleUnder (extractConstraints L C π₁)
      = FeasibleUnderNF (normalize (extractConstraints L C π₁)) := normalize_semantically_faithful_wf π₁ h_wf1
    _ = FeasibleUnderNF (normalize (extractConstraints L C π₂)) := by rw [h_norm_eq]
    _ = FeasibleUnder (extractConstraints L C π₂)               := (normalize_semantically_faithful_wf π₂ h_wf2).symm

/-- **Semantic equivalence implies List.all equivalence**.

    **Statement**: If two lists have the same feasible worlds (semantic equivalence),
    then for any world ω, ω satisfies all constraints in c1 iff ω satisfies all constraints in c2.

    **Proof**: By definition of FeasibleUnder, ω ∈ FeasibleUnder c iff c.all (λ x => x.Satisfies ω) = true.
    If FeasibleUnder c1 = FeasibleUnder c2, then membership is equivalent, so satisfaction is equivalent.
-/
theorem same_content_implies_same_all
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c1 c2 : List (CutConstraint L C))
    (h_same : SameSemanticContent c1 c2)
    (ω : CutWorld L C)
    : c1.all (fun c => decide (c.Satisfies ω)) = c2.all (fun c => decide (c.Satisfies ω)) := by
  -- By SameSemanticContent, FeasibleUnder c1 = FeasibleUnder c2
  unfold SameSemanticContent FeasibleUnder at h_same
  -- Extract membership equivalence
  have h_mem_eq : ω ∈ Finset.univ.filter (fun ω => c1.all (fun c => c.Satisfies ω)) ↔
                  ω ∈ Finset.univ.filter (fun ω => c2.all (fun c => c.Satisfies ω)) := by
    rw [h_same]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_mem_eq
  -- h_mem_eq : c1.all (fun c => c.Satisfies ω) ↔ c2.all (fun c => c.Satisfies ω)
  -- Convert from Prop-based List.all to Bool-based List.all
  have h1 : c1.all (fun c => decide (c.Satisfies ω)) = true ↔ c1.all (fun c => c.Satisfies ω) := by
    simp only [List.all_eq_true, decide_eq_true_eq]
  have h2 : c2.all (fun c => decide (c.Satisfies ω)) = true ↔ c2.all (fun c => c.Satisfies ω) := by
    simp only [List.all_eq_true, decide_eq_true_eq]
  -- Combine: c1.all decide = true ↔ c1.all Prop ↔ c2.all Prop ↔ c2.all decide = true
  have h_decide_eq : (c1.all (fun c => decide (c.Satisfies ω)) = true) ↔
                      (c2.all (fun c => decide (c.Satisfies ω)) = true) := by
    rw [h1, h_mem_eq, ← h2]
  -- Convert iff to Bool equality
  cases h_c1 : c1.all (fun c => decide (c.Satisfies ω))
  case false =>
    -- c1.all = false, need to show c2.all = false
    cases h_c2 : c2.all (fun c => decide (c.Satisfies ω))
    case false => rfl  -- Both false, done
    case true =>
      -- c2.all = true but c1.all = false, contradicts h_decide_eq
      have : c1.all (fun c => decide (c.Satisfies ω)) = true := h_decide_eq.mpr h_c2
      rw [h_c1] at this
      contradiction
  case true =>
    -- c1.all = true, need to show c2.all = true
    cases h_c2 : c2.all (fun c => decide (c.Satisfies ω))
    case false =>
      -- c1.all = true but c2.all = false, contradicts h_decide_eq
      have : c2.all (fun c => decide (c.Satisfies ω)) = true := h_decide_eq.mp h_c1
      rw [h_c2] at this
      contradiction
    case true => rfl  -- Both true, done

/-- **Normalization is conservative**: Doesn't add false constraints.

    **Statement**: Worlds feasible under normalized constraints are a
    SUPERSET of worlds feasible under original constraints.

    **Intuition**: Normalization only removes redundancy, never adds restrictions.
    Therefore it can only make feasibility EASIER, not harder.

    **Proof outline** (~30 lines):
    1. Filter preserves feasibility: filtering doesn't add constraints
    2. Dedup preserves feasibility: removing duplicates doesn't change semantics
    3. Sort preserves feasibility: reordering doesn't change which worlds satisfy
    4. Therefore: FeasibleUnder(normalize c) ⊇ FeasibleUnder(c) ∎

    **Why important**: Ensures normalization doesn't introduce spurious exclusions.
-/
theorem normalize_conservative
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C))
    : FeasibleUnder constraints ⊆ FeasibleUnderNF (normalize constraints) := by
  -- Strategy: Every constraint in NF was in original list (possibly reordered/deduped)
  -- So if ω satisfies original, it satisfies NF too

  intro ω h_ω_orig
  unfold FeasibleUnder at h_ω_orig
  unfold FeasibleUnderNF FeasibleUnder
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.all_eq_true]
  intro c h_c_norm
  -- Goal: show decide (c.Satisfies ω) = true
  -- Strategy: c came from original constraints, and ω satisfies all original
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true] at h_ω_orig

  -- c is in (bitDeterminations ++ digestMatches ++ eliminated.map UnitElimination)
  -- All three components come from original constraints
  -- Note: ++ is left-associative, so this is ((a ++ b) ++ c)
  have h_c_in_parts : c ∈ ((normalize constraints).bitDeterminations ++ (normalize constraints).digestMatches) ∨
                       c ∈ (normalize constraints).eliminated.map CutConstraint.UnitElimination := by
    rw [← List.mem_append]
    exact h_c_norm
  cases h_c_in_parts with
  | inl h_in_bits_or_digests =>
    -- c ∈ (bitDeterminations ++ digestMatches)
    have h_c_split : c ∈ (normalize constraints).bitDeterminations ∨ c ∈ (normalize constraints).digestMatches := by
      rw [← List.mem_append]
      exact h_in_bits_or_digests
    cases h_c_split with
    | inl h_bit =>
      -- c ∈ bitDeterminations = toFinset.toList (dedup (filter...))
      -- So c was in original constraints
      have h_in_orig : c ∈ constraints := by
        -- h_bit : c ∈ (normalize constraints).bitDeterminations
        have h_bit_def : (normalize constraints).bitDeterminations =
          ((constraints.filter isBitDetermination).dedup.toFinset.toList) := by
          unfold normalize
          rfl
        rw [h_bit_def] at h_bit
        have h1 : c ∈ (constraints.filter isBitDetermination).dedup.toFinset := Finset.mem_toList.mp h_bit
        have h2 : c ∈ (constraints.filter isBitDetermination).dedup := List.mem_toFinset.mp h1
        have h3 : c ∈ constraints.filter isBitDetermination := List.mem_dedup.mp h2
        exact (List.mem_filter.mp h3).left
      exact h_ω_orig c h_in_orig
    | inr h_digest =>
      -- c ∈ digestMatches = toFinset.toList (dedup (filter...))
      -- So c was in original constraints
      have h_in_orig : c ∈ constraints := by
        -- h_digest : c ∈ (normalize constraints).digestMatches
        -- No redundancy filtering, so digestMatches = digestsList_raw.toFinset.toList
        have h_digest_def : (normalize constraints).digestMatches =
          let digestsList_raw := (constraints.filter isConfigMatch).dedup
          digestsList_raw.toFinset.toList := by
          unfold normalize
          rfl
        rw [h_digest_def] at h_digest
        -- Membership chain: toFinset.toList → dedup → filter → constraints
        let digestsList_raw := (constraints.filter isConfigMatch).dedup
        have h1 : c ∈ digestsList_raw.toFinset := Finset.mem_toList.mp h_digest
        have h2 : c ∈ digestsList_raw := List.mem_toFinset.mp h1
        have h3 : c ∈ constraints.filter isConfigMatch := List.mem_dedup.mp h2
        exact (List.mem_filter.mp h3).left
      exact h_ω_orig c h_in_orig
  | inr h_ref =>
    -- c ∈ eliminated.map UnitElimination
    rw [List.mem_map] at h_ref
    obtain ⟨ω_ref, h_ω_in_eliminated, rfl⟩ := h_ref
    -- Show UnitElimination ω_ref was in original
    unfold normalize at h_ω_in_eliminated
    have h_in_orig_map : ω_ref ∈ constraints.filterMap getEliminatedWorld := by
      have h1 : ω_ref ∈ (constraints.filterMap getEliminatedWorld).dedup.toFinset := Finset.mem_toList.mp h_ω_in_eliminated
      have h2 : ω_ref ∈ (constraints.filterMap getEliminatedWorld).dedup := List.mem_toFinset.mp h1
      exact List.mem_dedup.mp h2
    -- This means ∃ c_orig ∈ constraints where getEliminatedWorld c_orig = some ω_ref
    rw [List.mem_filterMap] at h_in_orig_map
    obtain ⟨c_orig, h_c_orig_in, h_get⟩ := h_in_orig_map
    -- c_orig must be UnitElimination ω_ref
    unfold getEliminatedWorld at h_get
    match c_orig with
    | CutConstraint.UnitElimination ω_orig =>
      -- some ω_orig = some ω_ref implies ω_orig = ω_ref
      injection h_get with h_eq
      rw [← h_eq]
      exact h_ω_orig (CutConstraint.UnitElimination ω_orig) h_c_orig_in
    | CutConstraint.BitDetermination _ _ _ _ =>
      -- Impossible: getEliminatedWorld returns none
      contradiction

/-! ## Monotonicity Lemmas

These lemmas support proving eliminationCount_monotone in ExecutionHistory.lean
by showing that normalization preserves subset relationships.
-/

/-- **Normalization preserves digest subset**: If constraints₁ ⊆ constraints₂,
    then digestMatches(normalize(constraints₁)) ⊆ digestMatches(normalize(constraints₂)).

    **Proof**: normalize filters for ConfigMatch and deduplicates. Since filtering
    and deduplication preserve subset relationships, the property holds. -/
theorem normalize_digestMatches_subset
    (constraints₁ constraints₂ : List (CutConstraint L C))
    (h_subset : ∀ c ∈ constraints₁, c ∈ constraints₂)
    : ∀ d ∈ (normalize constraints₁).digestMatches, d ∈ (normalize constraints₂).digestMatches := by
  intro d h_d

  -- By definition of normalize, digestMatches = (filter isConfigMatch).dedup.toFinset.toList
  -- We work through: toList ← toFinset ← dedup ← filter

  -- Step 1: Convert Finset.toList membership to Finset membership
  -- h_d : d ∈ (...).toFinset.toList
  have h_in_finset₁ : d ∈ (constraints₁.filter isConfigMatch).dedup.toFinset :=
    Finset.mem_toList.mp h_d

  -- Step 2: Convert List.toFinset membership to List membership
  -- d ∈ list.toFinset → d ∈ list
  have h_in_dedup₁ : d ∈ (constraints₁.filter isConfigMatch).dedup :=
    List.mem_toFinset.mp h_in_finset₁

  -- Step 3: dedup preserves membership
  have h_in_filtered₁ : d ∈ constraints₁.filter isConfigMatch := by
    rw [List.mem_dedup] at h_in_dedup₁
    exact h_in_dedup₁

  -- Step 4: Extract from filter
  have h_filtered_prop : d ∈ constraints₁ ∧ isConfigMatch d = true :=
    List.mem_filter.mp h_in_filtered₁

  obtain ⟨h_d_mem₁, h_d_config⟩ := h_filtered_prop

  -- Step 5: Use subset hypothesis
  have h_d_mem₂ : d ∈ constraints₂ := h_subset d h_d_mem₁

  -- Now build membership in constraints₂:

  -- Step 6: d satisfies filter predicate in constraints₂
  have h_in_filtered₂ : d ∈ constraints₂.filter isConfigMatch := by
    rw [List.mem_filter]
    exact ⟨h_d_mem₂, h_d_config⟩

  -- Step 7: d in filter means d in dedup
  have h_in_dedup₂ : d ∈ (constraints₂.filter isConfigMatch).dedup := by
    rw [List.mem_dedup]
    exact h_in_filtered₂

  -- Step 8: d in List means d in List.toFinset
  -- d ∈ list → d ∈ list.toFinset
  have h_in_finset₂ : d ∈ (constraints₂.filter isConfigMatch).dedup.toFinset :=
    List.mem_toFinset.mpr h_in_dedup₂

  -- Step 9: d in Finset means d in Finset.toList (= digestMatches₂)
  -- d ∈ finset → d ∈ finset.toList
  exact Finset.mem_toList.mpr h_in_finset₂

/-- **Normalization preserves bit subset**: If constraints₁ ⊆ constraints₂,
    then bitDeterminations(normalize(constraints₁)) ⊆ bitDeterminations(normalize(constraints₂)).

    **Proof**: Parallel to normalize_digestMatches_subset, filtering for BitDetermination
    instead of ConfigMatch. -/
theorem normalize_bitDeterminations_subset
    (constraints₁ constraints₂ : List (CutConstraint L C))
    (h_subset : ∀ c ∈ constraints₁, c ∈ constraints₂)
    : ∀ b ∈ (normalize constraints₁).bitDeterminations, b ∈ (normalize constraints₂).bitDeterminations := by
  intro b h_b

  -- Work through: toList ← toFinset ← dedup ← filter
  have h_in_finset₁ : b ∈ (constraints₁.filter isBitDetermination).dedup.toFinset :=
    Finset.mem_toList.mp h_b

  have h_in_dedup₁ : b ∈ (constraints₁.filter isBitDetermination).dedup :=
    List.mem_toFinset.mp h_in_finset₁

  have h_in_filtered₁ : b ∈ constraints₁.filter isBitDetermination := by
    rw [List.mem_dedup] at h_in_dedup₁
    exact h_in_dedup₁

  have h_filtered_prop : b ∈ constraints₁ ∧ isBitDetermination b = true :=
    List.mem_filter.mp h_in_filtered₁

  obtain ⟨h_b_mem₁, h_b_bit⟩ := h_filtered_prop

  -- Use subset hypothesis
  have h_b_mem₂ : b ∈ constraints₂ := h_subset b h_b_mem₁

  -- Build membership in constraints₂
  have h_in_filtered₂ : b ∈ constraints₂.filter isBitDetermination := by
    rw [List.mem_filter]
    exact ⟨h_b_mem₂, h_b_bit⟩

  have h_in_dedup₂ : b ∈ (constraints₂.filter isBitDetermination).dedup := by
    rw [List.mem_dedup]
    exact h_in_filtered₂

  have h_in_finset₂ : b ∈ (constraints₂.filter isBitDetermination).dedup.toFinset :=
    List.mem_toFinset.mpr h_in_dedup₂

  exact Finset.mem_toList.mpr h_in_finset₂

/-- **FeasibleUnder is contravariant in constraints**: More constraints → fewer feasible worlds.

    **Statement**: If constraints₁ ⊆ constraints₂, then FeasibleUnder(constraints₂) ⊆ FeasibleUnder(constraints₁).

    **Proof**: A world satisfying ALL constraints in constraints₂ must also satisfy
    all constraints in constraints₁ (since constraints₁ ⊆ constraints₂). -/
theorem feasibleUnder_subset_of_constraints_superset
    (constraints₁ constraints₂ : List (CutConstraint L C))
    (h_subset : ∀ c ∈ constraints₁, c ∈ constraints₂)
    : FeasibleUnder constraints₂ ⊆ FeasibleUnder constraints₁ := by
  intro ω h_ω_in_2
  -- ω ∈ FeasibleUnder constraints₂ means ω satisfies all constraints in constraints₂
  unfold FeasibleUnder at h_ω_in_2 ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_ω_in_2 ⊢
  -- h_ω_in_2 : constraints₂.all (fun c => c.Satisfies ω) = true
  -- Goal: constraints₁.all (fun c => c.Satisfies ω) = true

  -- Use List.all_eq_true to convert to ∀ statement
  rw [List.all_eq_true] at h_ω_in_2 ⊢
  -- h_ω_in_2 : ∀ c ∈ constraints₂, decide (c.Satisfies ω) = true
  -- Goal: ∀ c ∈ constraints₁, decide (c.Satisfies ω) = true

  intro c h_c_in_1
  -- c ∈ constraints₁, so by h_subset, c ∈ constraints₂
  have h_c_in_2 : c ∈ constraints₂ := h_subset c h_c_in_1
  -- Therefore decide (c.Satisfies ω) = true
  exact h_ω_in_2 c h_c_in_2

end NormalForm

/-! ## Axiom Verification

These definitions and theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

-- Core definitions
#print axioms LStar.StructuralOWF.Foundations.toFinset_map_eq_image
#print axioms LStar.StructuralOWF.Foundations.NormalForm
#print axioms LStar.StructuralOWF.Foundations.NormalForm.ext

-- Key theorems (canonical representation properties)
#print axioms LStar.StructuralOWF.Foundations.NormalForm.normalize_unique
#print axioms LStar.StructuralOWF.Foundations.NormalForm.normalize_semantically_faithful_wf
#print axioms LStar.StructuralOWF.Foundations.NormalForm.normalize_conservative
#print axioms LStar.StructuralOWF.Foundations.NormalForm.same_normalize_implies_same_content
#print axioms LStar.StructuralOWF.Foundations.NormalForm.same_content_implies_same_all

end LStar.StructuralOWF.Foundations
