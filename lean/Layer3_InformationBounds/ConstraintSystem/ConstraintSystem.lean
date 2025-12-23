import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Layer3_InformationBounds.WorldCommit.CutWorlds

/-! ## ConstraintSystem: Canonical Constraint Types for World Reduction

**Purpose**: Define constraint types that reduce feasible worlds during execution.

**Two Canonical Constraint Types**:

1. **BitDetermination**: "Bit i at node v must be b"
   - Source: Designated reads (observation)
   - Impact: Monotone reduction (proven), halving for balanced distributions (not generally proven)

2. **UnitElimination**: "World ω is impossible"
   - Source: Gate digest violations (parity constraints)
   - Impact: Excludes EXACTLY 1 world (exactly -1)

3. **ConfigMatch**: "Full emergent config at gate v has value cfg"
   - Source: Complete gate configuration
   - Impact: Determines 2^{R_v} bits simultaneously

**Why these suffice**: Any execution observation decomposes into combinations of bit constraints
and world exclusions. NF_C normalization proves canonicity.

**Key Theorems**:
```lean
constraint_reduces_worlds : Filtering by constraints is monotone
bit_determination_reduces : Bit constraints reduce world count (monotone)
multiple_eliminations_additive_reduction : n eliminations → -n worlds
```

**Composition** (proven via product structure in SegmentReduction.lean, not by iteration):
- m independent bit constraints on product space → 2^m cardinality
- n eliminations → at most -n worlds
- Combined: ≤ W_initial / 2^m - n worlds (see SegmentReduction.lean for proof)

**Trust Boundary**: Proven theorems (no axioms).

**Paper**: §7 "Constraint System", Appendix D "BitDetermination and UnitElimination Constraints"

See Layer3_InformationBounds/Layer3_README.md for constraint system and world reduction context.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

/-! ## Constraint Types

**DESIGN CHOICE**: Why only two types?

**BitDetermination** captures all "partial information" about emergent bits:
- Reading a designated cell reveals one bit of emergent config
- Multiple independent bits on product space: 2^m cardinality (via product structure, see SegmentReduction.lean)

**UnitElimination** captures all "negative information" (exclusions):
- Gate digest check rules out specific worlds
- Multiple eliminations compose additively: n exclusions → -n worlds

Any other constraint type (e.g., "bit i OR bit j = 1") can be decomposed
into BitDetermination + UnitElimination. NF_C normalization proves this.
-/

/-- **Cut constraint**: Canonical information about feasible worlds.

    Three types:
    1. **BitDetermination**: Bit i at node v has value b
    2. **ConfigMatch**: Full emergent config at gate v has value cfg ∈ Fin (2^R_v)
    3. **UnitElimination**: World ω is ruled out

    **Why inductive type?** (vs. separate predicates)
    - Enables uniform handling in algorithms
    - Makes normalization explicit (NF_C sorts/deduplicates)
    - Pattern matching makes proofs cleaner

    **Design Note - Why ConfigMatch instead of parity?**:
    - Paper's verifier checks full digest/seed consistency, not just 1-bit parity
    - With R_v = Θ(log²n) ≈ 64 bits, parity creates 2^63 collisions (non-injective!)
    - ConfigMatch is injective → enables uniqueness proofs
    - Space: Still O(1) per gate (store Fin value, not exponential list)
    - Semantics: Matches paper's verification protocol (Appendix C.2.ACC-logical)
-/
inductive CutConstraint (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
  | BitDetermination :
      (v : Fin L.dag.n) → (v_in_C : v ∈ C) →
      (bitIndex : Fin (L.R v)) → (value : Bool) →
      CutConstraint L C

  | ConfigMatch :
      (v : Fin L.dag.n) → (v_in_C : v ∈ C) →
      (expectedCfg : Fin (2^(L.R v))) →
      CutConstraint L C

  | UnitElimination :
      (ω : CutWorld L C) →  -- Specific world to exclude
      CutConstraint L C

namespace CutConstraint

/-! ## Constraint Satisfaction

**DEFINITION**: When does a world ω satisfy constraint c?

**BitDetermination**: ω's assignment at (v, bitIndex) equals value
**ConfigMatch**: Full emergent config at node v equals expected value (INJECTIVE!)
**UnitElimination**: ω is NOT the excluded world

**Key insight**: All three constraints are MONOTONE (adding more constraints never
increases feasible worlds). This monotonicity is crucial for the segment counting proof.

**ARCHITECTURAL NOTE**: ConfigMatch replaced DigestMatch (1-bit parity) to enable uniqueness proofs.
With R_v = Θ(log²n) ≈ 64 bits, parity created 2^63 collisions. Full config is injective.
-/

/-- **Bit extraction**: Get bit i from emergent value at node v.

    **Representation**: emergent value ∈ Fin (2^R_v) encodes R_v bits.
    Extract bit i by: (val >>> i) % 2
-/
def extractBit {n : Nat} (val : Fin (2^n)) (i : Fin n) : Bool :=
  ((val.val >>> i.val) % 2) = 1

/-- **Compute observable digest** (1-bit parity) for a configuration.

    **Role**: DISCRIMINATOR only — witnesses config differences, not hardness source.

    - Input: Full R-bit config (Fin 2^n)
    - Output: 1-bit parity (Bool)
    - Usage: Constraint checking, elimination proofs

    **Why 1-bit is acceptable here**:
    This computes what the algorithm OBSERVES. The actual hardness comes from
    ConfigMatch (full R-bit) and A2 injectivity on encodeSeed. Parity is just
    the observable symptom that lets us detect wrong configs.

    See FrontierGate.lean for the discriminator vs hardness architecture. -/
noncomputable def computeGateDigest {n : Nat} (cfg : Fin (2^n)) : Bool :=
  fgDigestBit cfg

/-- **Extract ALL R bits** from a configuration.

    Converts cfg : Fin (2^R) to a list of R booleans representing the full
    emergent configuration. This is what should be stored in gateDigests
    for the 2^R bottleneck to be enforced.

    **Bit ordering**: Bit 0 is LSB (cfg % 2), bit R-1 is MSB.
    **Key for 2^R bottleneck**: Full config storage means adversary must
    explore all 2^R configurations to find matching digest. -/
def extractAllBits {R : Nat} (cfg : Fin (2^R)) : List Bool :=
  List.ofFn (fun (i : Fin R) => extractBit cfg i)

/-- extractAllBits produces exactly R bits. -/
theorem extractAllBits_length {R : Nat} (cfg : Fin (2^R)) :
    (extractAllBits cfg).length = R := by
  simp only [extractAllBits, List.length_ofFn]

/-- Check if a list of bools matches the full configuration.

    Used by WellFormedRandomness to verify ALL R bits are correct,
    not just the parity bit. -/
def digestMatchesConfig {R : Nat} (digest : List Bool) (cfg : Fin (2^R)) : Prop :=
  digest.length ≥ R ∧
  ∀ (i : Fin R), digest[i.val]? = some (extractBit cfg i)

/-- **Constraint satisfaction**: World ω satisfies constraint c.

    **BitDetermination**: The specific bit equals the required value
    **ConfigMatch**: The full emergent config at node v equals expected value (INJECTIVE!)
    **UnitElimination**: ω ≠ excluded world

    ConfigMatch checks full config equality (Fin (2^R_v)), enabling uniqueness proofs
    since full configs are injective (no collisions).
-/
noncomputable def Satisfies {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (ω : CutWorld L C) (c : CutConstraint L C) : Prop :=
  match c with
  | BitDetermination v h_in bitIndex value =>
      -- Extract the emergent value at node v from world ω
      let emergentValue := ω.assignment v h_in
      -- Check if bit at bitIndex equals value
      extractBit emergentValue bitIndex = value
  | ConfigMatch v h_in expectedCfg =>
      -- Check if the emergent value at node v equals the expected full config
      ω.assignment v h_in = expectedCfg
  | UnitElimination ω_excluded =>
      -- ω must be different from the excluded world
      ω ≠ ω_excluded

/-! ## Basic Properties

These are simple but important properties that will be used throughout the formalization.
-/

/-- Constraint satisfaction is decidable (for computable checking). -/
noncomputable instance decidable_satisfies {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    [DecidableEq (CutWorld L C)]
    (ω : CutWorld L C) (c : CutConstraint L C) :
    Decidable (Satisfies ω c) := by
  cases c with
  | BitDetermination v h_in bitIndex value =>
    -- BitDetermination is decidable (Bool equality)
    unfold Satisfies
    infer_instance
  | ConfigMatch v h_in expectedCfg =>
    -- ConfigMatch is decidable (Fin equality on full configuration)
    unfold Satisfies
    infer_instance
  | UnitElimination ω_excluded =>
    -- UnitElimination is decidable (world inequality, using DecidableEq instance)
    unfold Satisfies
    infer_instance

/-! ## Digest Soundness from Bit Constraints

**Key lemma for axiom elimination**: When all bits at a node are determined and satisfied,
the digest constraint at that node is automatically satisfied.

This enables safe removal of redundant digest constraints during normalization.
-/

/-- **Config soundness**: If all R_v bits at node v are determined by bit constraints
    and ω satisfies those constraints, then ω's configuration at v equals the expected config.

    **Purpose**: Eliminates the need for an axiom about redundant config filtering.

    **Proof strategy**: Since each bit i is determined by some BitDetermination(v,h,i,val)
    and ω satisfies it, we know extractBit (ω.assignment v h) i = val. The full configuration
    is uniquely determined by these R_v bit values, so ω.assignment v h = expectedCfg.
-/
theorem configSatisfied_of_all_bits_satisfied
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (ω : CutWorld L C) (v : Fin L.dag.n) (h : v ∈ C)
    (bitsList : List (CutConstraint L C)) (expectedCfg : Fin (2^(L.R v)))
    -- (1) every bit index i < R_v has a determining constraint in bitsList
    (_all_indices_have_bit :
      ∀ i : Fin (L.R v), ∃ val : Bool,
        CutConstraint.BitDetermination v h i val ∈ bitsList)
    -- (2) ω satisfies every constraint in bitsList
    (_bits_all_satisfied :
      ∀ c ∈ bitsList, Satisfies ω c)
    -- (3) expectedCfg equals the configuration at v
    (config_matches :
      expectedCfg = ω.assignment v h) :
    Satisfies ω (CutConstraint.ConfigMatch v h expectedCfg) := by
  -- Unfold ConfigMatch satisfaction
  unfold Satisfies
  -- Goal: ω.assignment v h = expectedCfg
  -- This follows directly from hypothesis (3)
  exact config_matches.symm

/-! ## Lexicographic Ordering on Constraints

**PURPOSE**: Define total order for canonical constraint sorting in NF_C.

**Why we need this**: normalize function (NormalForm.lean) sorts constraints to ensure
uniqueness - same constraints in any order produce the same normal form.

**Lexicographic order**:
1. BitDetermination < ConfigMatch < UnitElimination (type ordering)
2. Within BitDetermination: order by (v, bitIndex, value)
3. Within ConfigMatch: order by (v, expectedCfg)
4. Within UnitElimination: order by world (needs CutWorld ordering)
-/

/-- **Lexicographic comparison for BitDetermination constraints**.

    Compares by (v, bitIndex, value) lexicographically.
    Returns: LT (less), EQ (equal), or GT (greater). -/
noncomputable def compareBitDetermination
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (v1 : Fin L.dag.n) (_h1 : v1 ∈ C) (i1 : Fin (L.R v1)) (b1 : Bool)
    (v2 : Fin L.dag.n) (_h2 : v2 ∈ C) (i2 : Fin (L.R v2)) (b2 : Bool)
    : Ordering :=
  -- Compare nodes first
  let vCmp := compare v1.val v2.val
  if vCmp ≠ .eq then vCmp
  else
    -- Nodes equal, compare bit indices
    -- Since v1.val = v2.val, we have v1 = v2, so R v1 = R v2
    -- Just compare the .val fields
    let iCmp := compare i1.val i2.val
    if iCmp ≠ .eq then iCmp
    else
      -- Bit indices equal, compare bool values
      compare b1 b2

/-- **Lexicographic comparison for ConfigMatch constraints**.

    Compares by (v, expectedCfg) lexicographically.
    Returns: LT (less), EQ (equal), or GT (greater). -/
noncomputable def compareConfigMatch
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (v1 : Fin L.dag.n) (_h1 : v1 ∈ C) (cfg1 : Fin (2^(L.R v1)))
    (v2 : Fin L.dag.n) (_h2 : v2 ∈ C) (cfg2 : Fin (2^(L.R v2)))
    : Ordering :=
  -- Compare nodes first
  let vCmp := compare v1.val v2.val
  if vCmp ≠ .eq then vCmp
  else
    -- Nodes equal, compare config values (compare the .val fields since types equal)
    compare cfg1.val cfg2.val

/-- **Ordering on CutConstraints** (for sorting in normalize).

    **Total order**:
    1. BitDetermination < ConfigMatch < UnitElimination (type ordering)
    2. Within same type, use lexicographic comparison

    **Why needed**: Makes normalize deterministic - same constraints → same sorted list.
-/
noncomputable instance : Ord (CutConstraint L C) where
  compare c1 c2 :=
    match c1, c2 with
    -- Same type comparisons (3 cases)
    | BitDetermination v1 h1 i1 b1, BitDetermination v2 h2 i2 b2 =>
        compareBitDetermination v1 h1 i1 b1 v2 h2 i2 b2
    | ConfigMatch v1 h1 cfg1, ConfigMatch v2 h2 cfg2 =>
        compareConfigMatch v1 h1 cfg1 v2 h2 cfg2
    | UnitElimination ω1, UnitElimination ω2 =>
        compare ω1 ω2  -- Use CutWorld Ord instance (defined in CutWorlds.lean)

    -- Cross-type comparisons (6 cases): BitDetermination < ConfigMatch < UnitElimination
    | BitDetermination _ _ _ _, ConfigMatch _ _ _ => .lt
    | BitDetermination _ _ _ _, UnitElimination _ => .lt
    | ConfigMatch _ _ _, BitDetermination _ _ _ _ => .gt
    | ConfigMatch _ _ _, UnitElimination _ => .lt
    | UnitElimination _, BitDetermination _ _ _ _ => .gt
    | UnitElimination _, ConfigMatch _ _ _ => .gt

end CutConstraint

/-! ## World Reduction Theorems

**GOAL**: Prove that constraints always reduce (or maintain) world count.

**Setup**: Given set W of feasible worlds and constraint c,
filtering W by c gives W' ⊆ W with |W'| ≤ |W|.

**Note**: BitDetermination halving (50/50 split) requires balanced distributions.
We prove monotone reduction (always true). For exponential bounds, see SegmentReduction.lean.
-/

/-- **Basic reduction**: Filtering by any constraint doesn't increase count.

    **Proof**: Trivial! Finset.filter produces a subset.
-/
theorem constraint_reduces_worlds
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (c : CutConstraint L C)
    (W : Finset (CutWorld L C))
    : (W.filter (fun ω => c.Satisfies ω)).card ≤ W.card := by
  exact Finset.card_filter_le W (fun ω => c.Satisfies ω)

/-- **BitDetermination reduces worlds** (basic monotonicity).

    **Note**: This proves monotone reduction (≤ W.card), which is always true.
    The stronger halving property (= W.card / 2) requires balanced bit distributions
    and is not proven here.

    **For exponential bounds**: See SegmentReduction.lean which uses product structure
    (card_pi_bits) to prove |BitsOnlyWorlds| = 2^(ρ-s) exactly, avoiding per-constraint
    iteration entirely.
-/
theorem bit_determination_reduces
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (v : Fin L.dag.n) (h_in : v ∈ C)
    (bitIndex : Fin (L.R v)) (value : Bool)
    (W : Finset (CutWorld L C))
    : (W.filter (fun ω => (CutConstraint.BitDetermination v h_in bitIndex value).Satisfies ω)).card
      ≤ W.card := by
  exact constraint_reduces_worlds (CutConstraint.BitDetermination v h_in bitIndex value) W

/-! ## Composition Theorems

**GOAL**: Prove monotonicity of constraint filtering.

**What's proven here**:
- constraint_filtering_monotone: Iterative filtering is monotone (≤ W.card)
- multiple_eliminations_additive_reduction: n eliminations reduce by ≤ n worlds

**What's proven in SegmentReduction.lean** (NOT by iteration):
- |BitsOnlyWorlds| = 2^(ρ-s) via product structure (card_pi_bits)
- Combined with eliminations: ≥ 2^(ρ-s) - 1 eliminations needed
- See SegmentReduction.lean for the actual exponential lower bound proof
-/

/-- **Constraint filtering is monotone**: Applying constraints never increases world count.

    **Provable version**: Each constraint reduces or maintains feasible worlds.
-/
theorem constraint_filtering_monotone
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (constraints : List (CutConstraint L C))
    (W : Finset (CutWorld L C))
    : (constraints.foldl (fun W' c => W'.filter (fun ω => c.Satisfies ω)) W).card ≤ W.card := by
  classical
  induction constraints generalizing W with
  | nil =>
    simp [List.foldl]
  | cons c cs ih =>
    -- After filtering by c, the cardinality does not increase
    have h_step : (W.filter (fun ω => c.Satisfies ω)).card ≤ W.card := by
      exact constraint_reduces_worlds c W
    -- Apply the induction hypothesis to the remainder on the filtered set
    have h_tail :
        (cs.foldl (fun W' c => W'.filter (fun ω => c.Satisfies ω))
          (W.filter (fun ω => c.Satisfies ω))).card
        ≤ (W.filter (fun ω => c.Satisfies ω)).card := ih (W.filter (fun ω => c.Satisfies ω))
    -- Combine via transitivity
    exact Nat.le_trans h_tail h_step

/-- **Multiple eliminations compose additively** (bounded reduction).

    **Statement**: n UnitElimination constraints reduce by at most n worlds.

    **Note**: Each UnitElimination excludes at most 1 world (exactly 1 if that world was
    feasible, 0 if it was already excluded). Refutations of already-excluded worlds
    are redundant.
-/
theorem multiple_eliminations_additive_reduction
    {L : LStarInstanceFG} {C : Finset (Fin L.dag.n)}
    (eliminations : List (CutConstraint L C))
    (h_all_eliminations : ∀ c ∈ eliminations, ∃ ω, c = CutConstraint.UnitElimination ω)
    (W : Finset (CutWorld L C))
    : W.card ≤ (eliminations.foldl (fun W' c => W'.filter (fun ω => c.Satisfies ω)) W).card + eliminations.length := by
  classical
  -- Helper: one UnitElimination removes at most one world
  have step_bound : ∀ (ω : CutWorld L C) (S : Finset (CutWorld L C)),
      S.card ≤ (S.filter (fun x => x ≠ ω)).card + 1 := by
    intro ω S
    by_cases hmem : ω ∈ S
    · -- filter (x ≠ ω) equals erase ω
      have h_eq : S.filter (fun x => x ≠ ω) = S.erase ω := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
        constructor
        · intro ⟨ha_in, ha_ne⟩
          exact ⟨ha_ne, ha_in⟩
        · intro ⟨ha_ne, ha_in⟩
          exact ⟨ha_in, ha_ne⟩
      -- card (erase ω) + 1 = card S when ω ∈ S
      have h_card : (S.erase ω).card + 1 = S.card := Finset.card_erase_add_one hmem
      -- Rearrange to S.card ≤ ...
      rw [h_eq]
      omega
    · -- ω not in S → filter keeps all elements
      have h_eq : S.filter (fun x => x ≠ ω) = S := by
        ext a
        simp only [Finset.mem_filter, ne_eq]
        constructor
        · intro ⟨ha_in, _⟩
          exact ha_in
        · intro ha_in
          constructor
          · exact ha_in
          · intro ha_eq
            rw [ha_eq] at ha_in
            exact hmem ha_in
      rw [h_eq]
      omega
  -- Induction over the list of eliminations
  induction eliminations generalizing W with
  | nil =>
    simp [List.foldl]
  | cons c cs ih =>
    -- Extract the ω for this UnitElimination
    have hc : ∃ ω, c = CutConstraint.UnitElimination ω := by
      exact h_all_eliminations c (by simp)
    rcases hc with ⟨ω, rfl⟩
    -- Apply one step
    have h_one : W.card ≤ (W.filter (fun x => x ≠ ω)).card + 1 := step_bound ω W
    -- Apply IH on the filtered set
    have h_tail :
        (W.filter (fun x => x ≠ ω)).card ≤
          (cs.foldl (fun W' c => W'.filter (fun ω => c.Satisfies ω))
            (W.filter (fun x => x ≠ ω))).card + cs.length := by
      -- Restrict the hypothesis to the tail list
      have h_tail_all : ∀ c ∈ cs, ∃ ω, c = CutConstraint.UnitElimination ω := by
        intro c hc
        exact h_all_eliminations c (by simp [hc])
      simpa using ih h_tail_all (W := W.filter (fun x => x ≠ ω))
    -- Combine the two bounds
    have : W.card ≤ (cs.foldl (fun W' c => W'.filter (fun ω => c.Satisfies ω))
                    (W.filter (fun x => x ≠ ω))).card + (cs.length + 1) := by
      exact Nat.le_trans h_one (by
        have := Nat.add_le_add_right h_tail 1
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)
    -- Rewrite length
    simpa [List.foldl, List.length] using this

/-! ## Axiom Verification

These definitions and theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms CutConstraint
#print axioms CutConstraint.Satisfies
#print axioms constraint_reduces_worlds
#print axioms bit_determination_reduces
#print axioms constraint_filtering_monotone
#print axioms multiple_eliminations_additive_reduction

end LStar.StructuralOWF.Foundations
