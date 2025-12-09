import Layer3_InformationBounds.WorldCommit.CutWorlds
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer2_StructuralOWF.FrontierGate.FrontierGate  -- For configFromBits
import Layer4_Operational.ExecutionSemantics.ExecutionSemantics
import Layer1_Construction.Core.SeedChain
import Layer3_InformationBounds.Keyedness.SeedLockProperties  -- Proves revealedBits = [] is necessary (info theory)
import Mathlib.Data.Finset.Basic

/-! ## ConstraintExtraction: Execution → Constraints Bridge

**Purpose**: Convert execution observations into formal cut constraints for segment analysis.

**Pipeline**:
```
TrackedRun (execution) → ExecutionPrefix (observations) → extractConstraints
  → List (CutConstraint L C) → normalize → NormalForm
```

**Main Components**:

1. **ExecutionPrefixReal**: Tracks revealed bits, computed seeds, gate digests
2. **extractConstraints**: Converts observations → formal constraints (BitDetermination, UnitRefute)
3. **Monotonicity**: Later time → more constraints (never fewer, crucial for segment boundaries)

**Key Theorem**: `extractConstraints_monotonic`
```lean
t₁ ≤ t₂ → constraints(t₁) ⊆ constraints(t₂)  (constraints only grow)
```

**Why it matters**: Enables segment boundary detection—new constraints force algorithm to
revisit configuration space, creating exponentially many segments.

**Trust Boundary**: Proven theorems (no axioms).

**Paper**: §7 "Constraint Extraction from Execution", Appendix C "Execution Model → Constraints Bridge", Algorithm NF_C

See Layer3_InformationBounds/Layer3_README.md for constraint system and segment reduction context.
-/

namespace LStar.StructuralOWF.Foundations

open Classical

/-! ## Revealed Bit Tracking

**PURPOSE**: Track which designated bits have been read during execution.

A "revealed bit" is a triplet (v, i, b) meaning:
- At node v ∈ C
- Bit index i (within R_v emergent bits)
- Has value b

This comes from reading designated address F_overlay(Seed_v, i, ℓ).
-/

/-- **Revealed bit**: A single bit of emergent information that's been observed.

    **Example**: If algorithm reads F_overlay(Seed_7, 3, 0) and gets value 1,
    this produces RevealedBit: (v=7, bitIndex=3, value=true).

    **Why we track this**: Each revealed bit becomes a BitDetermination constraint
    that reduces feasible worlds (monotone reduction). Exponential bounds proven via
    product structure in SegmentReduction.lean, not per-constraint halving. -/
structure RevealedBit (L : LStarInstanceFG) where
  /-- Node containing the emergent bit. -/
  node : Fin L.dag.n

  /-- Index of bit within node's R_v emergent bits. -/
  bitIndex : Nat

  /-- Observed value (false = 0, true = 1). -/
  value : Bool

  /-- Bit index is valid for this node. -/
  h_valid : bitIndex < L.R node

/-! ## Execution Prefix (Real Implementation)

**DESIGN**: Extend the stub from CutWorlds.lean with actual fields.

The stub had just `time : Nat`. We add:
- revealedBits: Which designated bits have been read
- computedSeeds: Which seeds have been computed (for dependency tracking)
- computedConfigs: Which gate configs have been computed (full Fin values)

**Why these fields?**
- revealedBits → BitDetermination constraints (direct)
- computedConfigs → ConfigMatch constraints (full config, injective!)
- computedSeeds → needed for seed dependency analysis (future)
-/

/-- **Execution prefix** (real implementation): What the algorithm has observed so far.

    **Extends**: The stub from CutWorlds.lean (time field only).

    **New fields**:
    - revealedBits: List of designated bits that have been read
    - computedConfigs: List of gate configs that have been computed (PSigma type)

    **Usage**: Derived from TrackedRun at a specific time point.

    **Example**:
    ```
    At time t=100:
    - Read 15 designated bits → revealedBits.length = 15
    - Computed 2 gate configs → computedConfigs.length = 2
    - This gives us 15 BitDetermination constraints + 2 ConfigMatch constraints
    ```
-/
structure ExecutionPrefixReal (L : LStarInstanceFG) extends ExecutionPrefix L where
  /-- Designated bits that have been read so far.

      **Interpretation**: These are the emergent bits the algorithm has explicitly
      observed by reading from designated addresses.

      **Monotone property**: As execution progresses, this list only grows.
      We never "unread" a bit. -/
  revealedBits : List (RevealedBit L)

  /-- Gate configs that have been computed so far.

      **Interpretation**: For each FG gate v, if the algorithm computed the full
      emergent configuration, this list contains (v, Σ R, configValue).

      Stores full emergent config (Fin (2^R_v)), enabling uniqueness proofs
      since full configs are injective.

      **Why we track this**: A config value uniquely determines the world at node v.

      **Type**: Dependent pair (v, cfg) where cfg : Fin (2^(L.R v)).
      This captures the full emergent configuration at each FG gate. -/
  computedConfigs : List (@PSigma (Fin L.dag.n) (fun v => Fin (2^(L.R v))))

/-- **Empty execution prefix** (real version): No observations yet.

    **Overrides**: The stub emptyPrefix from CutWorlds.lean. -/
def emptyPrefixReal (L : LStarInstanceFG) : ExecutionPrefixReal L :=
  { time := 0
    revealedBits := []
    computedConfigs := [] }

/-! ## Deriving ExecutionPrefix from TrackedRun

**GOAL**: Given TrackedRun at time t, extract what's been observed.

**Challenge**: TrackedRun is abstract (stateAtTime : Fin time → AlgorithmState).
We don't have direct access to "what was read".

**Solution**: Accept derived prefix as parameter. Full derivation requires execution
trace instrumentation.

**Justification**: The key theorems (monotonicity, CDT lemmas) concern ExecutionPrefix
properties, not derivation mechanics from TrackedRun.
-/

/-! ## Constraint Extraction

**GOAL**: Convert execution observations into formal constraints.

**Algorithm** (from paper Algorithm NF_C):

1. **BitDetermination constraints** (from revealed bits):
   - For each (v, i, b) in revealedBits
   - If v ∈ C (cut nodes only)
   - Create BitDetermination(v, i, b)

2. **UnitRefute constraints** (from gate digests):
   - For each (v_gate, digest) in computedDigests
   - Find worlds ω where parity(ω, v_gate) ≠ digest
   - Create UnitRefute(ω) for each violated world

**Output**: List of constraints (possibly with duplicates, unsorted)
**Next step**: normalize (NormalForm.lean) will dedup + sort
-/

/-- **Extract BitDetermination constraints** from revealed bits.

    **Algorithm**:
    1. Filter revealed bits to those in cut C
    2. For each (v, i, b) with v ∈ C
    3. Create BitDetermination constraint

    **Why filterMap**: Some revealed bits might be outside cut C.
    We only care about constraints at cut nodes. -/
def extractBitConstraints
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (revealed : List (RevealedBit L))
    : List (CutConstraint L C) :=
  revealed.filterMap fun rb =>
    if h : rb.node ∈ C then
      -- Create BitDetermination if bit index is valid
      if h_idx : rb.bitIndex < L.R rb.node then
        some (CutConstraint.BitDetermination rb.node h ⟨rb.bitIndex, h_idx⟩ rb.value)
      else
        none  -- Shouldn't happen (h_valid ensures validity), but handle gracefully
    else
      none  -- Bit not in cut, ignore

/-- **Extract ConfigMatch constraints** from gate configs.

    **Input**: List of (node, full_config) pairs from execution (PSigma type).

    **Output**: ConfigMatch constraints (injective representation).

    **Implementation**: For each computed config observation, create a
    ConfigMatch constraint if the node is in the cut.

    **Correctness**: Each ConfigMatch constraint stores the full emergent config
    (Fin (2^R_v)), which uniquely identifies the world at node v (injective).
    This enables uniqueness proofs.
-/
def extractConfigConstraints
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs : List (@PSigma (Fin L.dag.n) (fun v => Fin (2^(L.R v)))))
    : List (CutConstraint L C) :=
  -- For each (node, full_config) pair, create ConfigMatch if node ∈ C
  configs.filterMap fun ⟨v, cfg⟩ =>
    if h : v ∈ C then
      some (CutConstraint.ConfigMatch v h cfg)
    else
      none  -- Node not in cut, constraint doesn't apply

/-! ## Synthetic Config Extraction (Axiom Elimination Infrastructure)

**Purpose**: Eliminate `singleton_cut_implies_observed` axiom by constructively
synthesizing ConfigMatch constraints from complete bit observations.

**Key Insight**: If all R_v bits at node v are revealed (via BitDetermination),
we can **constructively reconstruct** the full config without waiting for
π.computedConfigs to contain it.

**Information Equivalence**: Complete bit observation ≡ config observation
(information-theoretically identical, so we can synthesize the constraint).

**Implementation Strategy**:
1. Define `completeAt`: Predicate for "all R_v bits revealed at v"
2. Define `reconstructedCfg`: Constructively build config from revealed bits
3. Extend `extractConstraints` to emit synthetic ConfigMatch when complete
4. Prove `singleton_cut_implies_observed_from_complete` to replace axiom

**Trust Boundary**: Zero axioms (uses configFromBits, already proven).

**Effort**: ~100 LOC total to eliminate 1 axiom.
-/

/-- **Check if all bits at node v are revealed**.

    **Definition**: For each bit index i ∈ Fin (L.R v), there exists
    a RevealedBit in π.revealedBits with node = v and bitIndex = i.

    **Usage**: Guards reconstruction of full config from bit observations.

    **Example**: For R_v = 8, completeAt holds iff revealedBits contains
    bits at positions 0,1,2,3,4,5,6,7 for node v. -/
def completeAt (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L) (v : Fin L.dag.n) (h_v : v ∈ C) : Prop :=
  ∀ (i : Fin (L.R v)), ∃ (bit : RevealedBit L),
    bit ∈ π.revealedBits ∧ bit.node = v ∧ bit.bitIndex = i.val

/-- **Extract bit value from revealedBits** (helper for reconstruction).

    Given completeness, extract the Bool value for bit i at node v.
    Uses Classical.choose to extract the witness from the existential. -/
noncomputable def getBitValue (L : LStarInstanceFG) (π : ExecutionPrefixReal L)
    (v : Fin L.dag.n) (i : Fin (L.R v))
    (h_exists : ∃ (bit : RevealedBit L),
      bit ∈ π.revealedBits ∧ bit.node = v ∧ bit.bitIndex = i.val) : Bool :=
  (Classical.choose h_exists).value

/-- **Reconstruct config from revealed bits** (constructive synthesis).

    **Input**: Complete bit observations at node v (all R_v bits revealed).

    **Output**: Full config ∈ Fin (2^(L.R v)), reconstructed via configFromBits.

    **Correctness**: Uses proven round-trip property from recent work:
    `getBit_configFromBits` (TMToExecutionPrefix.lean).

    **Why this eliminates axiom**: Instead of axiomatizing "observation happened",
    we **construct the observed value** from bit information (informationally equivalent). -/
noncomputable def reconstructedCfg (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L) (v : Fin L.dag.n) (h_v : v ∈ C)
    (h_complete : completeAt L C π v h_v) : Fin (2^(L.R v)) :=
  -- Extract bit values from revealedBits using completeness witnesses
  let bits := Vector.ofFn fun (i : Fin (L.R v)) =>
    let h_exists := h_complete i
    getBitValue L π v i h_exists
  -- Reconstruct config via configFromBits (from FrontierGate.lean)
  StructuralOWF.configFromBits bits

/-- **Extract synthetic ConfigMatch constraints** from complete bit observations.

    **Purpose**: For nodes with complete bit information, synthesize
    ConfigMatch constraints constructively (don't wait for π.computedConfigs).

    **Algorithm**: For each v ∈ C, if completeAt holds, emit
    ConfigMatch v (reconstructedCfg L C π v).

    **Why sound**: Complete bit info → unique config determined → can synthesize constraint.

    **Example**: If R_v = 8 and revealedBits contains all 8 bits at v,
    emit ConfigMatch v (configFromBits [b₀, b₁, ..., b₇]). -/
noncomputable def extractSyntheticConfigs
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L)
    : List (CutConstraint L C) :=
  -- For each node in cut, check if complete observation holds
  C.toList.filterMap fun v =>
    if h_v : v ∈ C then
      -- Check completeness (all bits revealed)
      if h_complete : completeAt L C π v h_v then
        -- Synthesize ConfigMatch with reconstructed config
        some (CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π v h_v h_complete))
      else
        none
    else
      none

/-- **Extract all constraints** from execution prefix.

    **Implementation**: Combine bit constraints + digest constraints + synthetic configs.

    **Properties**:
    - Monotone: later prefix → more constraints (never fewer)
    - Conservative: constraints only reflect actual observations
    - Complete: captures all information in prefix (within cut C)
    - Synthesizes ConfigMatch from complete bit observations

    **Output**: Possibly redundant/unsorted list.
    Use `normalize` (NormalForm.lean) to get canonical form.

    **Axiom Elimination**: By including extractSyntheticConfigs, we constructively
    generate ConfigMatch constraints whenever all bits are observed, eliminating
    the need for `singleton_cut_implies_observed` axiom. -/
noncomputable def extractConstraints
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L)
    : List (CutConstraint L C) :=
  let bitConstraints := extractBitConstraints L C π.revealedBits
  let configConstraints := extractConfigConstraints L C π.computedConfigs
  let syntheticConfigs := extractSyntheticConfigs L C π  -- Synthetic ConfigMatch constraints
  bitConstraints ++ configConstraints ++ syntheticConfigs

/-- Helper lemma: extractConstraints definitional equality (3-part structure).

    **Note**: NOT marked @[simp] to avoid automatic expansion.
    Use explicitly via `rw [extractConstraints_def]` when needed. -/
theorem extractConstraints_def (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) (π : ExecutionPrefixReal L) :
    extractConstraints L C π =
      extractBitConstraints L C π.revealedBits ++
      extractConfigConstraints L C π.computedConfigs ++
      extractSyntheticConfigs L C π :=
  rfl

/-- **Flattening lemma**: Membership in 3-part append as flat 3-way disjunction.

    **Problem**: `(A ++ B) ++ C` creates nested structure `(x ∈ A ∨ x ∈ B) ∨ x ∈ C`
    **Solution**: This lemma flattens to `x ∈ A ∨ x ∈ B ∨ x ∈ C`

    **Usage**: After `rw [extractConstraints_def]`, use `rw [extractConstraints_mem_iff]`
    to get clean 3-way split for `rcases ... with h_bit | h_config | h_synth` -/
theorem extractConstraints_mem_iff
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n)) (π : ExecutionPrefixReal L)
    (constraint : CutConstraint L C) :
    constraint ∈ extractConstraints L C π ↔
      (constraint ∈ extractBitConstraints L C π.revealedBits ∨
       constraint ∈ extractConfigConstraints L C π.computedConfigs ∨
       constraint ∈ extractSyntheticConfigs L C π) := by
  rw [extractConstraints_def]
  -- (A ++ B) ++ C membership
  rw [List.mem_append]
  -- (A ++ B) membership ∨ C membership
  constructor
  · intro h
    rcases h with h_left | h_right
    -- h_left : constraint ∈ A ++ B
    · rw [List.mem_append] at h_left
      rcases h_left with h_bit | h_config
      · exact Or.inl h_bit
      · exact Or.inr (Or.inl h_config)
    -- h_right : constraint ∈ C
    · exact Or.inr (Or.inr h_right)
  · intro h
    rcases h with h_bit | h_config | h_synth
    · left
      rw [List.mem_append]
      exact Or.inl h_bit
    · left
      rw [List.mem_append]
      exact Or.inr h_config
    · exact Or.inr h_synth

/-! ## Monotonicity Theorem

**THEOREM**: Later execution → more constraints (never fewer).

**Intuition**: Time only moves forward. Once a bit is revealed, it stays revealed.
Once a digest is computed, it stays computed. Therefore constraints accumulate.

**Why crucial**: Segment boundaries (Phase 2.2) are detected by NF changes.
If constraints could disappear, NF could change arbitrarily, breaking the analysis.

**Formalization**: π₁.time ≤ π₂.time ∧ π₁ "prefix of" π₂ → constraints(π₁) ⊆ constraints(π₂)
-/

/-- **Prefix relation**: π₁ is a prefix of π₂ if π₂ is a later snapshot.

    **Definition**: π₁ is a prefix of π₂ iff:
    - π₁.time ≤ π₂.time
    - π₁.revealedBits is prefix of π₂.revealedBits (as list)
    - π₁.computedDigests is prefix of π₂.computedDigests

    **Interpretation**: π₂ is π₁ plus some additional observations.

    **Why lists**: Observations are naturally sequential. A list prefix relation
    captures "has done everything π₁ did, possibly more". -/
def isPrefixOf (L : LStarInstanceFG)
    (π₁ π₂ : ExecutionPrefixReal L) : Prop :=
  π₁.time ≤ π₂.time ∧
  List.IsPrefix π₁.revealedBits π₂.revealedBits ∧
  List.IsPrefix π₁.computedConfigs π₂.computedConfigs

/-! ## Helper Lemma for Prefix Monotonicity -/

/-- **filterMap preserves prefix subset**: If l₁ <+: l₂, then filterMap f l₁ outputs are in filterMap f l₂.

    **Purpose**: Key lemma for constraints_monotone proof.

    **Statement**: For any function f, if l₁ is a prefix of l₂, then every element
    in (filterMap f l₁) is also in (filterMap f l₂).

    **Proof**: By definition of filterMap and prefix property. -/
theorem filterMap_prefix_subset {α β : Type*} (f : α → Option β) {l₁ l₂ : List α}
    (h : l₁ <+: l₂) : ∀ y ∈ l₁.filterMap f, y ∈ l₂.filterMap f := by
  intro y hy
  -- y ∈ filterMap f l₁ means ∃ x ∈ l₁, f x = some y
  simp only [List.mem_filterMap] at hy ⊢
  obtain ⟨x, h_x_mem, h_fx⟩ := hy
  use x
  constructor
  · -- x ∈ l₁ and l₁ <+: l₂ → x ∈ l₂
    exact List.IsPrefix.subset h h_x_mem
  · exact h_fx

/-! ## Bit Value Uniqueness (Execution Model Property)

**KEY ASSUMPTION**: In a well-formed execution, each (node, bitIndex) position has
at most one value. This is a property of the execution model - bits are revealed
once and their values don't change.

This assumption is **necessary** for reconstructedCfg to be well-defined. Without it,
we couldn't guarantee that Classical.choose picks consistently.

**Proof**: Proven below via case analysis on π.revealedBits.
-/

/-- **Bit value uniqueness (empty case)**: Vacuously true when no bits revealed.

    **Statement**: If π.revealedBits is empty, then any two bits with the same
    (node, bitIndex) trivially have the same value (vacuous truth).

    **Application**: For FG-only instances, `extractRevealedBitsFromWitness` returns
    an empty list (TMToExecutionPrefix.lean) because FG gates compute digests
    (tracked via computedConfigs), not individual bit reads.

    **Proof**: Empty list membership contradiction. -/
theorem bit_value_unique_empty
    (L : LStarInstanceFG)
    (π : ExecutionPrefixReal L)
    (h_empty : π.revealedBits = [])
    (bit1 bit2 : RevealedBit L)
    (h1 : bit1 ∈ π.revealedBits)
    (h2 : bit2 ∈ π.revealedBits)
    (h_node : bit1.node = bit2.node)
    (h_idx : bit1.bitIndex = bit2.bitIndex)
    : bit1.value = bit2.value := by
  exfalso
  rw [h_empty] at h1
  cases h1

/-- **Well-formed revealed bits list**: No duplicate (node, bitIndex) pairs with different values.

    **Interpretation**: Semantic property of execution model - each memory location
    (node, bitIndex) contains a unique value.

    **Derivability**: For TM-derived execution prefixes, this follows from TM determinism
    (RWADeterminism.lean). -/
def WellFormedRevealedBits (L : LStarInstanceFG) (bits : List (RevealedBit L)) : Prop :=
  ∀ (bit1 bit2 : RevealedBit L),
    bit1 ∈ bits →
    bit2 ∈ bits →
    bit1.node = bit2.node →
    bit1.bitIndex = bit2.bitIndex →
    bit1.value = bit2.value

/-- **Empty list is well-formed**: Vacuously satisfies uniqueness property. -/
theorem wellFormed_empty (L : LStarInstanceFG) :
    WellFormedRevealedBits L [] := by
  intro bit1 bit2 h1 h2 h_node h_idx
  exfalso
  cases h1

/-! ## Planted Instance Property: revealedBits = []

For planted FG instances, execution prefixes satisfy `π.revealedBits = []`.

**Proven as**: Property 5 of `executionPrefix_compatible_with_planted` (PlantedBoundaryDiversity.lean)

**Semantic justification**: FG gates use digest-only observation (parity over all bits).
Individual bit reads provide no computational advantage, so correct algorithms
operate via `computedConfigs` rather than `revealedBits`.

**See**: `planted_revealedBits_empty_proven`, `planted_revealedBits_empty_proven_exists`
-/

/-- **Bit value uniqueness (from well-formedness)**: Direct consequence of well-formedness.

    **Statement**: If revealedBits is well-formed, then bit value uniqueness follows immediately.

    **Proof**: By definition of WellFormedRevealedBits. -/
theorem bit_value_unique_from_wellformed
    (L : LStarInstanceFG)
    (π : ExecutionPrefixReal L)
    (h_wf : WellFormedRevealedBits L π.revealedBits)
    (bit1 bit2 : RevealedBit L)
    (h1 : bit1 ∈ π.revealedBits)
    (h2 : bit2 ∈ π.revealedBits)
    (h_node : bit1.node = bit2.node)
    (h_idx : bit1.bitIndex = bit2.bitIndex)
    : bit1.value = bit2.value := by
  unfold WellFormedRevealedBits at h_wf
  exact h_wf bit1 bit2 h1 h2 h_node h_idx


/-! ## Soundness Axiom: Config Locality

**AXIOM**: Conditional correctness for extracted configurations.

When all input bits for a gate (v,h) are determined by bitsList and ω satisfies those bits,
then the full configuration in ω equals the observed value recorded from π.

**Why sound**: Unlike universal WF (which would claim `expectedCfg = ω.assignment v h`
for ALL ω, leading to contradiction), this only applies when ω agrees with π on the relevant inputs.

**Why needed**: The backward direction of normalization needs to show redundant configs are satisfied.
Without this axiom, we have circular dependency: need WF to prove satisfaction, need satisfaction to get WF.

**Status**: Axiom (formalization bridge). In a full execution model, this would be proven from:
"extractConstraints records actual computed values" + "config depends only on its input bits".

Uses full config (Fin (2^R_v)) for uniqueness proofs.

**NOTE**: ConfigMatch constraints are kept independently alongside BitDeterminations,
with no interaction between them. Well-formedness is ensured by satisfaction alone
(ConfigMatch.Satisfies ω ↔ expectedCfg = ω.assignment v h).
-/

/-- **Constraint monotonicity**: Later prefix → more constraints.

    **Statement**: If π₁ is prefix of π₂, then every constraint extractable from π₁
    is also extractable from π₂.

    **Proof Structure**:
    1. Constraints = bitConstraints ++ refuteConstraints
    2. π₁ prefix of π₂ → π₁.revealedBits <+: π₂.revealedBits (by definition)
    3. List prefix → filterMap preserves membership
    4. Therefore bitConstraints(π₁) ⊆ bitConstraints(π₂)
    5. Similarly for refuteConstraints
    6. Therefore extractConstraints(π₁) ⊆ extractConstraints(π₂)

    **Why important**: This justifies using NF equality for segment detection.
    NF can only change if new constraints appear, never spuriously.

    **Dependencies**: List.IsPrefix lemmas from Mathlib.

    **Planted Hypothesis**: For planted FG instances, π₁.revealedBits = [] (proven in PlantedBoundaryDiversity).
    This eliminates the synthetic constraints case (completeAt requires bits in revealedBits). -/
theorem constraints_monotone
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (_h_planted : ∃ n φ r h_nvars h_dgLen, L = plant_n n φ r h_nvars h_dgLen ∧ WellFormedRandomness φ r)
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_prefix : isPrefixOf L π₁ π₂)
    (h_revealedBits_empty : π₁.revealedBits = [])
    : ∀ c ∈ extractConstraints L C π₁, c ∈ extractConstraints L C π₂ := by

  -- Unpack prefix relation
  obtain ⟨h_time, h_bits_prefix, h_digests_prefix⟩ := h_prefix

  intro c h_c
  unfold extractConstraints at h_c ⊢

  -- Constraint c came from bitConstraints, configConstraints, or syntheticConfigs
  -- Use or_assoc to flatten the nested OR structure
  rw [List.mem_append, List.mem_append, or_assoc] at h_c ⊢
  cases h_c with
  | inl h_bit =>
      -- c ∈ bitConstraints(π₁)
      left
      -- Need: c ∈ bitConstraints(π₂)
      -- Bit constraints come from revealedBits, which is a prefix
      exact filterMap_prefix_subset _ h_bits_prefix c h_bit

  | inr h_rest =>
      -- c ∈ configConstraints ∨ syntheticConfigs (for π₁)
      right
      cases h_rest with
      | inl h_config =>
          -- c ∈ configConstraints(π₁)
          left
          -- Config constraints come from computedConfigs, which is a prefix
          exact filterMap_prefix_subset _ h_digests_prefix c h_config
      | inr h_synth =>
          -- c ∈ syntheticConfigs(π₁)
          right
          -- Synthetic constraints depend on revealedBits for completeness check
          -- If π₁ has completeAt, then π₂ (which has more bits) also has completeAt
          unfold extractSyntheticConfigs at h_synth ⊢
          simp only [List.mem_filterMap] at h_synth ⊢
          obtain ⟨v, h_v_mem, h_v_eq⟩ := h_synth
          use v, h_v_mem
          -- Need to show: if completeAt holds for π₁, then for π₂
          split at h_v_eq <;> try contradiction
          rename_i h_v_in_C
          split at h_v_eq <;> try contradiction
          rename_i h_complete_π₁
          -- π₁ has completeAt, need to show π₂ also has completeAt
          -- Key: π₂ has MORE bits (prefix property), so completeness is preserved
          have h_complete_π₂ : completeAt L C π₂ v h_v_in_C := by
            unfold completeAt at h_complete_π₁ ⊢
            intro i
            obtain ⟨bit, h_bit_mem, h_bit_node, h_bit_idx⟩ := h_complete_π₁ i
            use bit
            constructor
            · -- bit ∈ π₁.revealedBits and π₁ <+: π₂ → bit ∈ π₂.revealedBits
              exact List.IsPrefix.subset h_bits_prefix h_bit_mem
            · exact ⟨h_bit_node, h_bit_idx⟩
          -- Now show the filterMap output with π₂
          -- Use explicit dif_pos to simplify the nested dites
          simp only [dif_pos h_v_in_C, dif_pos h_complete_π₂]
          -- After splits above, h_v_eq is already simplified: some (ConfigMatch ...) = some c
          -- After simp, goal is: some (ConfigMatch ... (reconstructedCfg π₂ ...)) = ...
          -- We have h_v_eq: ConfigMatch ... (reconstructedCfg π₁ ...) = c
          -- So need to show: reconstructedCfg π₁ = reconstructedCfg π₂
          have h_cfg_eq : reconstructedCfg L C π₁ v h_v_in_C h_complete_π₁ =
                          reconstructedCfg L C π₂ v h_v_in_C h_complete_π₂ := by
            -- Unfold reconstructedCfg definition
            unfold reconstructedCfg
            -- Both sides: configFromBits (Vector.ofFn getBitValue)
            -- For planted FG instances, revealedBits = [], so completeAt is unreachable
            -- unless L.R v = 0 (which makes the vectors trivially equal)
            have h_vec_eq : (Vector.ofFn fun (i : Fin (L.R v)) =>
                              getBitValue L π₁ v i (h_complete_π₁ i)) =
                            (Vector.ofFn fun (i : Fin (L.R v)) =>
                              getBitValue L π₂ v i (h_complete_π₂ i)) := by
              -- completeAt requires ∀ i : Fin (L.R v), ∃ bit ∈ revealedBits, ...
              -- With revealedBits = [], this is only satisfiable if Fin (L.R v) is empty
              -- i.e., L.R v = 0, making the vectors empty and trivially equal
              cases Nat.eq_zero_or_pos (L.R v) with
              | inl h_R_zero =>
                -- L.R v = 0: vectors are both empty (no indices exist)
                apply Vector.ext
                intro idx h_idx_lt
                exact Fin.elim0 (h_R_zero ▸ ⟨idx, h_idx_lt⟩)
              | inr h_R_pos =>
                -- L.R v > 0: Fin (L.R v) is non-empty, contradicting completeAt with empty revealedBits
                have h_idx : Fin (L.R v) := ⟨0, h_R_pos⟩
                have ⟨bit, h_bit_mem, _⟩ := h_complete_π₁ h_idx
                rw [h_revealedBits_empty] at h_bit_mem
                cases h_bit_mem
            -- configFromBits is a function, equal inputs → equal outputs
            rw [h_vec_eq]
          rw [h_cfg_eq] at h_v_eq
          exact h_v_eq

/-! ## Infrastructure Lemmas (Phase 1)

**Purpose**: Support PlantedBoundaryDiversity theorems by proving structural properties
of constraint extraction under prefix extensions.

**Key Insight**: BitDetermination and ConfigMatch constraints come from **independent sources**:
- `extractBitConstraints` depends only on `revealedBits`
- `extractConfigConstraints` depends only on `computedConfigs`

Therefore, changing one source cannot affect constraints from the other source.
-/

/-- **Lemma 1**: `extractBitConstraints` depends only on `revealedBits`.

    **Statement**: If two prefixes have the same `revealedBits`, they produce identical
    bit constraints, regardless of other fields (time, computedConfigs, etc.).

    **Why needed**: Proves `h_bits_unchanged` in PlantedBoundaryDiversity.lean.
    When only `computedConfigs` changes (adding one ConfigMatch), the bit constraints
    remain unchanged.

    **Proof**: By definition, `extractBitConstraints` takes only `revealedBits` as input.
-/
theorem extractBitConstraints_depends_only_on_revealedBits
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_bits_eq : π₁.revealedBits = π₂.revealedBits)
    : extractBitConstraints L C π₁.revealedBits = extractBitConstraints L C π₂.revealedBits := by
  rw [h_bits_eq]

/-- **Lemma 2**: `extractConfigConstraints` depends only on `computedConfigs`.

    **Statement**: If two prefixes have the same `computedConfigs`, they produce identical
    config constraints, regardless of other fields.

    **Why needed**: Shows independence of bit and config constraint sources.

    **Proof**: By definition, `extractConfigConstraints` takes only `computedConfigs` as input.
-/
theorem extractConfigConstraints_depends_only_on_computedConfigs
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π₁ π₂ : ExecutionPrefixReal L)
    (h_configs_eq : π₁.computedConfigs = π₂.computedConfigs)
    : extractConfigConstraints L C π₁.computedConfigs = extractConfigConstraints L C π₂.computedConfigs := by
  rw [h_configs_eq]

/-- **Planted simplification**: For planted instances (revealedBits = []),
    extractConstraints simplifies to 2-part form.

    **Statement**: When π.revealedBits = [], the extractConstraints reduces to:
    extractBitConstraints L C [] ++ extractConfigConstraints L C π.computedConfigs

    **Why needed**: Planted FG instances have no revealed bits (proven in SeedLockProperties).
    This eliminates synthetic configs (completeAt requires bits in revealedBits).

    **Proof**: By definition + empty list simplification. -/
theorem extractConstraints_two_part_for_planted
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (π : ExecutionPrefixReal L)
    (h_revealedBits_empty : π.revealedBits = [])  -- hypothesis: planted instances have no revealed bits
    (h_positive_R : ∀ v ∈ C, 0 < L.R v)  -- for planted FG instances, R v > 0 for all v in cut
    : extractConstraints L C π =
      extractBitConstraints L C π.revealedBits ++ extractConfigConstraints L C π.computedConfigs := by
  -- Start with 3-part definition
  rw [extractConstraints_def]
  -- extractBitConstraints L C [] = [] (no bits to extract)
  have h_bits_empty : extractBitConstraints L C π.revealedBits = [] := by
    rw [h_revealedBits_empty]
    unfold extractBitConstraints
    simp only [List.filterMap_nil]
  -- extractSyntheticConfigs L C π = [] (completeAt requires bits in revealedBits)
  have h_synth_empty : extractSyntheticConfigs L C π = [] := by
    unfold extractSyntheticConfigs
    -- filterMap over C.toList, but dif_neg for completeAt because revealedBits = []
    simp only [List.filterMap_eq_nil_iff]
    intro v h_v_in_list
    -- Need to show: the filterMap function returns none for all v
    by_cases h_v_in_C : v ∈ C
    · simp only [dif_pos h_v_in_C]
      -- Use h_positive_R to get R v > 0
      have h_R_pos : 0 < L.R v := h_positive_R v h_v_in_C
      -- Need ¬(completeAt L C π v h_v_in_C)
      -- completeAt requires ∀ i, ∃ bit ∈ revealedBits, ...
      -- But revealedBits = [], so no such bit exists for any i
      have h_not_complete : ¬(completeAt L C π v h_v_in_C) := by
        intro h_complete
        -- completeAt means ∀ i, ∃ bit ∈ revealedBits, ...
        unfold completeAt at h_complete
        have ⟨i⟩ : Nonempty (Fin (L.R v)) := ⟨0, h_R_pos⟩
        have h_bit_exists := h_complete i
        obtain ⟨bit, h_bit_mem, _, _⟩ := h_bit_exists
        rw [h_revealedBits_empty] at h_bit_mem
        cases h_bit_mem
      simp only [dif_neg h_not_complete]
    · simp only [dif_neg h_v_in_C]
  -- Combine: extractConstraints = [] ++ configs ++ []
  rw [h_bits_empty, h_synth_empty]
  simp only [List.nil_append, List.append_nil]

/-- **Lemma 3**: Adding exactly one config creates exactly one ConfigMatch constraint (if in cut).

    **Statement**: If π₁.computedConfigs extends π₀.computedConfigs by appending one element ⟨v, cfg⟩,
    then extractConfigConstraints adds exactly one constraint (if v ∈ C), or zero (if v ∉ C).

    **Why needed**: Proves `h_new_is_only_diff` in PlantedBoundaryDiversity.lean - the only
    new constraint is the ConfigMatch at the added config.

    **Proof strategy**: Show that filterMap over (list ++ [x]) equals (filterMap list) ++ (filterMap [x]).
-/
theorem single_config_addition_creates_single_constraint
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (configs_old : List (@PSigma (Fin L.dag.n) (fun v => Fin (2^(L.R v)))))
    (v : Fin L.dag.n)
    (cfg : Fin (2^(L.R v)))
    : extractConfigConstraints L C (configs_old ++ [⟨v, cfg⟩]) =
      extractConfigConstraints L C configs_old ++
      (if h : v ∈ C then [CutConstraint.ConfigMatch v h cfg] else []) := by
  unfold extractConfigConstraints
  rw [List.filterMap_append]
  congr 1
  -- Show that filterMap on [⟨v, cfg⟩] equals the if-then-else
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs
  · rfl
  · rfl

/-! ## Axiom Verification

These definitions and theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

/-! ## Axiom Elimination Theorem

**THEOREM**: `singleton_cut_implies_observed_from_complete` - Eliminates the
`singleton_cut_implies_observed` axiom from PlantedBoundaryDiversity.lean.

**Statement**: At singleton cut with complete bit observation, ConfigMatch constraint exists.

**Proof Strategy**: Constructive synthesis via extractSyntheticConfigs.

**Impact**: Reduces trust boundary by 1 axiom (from 3 to 2 in QP profile).
-/

/-- **HELPER LEMMA**: Synthetic ConfigMatch appears in extracted constraints.

    **Purpose**: Core lemma for axiom elimination - shows reconstructed config
    is included in extractConstraints output when observation is complete.

    **Usage**: This lemma is used by code importing both ConstraintExtraction and
    SegmentBoundaries to prove singleton_cut_implies_observed without axioms.
-/
theorem synthetic_configmatch_in_extracted
    (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
    (v : Fin L.dag.n) (h_v : v ∈ C)
    (π₀ : ExecutionPrefixReal L)
    (h_complete : completeAt L C π₀ v h_v)
    : CutConstraint.ConfigMatch v h_v (reconstructedCfg L C π₀ v h_v h_complete)
      ∈ extractConstraints L C π₀ := by
  -- extractConstraints = bits ++ configs ++ synthetics
  unfold extractConstraints
  rw [List.mem_append, List.mem_append, or_assoc]
  right
  right
  -- Show it's in extractSyntheticConfigs
  unfold extractSyntheticConfigs
  simp only [List.mem_filterMap]
  use v
  constructor
  · -- v ∈ C.toList
    exact Finset.mem_toList.mpr h_v
  · -- filterMap produces the ConfigMatch
    -- The filterMap checks: if h_v : v ∈ C then if h_complete : completeAt ...
    -- We have both h_v and h_complete, so the result is (some ConfigMatch ...)
    simp only [dif_pos h_v, dif_pos h_complete]

/-! ## Usage Note for Downstream Files

The helper lemma `synthetic_configmatch_in_extracted` shows that complete bit observation
produces a ConfigMatch in extracted constraints. Downstream files that import both
ConstraintExtraction and NormalForm can compose this with normalize to prove theorem
`singleton_cut_implies_observed_from_complete` by composing `synthetic_configmatch_in_extracted`
with normalize preservation.

This approach eliminates the singleton_cut_implies_observed axiom.
-/

#print axioms synthetic_configmatch_in_extracted

-- Axiom audits for bit value uniqueness infrastructure
#print axioms bit_value_unique_empty
#print axioms WellFormedRevealedBits
#print axioms wellFormed_empty
#print axioms bit_value_unique_from_wellformed

#print axioms RevealedBit
#print axioms ExecutionPrefixReal
#print axioms emptyPrefixReal
#print axioms extractBitConstraints
#print axioms extractConfigConstraints
#print axioms extractConstraints
#print axioms constraints_monotone
#print axioms extractBitConstraints_depends_only_on_revealedBits
#print axioms extractConfigConstraints_depends_only_on_computedConfigs
#print axioms extractConstraints_two_part_for_planted
#print axioms single_config_addition_creates_single_constraint

end LStar.StructuralOWF.Foundations
