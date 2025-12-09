import Layer3_InformationBounds.Support.SeedSemantics
import Layer3_InformationBounds.WorldCommit.CutWorlds
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Mathlib.Data.Finset.Basic

/-! ## EmergentConfig: Pure Emergent Configuration Computation

**Purpose**: Compute emergent configurations without depending on Plant.lean (breaks circular dependencies).

**Key Principle**: PURE functions—compute from CNF structure + assignments only, no planting dependencies.

**Main Functions**:

1. **emergentConfigAtGate**: Computes emergent config at gate from φ, numGates, assignment, gateIndex
   - Pure function (no plant_n dependency)
   - Parameterized by numGates for consistency

2. **WellFormedRandomness**: Predicate ensuring r.gateDigests match emergent config parities
   - Connects randomness to CNF structure
   - Non-circular (uses pure emergentConfigAtGate)

3. **emergentConfigAtVertex**: Vertex-indexed access to emergent configs

**Dependency Chain** (acyclic):
```
Ranks.lean → SeedSemantics.lean → EmergentConfig.lean (pure) → Plant.lean → PlantedInstanceConsistency.lean
```

**Why separate**: Enables Plant.lean to use emergent config computations without circular dependencies.
WellFormedRandomness defined via pure functions, not planted instances.

**Trust Boundary**: Pure functions (no axioms).

**Paper**: §6 "Emergent Configurations", §2.2 "Emergence Rank and Pure Computations"

See Layer3_InformationBounds/Layer3_README.md for emergent configuration and witness uniqueness context.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF

/-! ## Pure Emergent Configuration Function -/

/-- **PURE FUNCTION**: Compute emergent configuration at a gate from formula and assignment.

    **Parameterization**: Takes numGates to ensure R computation matches planted instances.

    **Inputs**:
    - φ: The 3-SAT formula
    - numGates: Number of FG gates (must match r.gateDigests.length in planted contexts!)
    - a: A satisfying assignment for φ
    - gateIndex: Which FG gate (index into r.gateDigests)

    **Output**: The emergent configuration (as Fin (2^R_v)) that would be produced
    at this gate when using assignment a.

    **KEY PROPERTY**: This function does NOT depend on r.gateDigests!
    It only depends on:
    1. The structure of φ (how it's reduced to L* DAG)
    2. The number of FG gates numGates (determines R computation)
    3. The satisfying assignment a
    4. The emergence matrix at gate v

    **Algorithm**:
    ```
    1. Get pure DAG structure: L = lstarStructureFromCNF φ numGates
    2. Map gateIndex → vertex v in DAG
    3. Compute full seed at v: seed_v = computeSeedAtVertex φ numGates a v
       (This is recursive: source vertices use assignment, internal use parent seeds)
    4. Extract emergent portion: last R_v bits of seed_v
    5. Convert to Fin (2^R_v) for parity computation
    ```

    **Termination**: Recursion in computeSeedAtVertex terminates via DAG acyclicity.

    **Non-Circular**: NO reference to plant_n or r! Pure computation from φ, numGates, a.

    **Type Consistency**: Uses R_of φ numGates internally, matching plant_n exactly! -/
noncomputable def emergentConfigAtGate (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (gateIndex : Nat)
    : Option (@PSigma Nat (fun R => Fin (Nat.pow 2 R))) :=
  -- Get pure L* structure
  let L : LStarInstanceFull := lstarStructureFromCNF φ h_nvars_pos numGates

  -- Convert gate-relative index to DAG vertex
  -- FG gates are at vertices [1 + φ.nvars, 1 + φ.nvars + numGates)
  let clause_start := 1 + φ.nvars
  let vertex_idx := clause_start + gateIndex

  -- Check if gateIndex is valid (must be < numGates) and vertex is in DAG
  if _h_gate : gateIndex < numGates then
    if h_vertex : vertex_idx < L.dag.n then
      let v : Fin L.dag.n := ⟨vertex_idx, h_vertex⟩
      -- Step 3: Compute full seed at v using ONLY φ, numGates, and a
      -- (This calls computeSeedAtVertex, which is recursive on DAG structure)
      let fullSeed : Seed (L.seedWidth v) := (computeSeedAtVertex φ h_nvars_pos numGates a v : Seed (L.seedWidth v))
      -- Step 4: Extract emergent portion (last R_v bits)
      let R_v := L.R v
      if h_cap : R_v ≤ L.seedWidth v then
        let emergentBits : Vector Bool R_v := extractEmergentBits fullSeed R_v h_cap
        -- Step 5: Convert to Fin (2^R_v) for configuration value
        let cfg : Fin (2^R_v) := emergentBitsToConfig emergentBits
        some ⟨R_v, cfg⟩
      else
        -- Invalid: R_v > seedWidth (should never happen by L.seedWidth_ok)
        none
    else
      -- Invalid: vertex not in DAG
      none
  else
    -- Invalid: gateIndex >= numGates
    none

/-! ## Helper Lemmas for emergentConfigAtGate -/

/-- **HELPER**: If emergentConfigAtGate returns some, then gateIndex < numGates.

    This extracts the implicit constraint from the definition structure. -/
lemma emergentConfigAtGate_some_implies_gateIndex_bound
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (gateIndex : Nat)
    (R : Nat) (cfg : Fin (2^R))
    (h_some : emergentConfigAtGate φ h_nvars_pos numGates a gateIndex = some ⟨R, cfg⟩) :
    gateIndex < numGates := by
  -- Use by_contra to assume gateIndex ≥ numGates
  by_contra h_not_lt
  push_neg at h_not_lt
  -- Unfold the definition to expose the conditional structure
  simp only [emergentConfigAtGate] at h_some
  -- When gateIndex ≥ numGates, the definition returns none
  (split_ifs at h_some with h_gate h_vertex h_cap;
    -- All branches lead to either a contradiction or none
    try simp at h_some)
  -- The first case gives h_gate : gateIndex < numGates and h_not_lt : numGates ≤ gateIndex
  omega

/-! ## Well-Formed Randomness (NON-CIRCULAR Definition) -/

/-- **DEFINITION** (non-circular): Well-formed randomness for OWF construction.

    Uses parameterized emergentConfigAtGate with numGates = r.gateDigests.length
    to ensure R computation matches plant_n exactly.

    **Property**: r.gateDigests encodes the correct parities of emergent configurations
    computed from r.assignment.

    **NON-CIRCULAR**: Uses emergentConfigAtGate (pure function) instead of plant_n!

    **Meaning**: For each gate index i:
    - Compute emergent_cfg := emergentConfigAtGate φ numGates r.assignment i
      where numGates := r.gateDigests.length
    - Require: r.gateDigests[i] encodes parity(emergent_cfg)

    **Implementation**: Pure function with no dependency on plant_n.

    **Mathematical Content**:
    - φ.satisfies r.assignment: The embedded assignment is a valid solution
    - Digest consistency: For each FG gate i, the digest bits in r.gateDigests[i]
      match the parity of the emergent configuration computed from r.assignment

    **Why This Works**:
    - emergentConfigAtGate computes what the emergent config WOULD BE using R_of
    - We require r.gateDigests to encode this BEFORE planting
    - Plant.lean then COPIES r.gateDigests into the instance
    - Result: Planted instance has digests matching actual emergent configs!

    **Type Consistency**: numGates = r.gateDigests.length ensures R values match
    plant_n exactly, eliminating ALL type mismatches!

    **Precondition**: Requires φ.nvars > 0, provided by CNF structure invariant. -/
def WellFormedRandomness (φ : CNF) (r : Randomness) : Prop :=
  let numGates := r.gateDigests.length  -- Derive numGates from randomness structure
  φ.satisfies r.assignment ∧
  φ.clauses.length ≥ numGates ∧  -- ARCHITECTURAL FIX: Clause count constraint (eliminates specification gaps)
  ∀ (i : Nat) (h : i < numGates),
    match emergentConfigAtGate φ φ.nvars_pos numGates r.assignment i with
    | none => True  -- If no gate at this index, no requirement
    | some ⟨R, cfg⟩ =>
        -- **2^R BOTTLENECK**: ALL R bits of digest must match configuration
        -- This creates the information-theoretic barrier: adversary must explore
        -- 2^R configurations to find one with matching digest
        let digest := r.gateDigests.get ⟨i, h⟩
        -- Check ALL R bits match the configuration (not just parity!)
        digest.size ≥ R ∧
        ∀ (j : Fin R), digest[j.val]? = some (CutConstraint.extractBit cfg j)

/-! ## Assignment-Derived World (Scaffold)

We provide a pure assignment-derived configuration function over the DAG, to
serve as the planted "world" when transporting to planted instances. This avoids
any dependence on Plant.lean and can be cast into CutWorld for planted L via
the usual R equality (both use `R_of φ numGates`).
-/

/-- Emergent configuration at a vertex, computed purely from assignment.

    This mirrors the second component returned by `emergentConfigAtGate` but is
    defined for any vertex, not just FG gates. -/
noncomputable def cfgAtVertex
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment)
    (v : Fin (lstarStructureFromCNF φ h_nvars_pos numGates).dag.n) :
    Fin (2^((lstarStructureFromCNF φ h_nvars_pos numGates).R v)) :=
  let L := lstarStructureFromCNF φ h_nvars_pos numGates
  let Rv := L.R v
  have h_cap : Rv ≤ L.seedWidth v := by
    have h := L.seedWidth_ok v
    exact Nat.le_trans (Nat.le_add_left _ _) h
  let s := computeSeedAtVertex φ h_nvars_pos numGates a v
  emergentBitsToConfig (extractEmergentBits s Rv h_cap)

/-- Pure cut‑assignment from `a` over the DAG of `lstarStructureFromCNF φ numGates`.

    This can be transported (by casting along R equalities) to a `CutWorld` for
    a planted instance `plant_n n φ r`. -/
noncomputable def cutAssignmentFrom
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment)
    (C : Finset (Fin (lstarStructureFromCNF φ h_nvars_pos numGates).dag.n)) :
    (∀ v : Fin (lstarStructureFromCNF φ h_nvars_pos numGates).dag.n,
      v ∈ C → Fin (2^((lstarStructureFromCNF φ h_nvars_pos numGates).R v))) :=
  fun v _ => cfgAtVertex φ h_nvars_pos numGates a v

/-! ## No Foundational Axioms (Clean Architecture)

**Architecture**: Axiom-free infrastructure with localized assumptions.

**Key components**:
- EmergentConfig: Pure structural lemmas (no axioms)
- VerifiedWitness: Uses `digestsFromAssignment` directly (pure function)
- TMToExecutionPrefix: Uses witness's configs (no axioms)
- Security.lean: Hardness assumption localized where needed (OWF proof)

**Key insight**: `digestsFromAssignment` is a **pure function** of the assignment.
It doesn't reference planted randomness r at all - just computes configs → parities.

**Design principles**:
1. **No axioms in infrastructure** - all structural lemmas are proven
2. **Cleaner separation** - assumptions live where they're used (Security.lean)
3. **Honest scoping** - don't claim uniqueness in layers that don't need it
4. **Matches paper** - paper assumes uniqueness for security proof, not as structural property

**Assumption placement**:
- **Not in infrastructure** - EmergentConfig is axiom-free
- **In Security.lean** - where hardness claim is actually made
- **Localized properly** - assumption appears exactly once, where it's used

**Achievement**: Zero axioms in EmergentConfig/VerifiedWitness/TMToExecutionPrefix.
Infrastructure is purely constructive. Security assumption lives in Security.lean.
-/

/-! ## Vertex-Indexed API (Wrapper for DAG Traversal) -/

/-- **Emergent configuration at a DAG vertex** (wrapper for vertex-centric code).

    **Purpose**: Convenience wrapper for code iterating over DAG vertices.
    Takes vertex index directly instead of gate index.

    **Semantics**:
    - For gate vertices (clause_start ≤ v < clause_start + numGates):
      Returns emergent config at that vertex
    - For non-gate vertices: Returns none

    **Relationship to emergentConfigAtGate**:
    When v is a gate vertex at index (clause_start + g), this returns
    emergentConfigAtGate φ numGates a g.

    **Use case**: AcceptanceUniqueness, world construction, any code that
    iterates over DAG.vertices rather than gate indices.

    **NO AXIOMS**: Pure wrapper, delegates to emergentConfigAtGate. -/
noncomputable def emergentConfigAtVertex
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (vertexIdx : Nat)
    : Option (Σ' R, Fin (2^R)) :=
  let clause_start := 1 + φ.nvars
  -- Check if vertexIdx is in the gate range
  if _h_range : clause_start ≤ vertexIdx ∧ vertexIdx < clause_start + numGates then
    -- Convert vertex index to gate index
    let gateIdx := vertexIdx - clause_start
    -- Call the gate-indexed API
    emergentConfigAtGate φ h_nvars_pos numGates a gateIdx
  else
    none

/-- **Relationship theorem**: emergentConfigAtVertex delegates to emergentConfigAtGate.

    **Statement**: For gate vertices, emergentConfigAtVertex returns exactly what
    emergentConfigAtGate returns for the corresponding gate index.

    **Proof**: Direct from definition (unfold + split). -/
theorem emergentConfigAtVertex_eq_atGate
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (vertexIdx : Nat)
    (h_range : 1 + φ.nvars ≤ vertexIdx ∧ vertexIdx < 1 + φ.nvars + numGates) :
    emergentConfigAtVertex φ h_nvars_pos numGates a vertexIdx =
      emergentConfigAtGate φ h_nvars_pos numGates a (vertexIdx - (1 + φ.nvars)) := by
  unfold emergentConfigAtVertex
  simp only [dif_pos h_range]

/-- **Key theorem**: The R component from emergentConfigAtVertex matches the vertex's R value.

    **Statement**: When emergentConfigAtVertex returns some ⟨R_v, cfg⟩ for vertex v,
    then R_v equals (lstarStructureFromCNF φ numGates).R ⟨vertexIdx, _⟩.

    **This solves AcceptanceUniqueness sorries 1-2**: The returned R value DIRECTLY
    matches L.R v when L's structure derives from lstarStructureFromCNF!

    **Proof strategy**:
    1. emergentConfigAtVertex delegates to emergentConfigAtGate
    2. emergentConfigAtGate internally computes vertex_idx = clause_start + gateIdx
    3. With our conversion gateIdx = vertexIdx - clause_start, we get vertex_idx = vertexIdx
    4. emergentConfigAtGate returns L.R ⟨vertex_idx, _⟩ by definition
    5. Therefore: R_v = L.R ⟨vertexIdx, _⟩ ✓

    **NO AXIOMS**: Pure definitional unfolding proof. -/
theorem emergentConfigAtVertex_R_component
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (vertexIdx : Nat)
    {R_v : Nat} {cfg : Fin (2^R_v)}
    (h_some : emergentConfigAtVertex φ h_nvars_pos numGates a vertexIdx = some ⟨R_v, cfg⟩) :
    let L := lstarStructureFromCNF φ h_nvars_pos numGates
    let clause_start := 1 + φ.nvars
    -- If vertexIdx is valid for L's DAG
    ∀ (h_valid : vertexIdx < L.dag.n),
      vertexIdx ≥ clause_start → vertexIdx < clause_start + numGates →
      R_v = L.R ⟨vertexIdx, h_valid⟩ := by
  -- Introduce let bindings from the goal
  intro L clause_start h_valid h_ge h_lt

  -- Establish range for emergentConfigAtVertex
  have h_range : clause_start ≤ vertexIdx ∧ vertexIdx < clause_start + numGates :=
    ⟨h_ge, h_lt⟩

  -- Use relationship theorem
  have h_eq := emergentConfigAtVertex_eq_atGate φ h_nvars_pos numGates a vertexIdx h_range
  rw [h_eq] at h_some

  -- Now h_some: emergentConfigAtGate φ numGates a (vertexIdx - clause_start) = some ⟨R_v, cfg⟩

  -- Unfold emergentConfigAtGate to see what it returns
  unfold emergentConfigAtGate at h_some

  -- The function computes vertex_idx = clause_start + gateIdx
  let gateIdx := vertexIdx - clause_start
  have h_gateIdx : gateIdx = vertexIdx - clause_start := rfl

  -- Show gateIdx < numGates
  have h_gate_bound : gateIdx < numGates := by
    show vertexIdx - clause_start < numGates
    omega

  -- Note: After unfolding, emergentConfigAtGate has if conditions that will be evaluated
  -- No simplification needed - the match will handle the structure directly

  -- Now compute vertex_idx = clause_start + gateIdx = clause_start + (vertexIdx - clause_start) = vertexIdx
  have h_vertex_idx : clause_start + gateIdx = vertexIdx := by omega

  -- Show this equals vertexIdx, which is < L.dag.n
  have h_vertex_valid : clause_start + gateIdx < L.dag.n := by
    rw [h_vertex_idx]
    exact h_valid

  -- Now inside the if branches, the function constructs v : Fin L.dag.n := ⟨vertex_idx, _⟩
  -- and returns some ⟨L.R v, cfg⟩

  -- The value v.val = vertex_idx = vertexIdx
  -- So L.R v = L.R ⟨vertexIdx, _⟩

  -- The returned R value comes from let R_v := L.R v in the definition
  -- Need to extract this from the some ⟨..., ...⟩ pattern

  -- After the two dif_pos simplifications, we're inside the innermost if
  let v : Fin L.dag.n := ⟨clause_start + gateIdx, h_vertex_valid⟩

  -- Show v.val = vertexIdx
  have h_v_val : v.val = vertexIdx := by
    simp only [v]
    exact h_vertex_idx

  -- The definition returns some ⟨L.R v, ...⟩ when the capacity check passes
  -- We need to show the capacity check passes
  have h_cap : L.R v ≤ L.seedWidth v := by
    have h := L.seedWidth_ok v
    exact Nat.le_trans (Nat.le_add_left _ _) h

  -- Note: h_cap proves capacity constraint, but no simplification needed
  -- The match structure will handle evaluation directly

  -- After unfolding, h_some has structure:
  -- (let ... in if ... then if ... then if ... then some ⟨..., ...⟩ else none else none else none) = some ⟨R_v, cfg⟩

  -- Beta-reduce all the let bindings first
  dsimp only at h_some

  -- Now split on all the if conditions
  split_ifs at h_some with h_g

  · -- Case: all three conditions true
    -- h_some now has form: some ⟨_, _⟩ = some ⟨R_v, cfg⟩
    -- Use Option.some_inj to get PSigma equality
    rw [Option.some_inj] at h_some
    -- Now h_some is a PSigma equality: ⟨L.R ⟨..., ...⟩, ...⟩ = ⟨R_v, cfg⟩
    -- Extract the first component (the R value) using PSigma.fst
    have h_fst := congrArg PSigma.fst h_some
    simp only at h_fst
    -- Now h_fst : L.R ⟨..., ...⟩ = R_v
    -- We need to show: R_v = L.R ⟨vertexIdx, h_valid⟩
    rw [← h_fst]
    -- Both Fin values should be equal (same .val by arithmetic)
    congr 1
    apply Fin.ext
    -- Simplify the .val comparison
    simp only
    -- 1 + φ.nvars + (vertexIdx - (1 + φ.nvars)) = vertexIdx when vertexIdx ≥ 1 + φ.nvars
    omega

  -- Cases 2-8: some if-condition is false, so LHS = none ≠ some ⟨R_v, cfg⟩
  all_goals (contradiction)

/-! ## Axiom Verification

These definitions and theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms emergentConfigAtGate
#print axioms emergentConfigAtGate_some_implies_gateIndex_bound
#print axioms WellFormedRandomness
#print axioms cfgAtVertex
#print axioms cutAssignmentFrom
#print axioms emergentConfigAtVertex
#print axioms emergentConfigAtVertex_eq_atGate
#print axioms emergentConfigAtVertex_R_component

end LStar.StructuralOWF.Foundations
