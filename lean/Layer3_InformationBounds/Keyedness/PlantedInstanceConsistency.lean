import Layer2_StructuralOWF.Plant.PlantCore
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer3_InformationBounds.SegmentReduction.StructuralLowerBound
import Layer3_InformationBounds.Support.SeedSemantics
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig  -- Import for emergentConfigAtGate and WellFormedRandomness
import Layer3_InformationBounds.WorldCommit.CutWorlds  -- For CutWorld definition
import Layer1_Construction.Core.InstanceOps

/-! ## PlantedInstanceConsistency: Well-Formed Randomness (Non-Circular)

**Architecture**: Non-circular well-formedness via pure functions.

The public gateDigest field is a constant placeholder independent of the witness,
ensuring the planted instance reveals no assignment information. Parity consistency
is tracked internally via WellFormedRandomness on the input randomness r.

**Pure function separation**:
```
emergentConfigAtGate φ a i : Pure function computing emergent config from φ and a
WellFormedRandomness φ r   : Verifies r.gateDigests match computed parities
wellformed_randomness_exists : Constructive existence proof
worldFromWitness            : Builds CutWorld from witness using internal parity data
```

**Key property**: Emergent configs are defined purely from φ + a (no plant_n dependency),
breaking circular definitions. The public instance structure is independent of the witness.

**Trust Boundary**: Proven theorems (no custom axioms).

**Paper**: §7 "A1-A5 Construction", §8 "Planted Randomness"

See Layer3_InformationBounds/Layer3_README.md for planted instance consistency and well-formedness.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF LStar.StructuralOWF.Foundations

/-! ## Pure Emergent Configuration Functions

**NOTE**: The definitions `emergentConfigAtGate` and `WellFormedRandomness` are imported
from `LStar.StructuralOWF.Foundations.EmergentConfig`. This module proves theorems about planted
instances using those pure functions. -/

/-! ## Plant Preserves Well-Formedness -/

/-- **HELPER LEMMA**: Extract R value from emergentConfigAtGate result.

    **Purpose**: When emergentConfigAtGate returns some ⟨R, cfg⟩, prove that R equals
    R_of φ numGates gateIndex definitionally.

    **Why needed**: The returned R is computed inside emergentConfigAtGate's implementation,
    but we need to connect it to the definitional R_of to prove type equalities. -/
lemma emergentConfigAtGate_R_component
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : Assignment) (gateIndex : Nat)
    (R_ret : Nat) (cfg_ret : Fin (2^R_ret))
    (h_ret : emergentConfigAtGate φ h_nvars_pos numGates a gateIndex = some ⟨R_ret, cfg_ret⟩)
    : R_ret = R_of φ numGates (1 + φ.nvars + gateIndex) := by
  -- Unfold emergentConfigAtGate to expose the computation
  unfold emergentConfigAtGate at h_ret
  -- Simplify let-bindings in the hypothesis
  simp only at h_ret
  -- Now split on the if-conditions
  split at h_ret
  · -- Case: gateIndex < L.dag.n (valid index)
    rename_i h_valid
    -- Now split on the vertex validity condition
    split at h_ret
    · -- Case: vertex_idx < L.dag.n (vertex in DAG)
      -- Now split on the capacity condition
      split at h_ret
      · -- Case: R_v ≤ seedWidth (capacity OK), returns some ⟨R_v, cfg⟩
        -- Inject through Option.some to get Sigma equality
        injection h_ret with h_sigma_eq
        -- h_sigma_eq : ⟨L.R v, emergentBitsToConfig ...⟩ = ⟨R_ret, cfg_ret⟩
        -- Goal: R_ret = R_of φ numGates (1 + φ.nvars + gateIndex)
        --
        -- Strategy: use cases on the Sigma equality to get R_ret = L.R v definitionally
        cases h_sigma_eq
        -- After cases, R_ret := L.R v definitionally
        -- Goal: (lstarStructureFromCNF φ numGates).R ⟨1 + φ.nvars + gateIndex, ...⟩ = R_of φ numGates (1 + φ.nvars + gateIndex)
        unfold lstarStructureFromCNF
        rfl  -- Definitional: R := fun v => R_of φ numGates v.val
      · -- Case: capacity condition fails, returns none
        contradiction  -- h_ret : none = some ..., impossible
    · -- Case: vertex_idx >= L.dag.n (vertex not in DAG), returns none
      contradiction  -- h_ret : none = some ..., impossible
  · -- Case: gateIndex >= numGates (invalid gate index), returns none
    contradiction  -- h_ret : none = some ..., impossible

/-- **LEMMA**: For valid FG gate indices, emergentConfigAtGate always returns some.

    **Impact**: This eliminates the none case in plant_preserves_wellformedness
    by proving it's impossible when the index is valid.

    **Proof**: Both plant_n and lstarStructureFromCNF use build3SATReductionDAG φ,
    so their dag.n values are definitionally equal. Valid FG gates satisfy both
    index bounds and capacity constraints (R_v ≤ seedWidth_v). -/
lemma emergentConfigAtGate_some_of_valid_fg_gate
    (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (v : {v // (plant_n n φ r h_nvars h_dgLen).fg.gateReq v}) :
    ∃ R_val cfg, emergentConfigAtGate φ (by omega : φ.nvars > 0) r.gateDigests.length r.assignment (v.val.val - (1 + φ.nvars)) = some ⟨R_val, cfg⟩ := by
  -- Extract gate requirement: v is an FG gate in range [1+φ.nvars, 1+φ.nvars+numGates)
  have h_prop := v.property
  unfold plant_n at h_prop
  simp at h_prop
  -- h_prop : 1 + φ.nvars ≤ v.val.val ∧ v.val.val < 1 + φ.nvars + r.gateDigests.length

  -- Compute gate-relative index
  let clause_start := 1 + φ.nvars
  let gate_idx := v.val.val - clause_start

  -- Prove gate_idx < numGates
  have h_gate_idx : gate_idx < r.gateDigests.length := by
    -- From h_prop: clause_start ≤ v.val.val < clause_start + numGates
    -- Therefore: v.val.val - clause_start < numGates
    omega

  -- Key insight: DAG sizes match
  have h_dag_eq : (plant_n n φ r h_nvars h_dgLen).dag.n = (lstarStructureFromCNF φ (by omega : φ.nvars > 0) r.gateDigests.length).dag.n := by
    unfold plant_n lstarStructureFromCNF build3SATReductionDAG
    rfl

  -- v.val.val is valid in the DAG
  have h_vertex_valid : v.val.val < (lstarStructureFromCNF φ (by omega : φ.nvars > 0) r.gateDigests.length).dag.n := by
    rw [← h_dag_eq]
    exact v.val.isLt

  -- Show the equality by structural reasoning
  -- by splitting on the conditionals in emergentConfigAtGate and proving each branch

  -- First, establish the pure L* structure and key indices
  let L := lstarStructureFromCNF φ (by omega : φ.nvars > 0) r.gateDigests.length

  -- Show vertex_idx = clause_start + gate_idx = v.val.val
  have h_vertex_eq : clause_start + gate_idx = v.val.val := by
    omega

  -- Therefore vertex_idx < L.dag.n
  have h_vertex_in_dag : clause_start + gate_idx < L.dag.n := by
    rw [h_vertex_eq]
    exact h_vertex_valid

  -- Define the vertex index
  let v_idx : Fin L.dag.n := ⟨clause_start + gate_idx, h_vertex_in_dag⟩

  -- Show capacity condition holds
  have h_cap : L.R v_idx ≤ L.seedWidth v_idx := by
    have h_seedWidth_ok := L.seedWidth_ok v_idx
    calc L.R v_idx
        ≤ (∑ u ∈ L.dag.parents v_idx, L.seedWidth u) + L.R v_idx := Nat.le_add_left _ _
      _ ≤ L.seedWidth v_idx := h_seedWidth_ok

  -- Provide witnesses
  use L.R v_idx
  use emergentBitsToConfig (extractEmergentBits (computeSeedAtVertex φ (by omega : φ.nvars > 0) r.gateDigests.length r.assignment v_idx) (L.R v_idx) h_cap)

  -- Show the equality by unfolding and rewriting conditionals explicitly
  unfold emergentConfigAtGate

  -- Use dif_pos to rewrite each conditional
  rw [dif_pos h_gate_idx]  -- First if: gateIndex < numGates
  rw [dif_pos h_vertex_in_dag]  -- Second if: vertex_idx < L.dag.n
  rw [dif_pos h_cap]  -- Third if: R_v ≤ seedWidth v
  -- After these rewrites, the goal is solved (equality holds)

/-! ## Constructive Existence -/

/-- **THEOREM**: Well-formed randomness exists and is CONSTRUCTIBLE.

    **Construction** (~100-140 lines):
    ```lean
    Given: φ (CNF formula), a (satisfying assignment), numGates, dgLen
    Build: r : Randomness where WellFormedRandomness φ r holds

    Construction:
    1. Set r.assignment := a
    2. For each gate index i in 0..numGates:
       - Compute cfg := emergentConfigAtGate φ a i  (pure function!)
       - Compute parity_bit := fgDigestBit cfg
       - Set r.gateDigests[i] := encode_as_vector(parity_bit)
    3. Return r

    Verification:
    - By construction, r.gateDigests[i] = parity(emergentConfigAtGate φ a i)
    - This is exactly WellFormedRandomness φ r!
    - QED
    ```

    **Key Property**: This is CONSTRUCTIVE! We BUILD well-formed randomness,
    we don't just assume it exists.

    **Impact**: Eliminates axiom "OWF uses well-formed randomness" - now it's
    "OWF constructs well-formed randomness via this algorithm". -/
theorem wellformed_randomness_exists
    (φ : CNF) (a : Assignment)
    (h_sat : φ.satisfies a)
    (numGates : Nat)
    (_h_pos : 0 < numGates)
    (h_single : numGates = 1)  -- Single-gate constraint
    (h_clauses : φ.clauses.length ≥ numGates)  -- Clause count requirement for FG gate placement
    (dgLen : Nat)
    (h_dgLen_pos : dgLen > 0)
    (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2)  -- dgLen ≥ R for FG gates (QP profile)
    : ∃ r : Randomness, WellFormedRandomness φ r := by
  -- Step 1: Construct r.gateDigests by computing parity for each gate
  -- Pass numGates to emergentConfigAtGate for type consistency
  let gateDigests : List (Vector Bool dgLen) :=
    List.ofFn (fun (i : Fin numGates) =>
      match emergentConfigAtGate φ φ.nvars_pos numGates a i.val with
      | none =>
          -- No config at this index - use default all-false
          Vector.replicate dgLen false
      | some ⟨R, cfg⟩ =>
          -- Build dgLen-bit vector with ALL R bits from cfg
          -- For j < R: extract bit j from cfg
          -- For j >= R: false
          Vector.ofFn (fun (j : Fin dgLen) =>
            if h_j : j.val < R then
              CutConstraint.extractBit cfg ⟨j.val, h_j⟩
            else
              false))

  -- Step 2: Build the Randomness structure
  have h_single_gate : gateDigests.length = 1 := by
    simp [gateDigests, List.length_ofFn]
    exact h_single

  let r : Randomness := {
    dgLen := dgLen
    h_dgLen_pos := h_dgLen_pos
    assignment := a
    gateDigests := gateDigests
    structuralBits := List.replicate 64 false  -- Satisfy salt requirement (≥64 bits)
    h_single_gate := h_single_gate
    h_sufficient_salts := by simp only [List.length_replicate]; decide
  }

  -- Step 3: Prove WellFormedRandomness φ r
  use r

  -- WellFormedRandomness unfolds with let binding
  -- Unfold and provide components directly
  unfold WellFormedRandomness
  simp only []

  -- Now prove: φ.satisfies r.assignment ∧ (φ.clauses.length ≥ r.gateDigests.length ∧ ∀ ...)
  constructor
  · exact h_sat  -- P1: φ.satisfies r.assignment (r.assignment = a by construction)
  constructor
  · -- P2: φ.clauses.length ≥ r.gateDigests.length
    -- h_clauses : φ.clauses.length ≥ numGates, and r.gateDigests.length = numGates by construction
    have h_len : r.gateDigests.length = numGates := by simp only [r, gateDigests, List.length_ofFn, h_single]
    rw [h_len]
    exact h_clauses
  · -- P3: ∀ (i : Nat) (h : i < r.gateDigests.length), ...
    intro i h_i
    -- Establish definitional equalities
    have h_len_eq : r.gateDigests.length = numGates := by simp [r, gateDigests, List.length_ofFn]
    have h_assign_eq : r.assignment = a := rfl

    -- Rewrite using length equality
    have h_i_bound : i < numGates := by rw [← h_len_eq]; exact h_i

    -- Pattern match on emergentConfigAtGate
    cases h_cfg : emergentConfigAtGate φ φ.nvars_pos numGates a i with
    | none =>
        -- When emergentConfigAtGate returns none, the requirement is True
        simp only [h_len_eq, h_assign_eq, h_cfg]
    | some cfg_with_R =>
        obtain ⟨R_val, cfg⟩ := cfg_with_R
        -- Prove r.gateDigests[i] matches construction with ALL R bits
        have h_get : r.gateDigests[i] =
            Vector.ofFn (fun (j : Fin dgLen) =>
              if h_j : j.val < R_val then CutConstraint.extractBit cfg ⟨j.val, h_j⟩ else false) := by
          simp only [r, gateDigests]
          simp only [List.getElem_ofFn, h_cfg]

        -- Show the size is dgLen
        have h_digest_size : (r.gateDigests.get ⟨i, h_i⟩).size = dgLen := by
          simp only [r, gateDigests, List.getElem_ofFn]

        -- Rewrite goal with h_cfg to get the R_val and cfg into scope
        simp only [h_len_eq, h_assign_eq, h_cfg]

        -- Use emergentConfigAtGate_R_component to show R_val = R_of φ numGates (1 + φ.nvars + i)
        have h_R_comp := emergentConfigAtGate_R_component φ φ.nvars_pos numGates a i R_val cfg h_cfg
        -- h_R_comp : R_val = R_of φ numGates (1 + φ.nvars + i)

        -- For FG gates, R_of gives (Nat.log 2 φ.nvars)^2
        -- Gate i is at vertex (1 + φ.nvars + i) which is in FG range when i < numGates
        have h_R_eq : Foundations.R_of φ numGates (1 + φ.nvars + i) = (Nat.log 2 φ.nvars)^2 := by
          unfold Foundations.R_of
          -- Show FG gate condition holds
          have h_fg_left : 1 + φ.nvars ≤ 1 + φ.nvars + i := by omega
          have h_fg_right : 1 + φ.nvars + i < min (1 + φ.nvars + numGates) (1 + φ.nvars + φ.clauses.length) := by
            have h_nc : numGates ≤ φ.clauses.length := h_clauses
            simp only [Nat.lt_min]; omega
          simp only [h_fg_left, h_fg_right, and_self, ite_true]

        -- Now R_val = (Nat.log 2 φ.nvars)^2 ≤ dgLen
        have h_R_val_eq : R_val = (Nat.log 2 φ.nvars)^2 := by rw [h_R_comp, h_R_eq]
        have h_dgLen_ge_R_val : dgLen ≥ R_val := by rw [h_R_val_eq]; exact h_dgLen_ge_R

        -- Goal is: digest.size ≥ R_val ∧ ∀ (j : Fin R_val), digest[j.val]? = some (extractBit cfg j)
        constructor
        · -- digest.size ≥ R_val
          -- digest = r.gateDigests[i] which has size dgLen ≥ R_val
          calc (r.gateDigests.get ⟨i, h_i⟩).size = dgLen := h_digest_size
            _ ≥ R_val := h_dgLen_ge_R_val
        · -- ∀ (j : Fin R_val), digest[j.val]? = some (extractBit cfg j)
          intro j
          -- digest = Vector.ofFn ... at position j should give extractBit cfg j
          -- First connect r.gateDigests.get to r.gateDigests[i]
          have h_get' : r.gateDigests.get ⟨i, h_i⟩ = r.gateDigests[i] := rfl
          rw [h_get', h_get]
          -- The Vector.ofFn's toList is List.ofFn, and indexing returns the function value
          have h_j_lt_dgLen : j.val < dgLen := by omega
          -- Goal: (Vector.ofFn f)[j.val]? = some (extractBit cfg j)
          rw [Vector.getElem?_ofFn]
          -- Now split on whether j.val < dgLen
          simp only [h_j_lt_dgLen, ↓reduceDIte]
          -- Goal: if j.val < R_val then ... else false = extractBit cfg j
          simp only [j.isLt, ↓reduceDIte]

/-- **COROLLARY**: OWF uses constructible well-formed randomness. -/
noncomputable def owf_randomness_for (φ : CNF) (a : Assignment) (h_sat : φ.satisfies a)
    (numGates : Nat) (h_pos : 0 < numGates) (h_single : numGates = 1) (h_clauses : φ.clauses.length ≥ numGates)
    (dgLen : Nat) (h_dgLen_pos : dgLen > 0) (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2) : Randomness :=
  Classical.choose (wellformed_randomness_exists φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R)

theorem owf_randomness_is_wellformed
    (φ : CNF) (a : Assignment) (h_sat : φ.satisfies a)
    (numGates : Nat) (h_pos : 0 < numGates) (h_single : numGates = 1) (h_clauses : φ.clauses.length ≥ numGates)
    (dgLen : Nat) (h_dgLen_pos : dgLen > 0) (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2)
    : WellFormedRandomness φ (owf_randomness_for φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R) := by
  unfold owf_randomness_for
  exact Classical.choose_spec (wellformed_randomness_exists φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R)

/-! ## Summary: Architectural Solution

**Architecture**: Non-circular well-formedness via pure functions.
- `emergentConfigAtGate φ a gateIndex`: Computes emergent config from φ and a only
- `WellFormedRandomness φ r`: Verifies parity consistency on internal randomness
- `wellformed_randomness_exists`: Constructive proof of existence
- `worldFromWitness`: Builds CutWorld from witness using internal parity data

**Key properties**:
- Public gateDigest is constant (zeros), independent of the witness
- Parity consistency is maintained internally via WellFormedRandomness
- Injectivity derives from A2 (seed encoding), not from public instance structure

**Result**: Sound architecture with explicit semantic bridges and no circular dependencies.
-/

/-! ## Witness → CutWorld Construction

**PURPOSE**: Build a CutWorld from a witness for planted FG instances.

This is the "witness world" ω_w that satisfies all constraints extracted from
the witness (used to prove FeasibleUnder is nonempty at acceptance).

**Architecture**: This belongs HERE (planted instance properties), not in TMToExecutionPrefix
(which is just an integration layer). -/

/-- **HELPER**: For planted FG gates, clause_start ≤ v.val.

    This extracts the lower bound from plant_n's gateReq definition. -/
lemma planted_fg_gate_ge_clause_start
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_L_eq : L = plant_n n φ r h_nvars h_dgLen)
    (h_gate : L.fg.gateReq v = true)
    : 1 + φ.nvars ≤ v.val := by
  -- Use subst to replace L (handles dependent types correctly)
  subst h_L_eq
  -- Now L is definitionally plant_n n φ r h_nvars h_dgLen everywhere, including in h_gate
  -- h_gate : (plant_n n φ r h_nvars h_dgLen).fg.gateReq v = true
  unfold plant_n at h_gate
  simp only [decide_eq_true_eq] at h_gate
  -- h_gate : 1 + φ.nvars ≤ v.val ∧ v.val < 1 + φ.nvars + r.gateDigests.length
  exact h_gate.1

/-- **HELPER**: For planted instances, L.R v = R_of φ numGates v.val.

    This connects the planted instance's R function to R_of. -/
lemma planted_R_eq_R_of
    (L : LStarInstanceFG)
    (v : Fin L.dag.n)
    (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_L_eq : L = plant_n n φ r h_nvars h_dgLen)
    : L.R v = R_of φ r.gateDigests.length v.val := by
  -- Use subst to replace L (handles dependent types correctly)
  subst h_L_eq
  -- Now L is definitionally plant_n n φ r h_nvars h_dgLen everywhere
  -- Goal: (plant_n n φ r h_nvars h_dgLen).R v = R_of φ r.gateDigests.length v.val
  unfold plant_n
  rfl  -- Definitional from plant_n.R := fun v => R_of φ numGates v.val

/-- **Construct CutWorld from witness** for planted FG instances.

    **Mathematical content**: For planted L = plant_n n φ r, given witness w,
    construct the unique CutWorld corresponding to w's emergent configurations.

    **Implementation**:
    - For each node v ∈ C, compute gate index g := v.val - clause_start
    - Call emergentConfigAtGate φ numGates w.assignment g to get config
    - Cast config to Fin (2^(L.R v)) using planted R equality
    - For non-FG nodes or none case, default to 0

    **Usage**: Proves FeasibleUnder nonempty (witness world always satisfies extracted constraints).

    **Why here**: Depends on planted structure (emergentConfigAtGate, planted_R_eq),
    not on TM execution semantics. -/
noncomputable def worldFromWitness
    (L : LStarInstanceFG)
    (w : Witness)
    (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_L_eq : L = plant_n n φ r h_nvars h_dgLen)
    (_h_wf : WellFormedRandomness φ r)
    (C : Finset (Fin L.dag.n))
    : CutWorld L C :=
  let numGates := r.gateDigests.length
  let clause_start := 1 + φ.nvars

  { assignment := fun v (h_in_C : v ∈ C) =>
      -- Compute gate-relative index (reverse of: v_nat = clause_start + g)
      let g := v.val - clause_start
      match hx : emergentConfigAtGate φ (by omega : φ.nvars > 0) numGates w.assignment g with
      | none =>
          -- No emergent config (shouldn't happen for well-formed FG gates, but we need totality)
          (0 : Fin (2^(L.R v)))
      | some ⟨R, cfg⟩ =>
          -- Check if this is an FG gate (if so, cast cfg appropriately)
          if h_gate : L.fg.gateReq v then
            -- For FG gates in planted instances, R = L.R v (proven by emergentConfigAtGate_R_component)
            -- We need the gateIdx as Fin numGates for the lemma, but we know g < numGates
            -- from FG structure (gate indices are in range [0, numGates))
            if h_g_valid : g < numGates then
              let gateIdx : Fin numGates := ⟨g, h_g_valid⟩
              -- Extract the gateReq constraint: clause_start ≤ v.val
              have h_v_ge_clause : clause_start ≤ v.val :=
                planted_fg_gate_ge_clause_start L v n φ r h_nvars h_dgLen h_L_eq h_gate
              have h_v_valid : clause_start + g < L.dag.n := by
                -- v.val < L.dag.n (from v : Fin L.dag.n)
                -- clause_start + g = v.val (by definition of g and h_v_ge_clause)
                calc clause_start + g
                    = v.val := by omega  -- g := v.val - clause_start, and clause_start ≤ v.val
                  _ < L.dag.n := v.isLt
              have hR : R = L.R v := by
                -- emergentConfigAtGate_R_component gives: R = R_of φ numGates (1 + φ.nvars + g)
                -- We need: R = L.R v
                -- Connection: v.val = clause_start + g = 1 + φ.nvars + g (by definition)
                have h_R_component := emergentConfigAtGate_R_component φ (by omega : φ.nvars > 0) numGates w.assignment g R cfg hx
                -- h_R_component : R = R_of φ numGates (1 + φ.nvars + g)
                -- For planted instances, L.R v = R_of φ numGates v.val
                -- And v.val = clause_start + g = 1 + φ.nvars + g
                calc R
                    = R_of φ numGates (1 + φ.nvars + g) := h_R_component
                  _ = R_of φ numGates (clause_start + g) := rfl  -- clause_start := 1 + φ.nvars
                  _ = R_of φ numGates v.val := by
                      -- v.val = clause_start + g
                      congr 1
                      omega  -- from h_v_ge_clause and g := v.val - clause_start
                  _ = L.R v := (planted_R_eq_R_of L v n φ r h_nvars h_dgLen h_L_eq).symm
              -- Cast cfg : Fin (2^R) to Fin (2^(L.R v))
              hR ▸ cfg
            else
              -- g >= numGates (shouldn't happen for FG gates, but handle for totality)
              (0 : Fin (2^(L.R v)))
          else
            -- Non-FG gate: default assignment
            (0 : Fin (2^(L.R v)))
  }

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms WellFormedRandomness
#print axioms emergentConfigAtGate
#print axioms wellformed_randomness_exists
#print axioms worldFromWitness

end LStar.StructuralOWF.Foundations
