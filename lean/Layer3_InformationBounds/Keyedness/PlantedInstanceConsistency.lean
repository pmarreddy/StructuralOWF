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
WellFormedRandomness φ r   : Verifies ALL R bits of r.gateDigests match computed configs
wellformed_randomness_exists : Constructive existence proof
worldFromWitness            : Builds CutWorld from witness using internal parity data
```

**Key property**: Emergent configs are defined purely from φ + a,
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
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : AssignmentInf) (gateIndex : Nat)
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
       - Extract ALL R bits from cfg via CutConstraint.extractBit
       - Set r.gateDigests[i] := vector of ALL R bits (identity digest)
    3. Return r

    Verification:
    - By construction, r.gateDigests[i] contains ALL R bits of emergentConfigAtGate φ a i
    - This is exactly WellFormedRandomness φ r (which requires ALL R bits to match)!
    - QED
    ```

    **Key Property**: This is CONSTRUCTIVE! We BUILD well-formed randomness,
    we don't just assume it exists.

    **Impact**: Eliminates axiom "OWF uses well-formed randomness" - now it's
    "OWF constructs well-formed randomness via this algorithm". -/
theorem wellformed_randomness_exists
    (φ : CNF) (a : Assignment φ.nvars)
    (h_sat : φ.satisfies a.extend)
    (numGates : Nat)
    (_h_pos : 0 < numGates)
    (h_single : numGates = 1)  -- Single-gate constraint
    (h_clauses : φ.clauses.length ≥ numGates)  -- Clause count requirement for FG gate placement
    (dgLen : Nat)
    (h_dgLen_pos : dgLen > 0)
    (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2)  -- dgLen ≥ R for FG gates (QP profile)
    : ∃ r : Randomness φ.nvars, WellFormedRandomness φ r := by
  -- Step 1: Construct r.gateDigests by extracting ALL R bits for each gate
  -- Pass numGates to emergentConfigAtGate for type consistency
  let gateDigests : List (Vector Bool dgLen) :=
    List.ofFn (fun (i : Fin numGates) =>
      match emergentConfigAtGate φ φ.nvars_pos numGates a.extend i.val with
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

  let r : Randomness φ.nvars := {
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

  -- Now prove: φ.satisfies r.assignmentInf ∧ (φ.clauses.length ≥ r.gateDigests.length ∧ ∀ ...)
  constructor
  · -- P1: φ.satisfies r.assignmentInf (r.assignmentInf = a.extend by construction)
    -- r.assignment = a, so r.assignmentInf = a.extend
    have h_eq : r.assignmentInf = a.extend := rfl
    rw [h_eq]
    exact h_sat
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
    have h_assignInf_eq : r.assignmentInf = a.extend := rfl

    -- Rewrite using length equality
    have h_i_bound : i < numGates := by rw [← h_len_eq]; exact h_i

    -- Pattern match on emergentConfigAtGate
    -- r.assignmentInf = a.extend by construction
    cases h_cfg : emergentConfigAtGate φ φ.nvars_pos numGates r.assignmentInf i with
    | none =>
        -- When emergentConfigAtGate returns none, the requirement is True
        simp only [h_len_eq, h_cfg]
    | some cfg_with_R =>
        obtain ⟨R_val, cfg⟩ := cfg_with_R
        -- Prove r.gateDigests[i] matches construction with ALL R bits
        have h_get : r.gateDigests[i] =
            Vector.ofFn (fun (j : Fin dgLen) =>
              if h_j : j.val < R_val then CutConstraint.extractBit cfg ⟨j.val, h_j⟩ else false) := by
          simp only [r, gateDigests]
          simp only [List.getElem_ofFn]
          -- Rewrite using h_assignInf_eq to connect r.assignmentInf and a.extend
          rw [h_assignInf_eq] at h_cfg
          rw [h_cfg]

        -- Show the size is dgLen
        have h_digest_size : (r.gateDigests.get ⟨i, h_i⟩).size = dgLen := by
          simp only [r, gateDigests, List.getElem_ofFn]

        -- Rewrite goal with h_cfg to get the R_val and cfg into scope
        simp only [h_len_eq, h_cfg]

        -- Use emergentConfigAtGate_R_component to show R_val = R_of φ numGates (1 + φ.nvars + i)
        have h_R_comp := emergentConfigAtGate_R_component φ φ.nvars_pos numGates r.assignmentInf i R_val cfg h_cfg
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
noncomputable def owf_randomness_for (φ : CNF) (a : Assignment φ.nvars) (h_sat : φ.satisfies a.extend)
    (numGates : Nat) (h_pos : 0 < numGates) (h_single : numGates = 1) (h_clauses : φ.clauses.length ≥ numGates)
    (dgLen : Nat) (h_dgLen_pos : dgLen > 0) (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2) : Randomness φ.nvars :=
  Classical.choose (wellformed_randomness_exists φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R)

theorem owf_randomness_is_wellformed
    (φ : CNF) (a : Assignment φ.nvars) (h_sat : φ.satisfies a.extend)
    (numGates : Nat) (h_pos : 0 < numGates) (h_single : numGates = 1) (h_clauses : φ.clauses.length ≥ numGates)
    (dgLen : Nat) (h_dgLen_pos : dgLen > 0) (h_dgLen_ge_R : dgLen ≥ (Nat.log 2 φ.nvars)^2)
    : WellFormedRandomness φ (owf_randomness_for φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R) := by
  unfold owf_randomness_for
  exact Classical.choose_spec (wellformed_randomness_exists φ a h_sat numGates h_pos h_single h_clauses dgLen h_dgLen_pos h_dgLen_ge_R)

/-! ## Summary: Architectural Solution

**Architecture**: Non-circular well-formedness via pure functions.
- `emergentConfigAtGate φ a gateIndex`: Computes emergent config from φ and a only
- `WellFormedRandomness φ r`: Verifies ALL R bits match emergent configs (identity digest)
- `wellformed_randomness_exists`: Constructive proof of existence
- `worldFromWitness_flat`: Builds CutWorld from witness (see PlantExponential.lean)

**Key properties**:
- Public gateDigest is constant (zeros), independent of the witness
- Parity consistency is maintained internally via WellFormedRandomness
- Injectivity derives from A2 (seed encoding), not from public instance structure

**Result**: Sound architecture with explicit semantic bridges and no circular dependencies.

**Note**: For planted instance helpers (worldFromWitness_flat, planted_fg_gate_ge_clause_start_flat,
planted_R_eq_R_of_flat), see Layer2_StructuralOWF/Plant/PlantExponential.lean which provides
these for the exponential (plant_flat) profile used in the main P≠NP proof.
-/

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms WellFormedRandomness
#print axioms emergentConfigAtGate
#print axioms wellformed_randomness_exists

end LStar.StructuralOWF.Foundations
