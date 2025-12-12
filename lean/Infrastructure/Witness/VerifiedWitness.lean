import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer2_StructuralOWF.FrontierGate.FrontierGate
-- import Layer2_StructuralOWF.Plant omitted to break circular dependency
import Layer2_StructuralOWF.Plant.PlantCore
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig
import Layer3_InformationBounds.Support.SeedSemantics
import Layer1_Construction.Core.OAPEncoding
import Layer1_Construction.Core.InstanceOps
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic

/-!
# Verified Witness (Proof-Carrying Witness Structure)

Eliminate formalization gap by making digest correctness structural.

## The Gap

Current witness structure:
```lean
structure Witness where
  assignment : Assignment
  digestBits : List Bool  -- Unconstrained
```

Current verifier:
```lean
def LStarVerifier L W := (decodeφFromAssignment L W.assignment).satisfies W.assignment
```

Problem: No connection between `W.digestBits` and actual digest values computed from
`W.assignment`. This makes certain length and value equality proofs impossible.

## The Fix

Proof-carrying witness with digests correct by construction:
```lean
structure VerifiedWitness (L : LStarInstanceFG) where
  assignment : Assignment
  digest : Vector Bool (numGates L)  -- Length correct by type
  digest_correct : digest = digestsFromAssignment L assignment  -- Values correct by proof
```

Benefits:
1. No axioms needed
2. Length equality automatic (Vector type)
3. Value equality automatic (digest_correct proof)
4. Backward compatible (bridge from legacy Witness)
5. Minimal surface area (most code unchanged)

## Usage

Before:
```lean
-- w.digestBits.length = r.gateDigests.length  -- Unprovable
-- w.digestBits[i] = r.gateDigests[i]  -- Unprovable
```

After:
```lean
have vw := VerifiedWitness.ofLegacy L w h_canonical
-- vw.digest.length = numGates L  -- By type
-- vw.digest[i] = computeGateDigest (...)  -- By digest_correct
```

-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF LStar.OAP CutConstraint

/-! ## Step 1: Authoritative Digest Specification -/

/-- Number of FG gates in an L* instance.

    For planted instances: `numGates L = r.gateDigests.length` where `L = plant_n n φ r`.

    This is the source of truth for digest vector length. -/
def numGates (L : LStarInstanceFG) : Nat :=
  -- FG gates are in range [clause_start, clause_start + num_fg_gates)
  -- For our construction: always 1 gate (enforced by h_single_gate)
  -- In general: count nodes v where L.fg.gateReq v holds
  (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).card

/-- Total R bits across all FG gates.

    With the FG bottleneck architecture, each gate produces R bits (not 1 parity bit).
    This is the correct length for digestBits: sum of R values for all FG gates.

    For single-gate planted instances: `totalRBits L = R_of φ numGates gateVertex`
    which equals `(log₂ φ.nvars)²` for the QP profile. -/
def totalRBits (L : LStarInstanceFG) : Nat :=
  (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).sum (fun v => L.R v)

/-- Decode φ from L.encodedφ using an assignment.

    Uses the assignment to compute seeds via entropy pattern,
    then decodes the OAP-encoded formula.

    Note: This is the standard pattern for OAP decoding. -/
noncomputable def decodeφFromAssignment (L : LStarInstanceFG) (a : Assignment L.n) : CNF :=
  -- Build entropy from assignment (same pattern as LStarNP.entropyFromWitness)
  let entropy : (v : Fin L.dag.n) → LStar.Seed (L.seedWidth v) := fun v =>
    if v.val == 0 then
      LStar.ofBits _ (fun _ => false)
    else if v.val <= L.n then
      let varIdx := v.val - 1
      let bit := a.extend varIdx
      LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
    else
      LStar.ofBits _ (fun _ => false)
  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull entropy

  -- Seed width function for clause indices
  let clauseSeedWidthFn : Fin L.encodedφ.clauses.length → Nat := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      L.seedWidth ⟨1 + L.n + i.val, h⟩
    else
      0

  -- Get seeds for clauses
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else
      LStar.ofBits _ (fun _ => false)
  -- Decode
  LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

/-- Decode φ from L.encodedφ using a witness (assignment + FG digest bits).

    **FG-Aware Decoding**: Unlike decodeφFromAssignment which uses zero entropy
    for FG gates, this function uses W.digestBits as the FG gate entropy.

    **Architecture**:
    1. FG gate entropy comes from W.digestBits (derived from assignment)
    2. Non-FG clause seeds depend on FG gate seeds (via DAG parent structure)
    3. Different digestBits → different FG seeds → different clause seeds → different decoding

    **Important Clarification on 2^R Hardness**:
    The digestBits are NOT independent secrets - they are deterministically derived
    from the assignment. The verifier checks this consistency. The 2^R lower bound
    comes from SCL (Semantic Conservation Law, Layer 0), which proves that any
    algorithm solving L* must maintain ≥2^R distinguishable states to correctly
    traverse the FG bottleneck. This is an algorithmic complexity theorem, not
    an additional search dimension in the witness space.

    **Comparison**:
    - decodeφFromAssignment: Uses zero FG entropy (ignores W.digestBits)
    - decodeφFromWitness: Uses W.digestBits as FG entropy (FG-aware)

    **Profile Parameter**: The `profile` determines how R is computed:
    - `.exponential`: R = nvars - exponential hardness (default, stronger result)
    - `.qp`: R = (log₂ nvars)² - quasi-polynomial hardness
    Must match the profile used during planting for correct decoding. -/
noncomputable def decodeφFromWitness (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential) : CNF :=
  -- R = emergence rank at FG gates (= digest bits per gate)
  -- Computed via profile-specific formula for consistency
  let R := Foundations.computeR profile L.n
  -- Build FG-aware entropy (includes ALL R bits from W.digestBits for FG gates)
  let entropy : (v : Fin L.dag.n) → LStar.Seed (L.seedWidth v) := fun v =>
    if v.val == 0 then
      -- Source
      LStar.ofBits _ (fun _ => false)
    else if v.val <= L.n then
      -- Variable: use assignment bit
      let varIdx := v.val - 1
      let bit := W.assignmentInf varIdx
      LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
    else if L.fg.gateReq v then
      -- FG Gate: use ALL R bits from digestBits (derived from assignment)
      -- digestBits layout: [gate0_bit0, gate0_bit1, ..., gate0_bitR-1, gate1_bit0, ...]
      let clause_start := 1 + L.n
      let gate_idx := v.val - clause_start
      -- Use ONLY the first R bits of the seed from digestBits
      -- (matching plant_n_entropy which uses i.val < r.dgLen)
      -- Rest of seedWidth bits are zero (parent contributions handled by seed chain)
      LStar.ofBits (L.seedWidth v) (fun i =>
        if i.val < R then
          -- This bit comes from digestBits at position gate_idx * R + i.val
          let bit_idx := gate_idx * R + i.val
          if h : bit_idx < W.digestBits.length then
            W.digestBits.get ⟨bit_idx, h⟩
          else
            false
        else
          -- Beyond R bits: zero (parent contributions are in seed chain, not entropy)
          false)
    else
      -- Other
      LStar.ofBits _ (fun _ => false)
  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull entropy

  -- Seed width function for clause indices
  let clauseSeedWidthFn : Fin L.encodedφ.clauses.length → Nat := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      L.seedWidth ⟨1 + L.n + i.val, h⟩
    else
      0

  -- Get seeds for clauses
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else
      LStar.ofBits _ (fun _ => false)
  -- Decode
  LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

-- NOTE: LStarVerifierFG moved after digestsFromAssignment definition (line ~870)
-- to avoid forward reference issues.

/-- Entropy function for decoding that matches plant_n_entropy structure.

    This is extracted to a named definition so that proofs involving
    decodeφFromRandomness can reason about entropy equality more easily.

    The structure matches plant_n_entropy exactly when L = plant_n n φ r ... -/
noncomputable def decode_entropy_from_randomness (L : LStarInstanceFG) (r : Randomness L.n)
    (h_dgLen_pos : 0 < r.dgLen)
    (v : Fin L.dag.n) : LStar.Seed (L.seedWidth v) :=
  let clause_start := 1 + L.n
  let fg_end := clause_start + r.gateDigests.length
  if v.val == 0 then
    -- Source: zero entropy
    LStar.ofBits _ (fun _ => false)
  else if v.val <= L.n then
    -- Variable: assignment bit
    let varIdx := v.val - 1
    let bit := r.assignmentInf varIdx
    LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
  else if (clause_start ≤ v.val) ∧ (v.val < fg_end) then
    -- FG Gate: ALL R bits from digest (matches plant_n_entropy exactly!)
    -- The FG gate is the structural bottleneck where SCL's 2^R bound applies
    let idx := v.val - clause_start
    if h : idx < r.gateDigests.length then
      let digest := r.gateDigests.get ⟨idx, h⟩
      -- Use ALL dgLen bits from digest, not just bit 0
      LStar.ofBits _ (fun i =>
        if h_i : i.val < r.dgLen then
          digest.get ⟨i.val, h_i⟩
        else
          false)
    else
      LStar.ofBits _ (fun _ => false)
  else
    -- Other nodes: zero entropy
    LStar.ofBits _ (fun _ => false)

/-- Decode φ from L.encodedφ using full randomness (assignment + gate digests).

    This version uses the SAME entropy pattern as planting, including gate digest
    parity bits for FG gates. This enables proving OAP roundtrip for planted instances.

    The key difference from decodeφFromAssignment:
    - decodeφFromAssignment: Uses ZERO entropy for FG gates (for general instances)
    - decodeφFromRandomness: Uses r.gateDigests for FG gates (matches planting)

    For planted instances L = plant_n n φ r ..., this function will recover φ.

    Requires h_dgLen_pos : 0 < r.dgLen to ensure digest bits are accessible. -/
noncomputable def decodeφFromRandomness (L : LStarInstanceFG) (r : Randomness L.n)
    (h_dgLen_pos : 0 < r.dgLen) : CNF :=
  -- Use the named entropy function (extracted for proof convenience)
  let entropy := decode_entropy_from_randomness L r h_dgLen_pos

  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull entropy

  -- Seed width function for clause indices
  let clauseSeedWidthFn : Fin L.encodedφ.clauses.length → Nat := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      L.seedWidth ⟨1 + L.n + i.val, h⟩
    else
      0

  -- Get seeds for clauses
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else
      LStar.ofBits _ (fun _ => false)

  -- Decode
  LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

/-- Helper: The key theorem we need: plant_n's encoded clause at index i equals encodeClause applied to original -/
theorem plant_n_encoded_clause_eq (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars_min : φ.nvars ≥ 4) (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (i : Nat) (h_i : i < φ.clauses.length) :
    let L := plant_n n φ r h_nvars_min h_dgLen
    let h_i_enc : i < L.encodedφ.clauses.length := by
      have h_len := plant_n_encodedφ_clauses_length n φ r h_nvars_min h_dgLen
      rw [h_len]; exact h_i
    let numGates := r.gateDigests.length
    let dag := build3SATReductionDAG φ numGates
    let seedWidth_val : Fin dag.n → Nat := fun v =>
      Construction.computeSeedWidth φ numGates (Foundations.R_of φ numGates) v
    let plant_entropy := plant_n_entropy φ r h_nvars_min h_dgLen dag seedWidth_val
    let plant_seeds := L.toLStarInstanceFull.computeSeedChain plant_entropy
    let vertexIdx := φ.nvars + 1 + i
    let h_valid : vertexIdx < dag.n := by
      simp only [dag, build3SATReductionDAG, Construction.build3SATReductionDAG,
                 Construction.totalNodes, Construction.reductionTreeSize]
      omega
    let clauseSeed := plant_seeds ⟨vertexIdx, h_valid⟩
    L.encodedφ.clauses[i]'h_i_enc = LStar.OAP.encodeClause φ.clauses[i] clauseSeed i := by
  intro L h_i_enc numGates dag seedWidth_val plant_entropy plant_seeds vertexIdx h_valid clauseSeed

  -- Get the structure of L.encodedφ from plant_n_encodedφ_eq
  have h_enc := plant_n_encodedφ_eq n φ r h_nvars_min h_dgLen

  -- Extract clauses equality from h_enc
  have h_clauses : L.encodedφ.clauses =
    (plant_n_encode_cnf φ numGates dag seedWidth_val plant_seeds rfl).clauses := by
    have h_eq : L.encodedφ = plant_n_encode_cnf φ numGates dag seedWidth_val plant_seeds rfl := by
      calc L.encodedφ
        _ = (let numGates := r.gateDigests.length
             let dag := build3SATReductionDAG φ numGates
             let seedWidth_val := fun v => Construction.computeSeedWidth φ numGates (Foundations.R_of φ numGates) v
             let entropy := plant_n_entropy φ r h_nvars_min h_dgLen dag seedWidth_val
             let full := (plant_n n φ r h_nvars_min h_dgLen).toLStarInstanceFull
             let seeds := full.computeSeedChain entropy
             plant_n_encode_cnf φ numGates dag seedWidth_val seeds rfl) := h_enc
        _ = plant_n_encode_cnf φ numGates dag seedWidth_val plant_seeds rfl := rfl
    rw [h_eq]

  -- Get bound for RHS
  have h_bound_rhs : i < (plant_n_encode_cnf φ numGates dag seedWidth_val plant_seeds rfl).clauses.length := by
    unfold plant_n_encode_cnf
    simp only [LStar.OAP.encodeWithOAPDep_clauses_length]
    exact h_i

  -- Clauses at index i are equal
  have h_elem : L.encodedφ.clauses[i]'h_i_enc =
    (plant_n_encode_cnf φ numGates dag seedWidth_val plant_seeds rfl).clauses[i]'h_bound_rhs := by
    simp only [h_clauses]

  rw [h_elem]

  -- Now unfold plant_n_encode_cnf to encodeWithOAPDep
  unfold plant_n_encode_cnf

  -- Define the clauseSeedWidth and getClauseSeed from plant_n_encode_cnf
  let clauseSeedWidth' : Fin φ.clauses.length → Nat := fun j =>
    let vIdx := φ.nvars + 1 + j.val
    seedWidth_val ⟨vIdx, by
      have h_j_lt := j.isLt
      simp only [dag, build3SATReductionDAG, Construction.build3SATReductionDAG,
                 Construction.totalNodes, Construction.reductionTreeSize]
      omega⟩

  let getClauseSeed' : (j : Fin φ.clauses.length) → Seed (clauseSeedWidth' j) := fun j =>
    let vIdx := φ.nvars + 1 + j.val
    plant_seeds ⟨vIdx, by
      have h_j_lt := j.isLt
      simp only [L, plant_n, build3SATReductionDAG, Construction.build3SATReductionDAG,
        Construction.totalNodes, Construction.reductionTreeSize]
      omega⟩

  -- Apply encodeWithOAPDep_getElem
  have h_getElem := LStar.OAP.encodeWithOAPDep_getElem φ clauseSeedWidth' getClauseSeed' i h_i
  rw [h_getElem]
  -- Goal closed by the rewrite

theorem plant_n_oap_decode (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars_min : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2) :
    let h_dgLen_pos : 0 < r.dgLen := by
      rw [h_dgLen]
      have h_log_pos : 0 < Nat.log 2 φ.nvars := Nat.log_pos (by omega) (by omega)
      exact Nat.pow_pos h_log_pos
    decodeφFromRandomness (plant_n n φ r h_nvars_min h_dgLen) r h_dgLen_pos = φ := by
  let L := plant_n n φ r h_nvars_min h_dgLen

  -- Derive h_dgLen_pos from h_dgLen and h_nvars_min
  have h_dgLen_pos : 0 < r.dgLen := by
    rw [h_dgLen]
    have h_log_pos : 0 < Nat.log 2 φ.nvars := Nat.log_pos (by omega) (by omega)
    exact Nat.pow_pos h_log_pos

  -- Define common structures
  let numGates := r.gateDigests.length
  let dag := build3SATReductionDAG φ numGates
  let seedWidth_val := fun v => Construction.computeSeedWidth φ numGates (Foundations.R_of φ numGates) v

  -- Key structural facts
  have h_L_n : L.n = φ.nvars := rfl
  have h_L_seedWidth : L.seedWidth = seedWidth_val := rfl
  have h_L_dag : L.dag = dag := rfl

  -- The decoding entropy (from decodeφFromRandomness) - now uses the named function
  let decode_entropy : (v : Fin L.dag.n) → LStar.Seed (L.seedWidth v) :=
    decode_entropy_from_randomness L r h_dgLen_pos

  -- The planting entropy (from plant_n construction)
  let plant_entropy := plant_n_entropy φ r h_nvars_min h_dgLen dag seedWidth_val

  -- Step 1: Prove entropy functions are equal pointwise
  -- Key insight: When L = plant_n ..., we have L.n = φ.nvars and L.seedWidth = seedWidth_val
  -- definitionally. Use dsimp to unfold L and then everything matches.
  have h_entropy_eq : ∀ v, decode_entropy v = plant_entropy v := by
    intro v
    -- Unfold the let-bindings for L and use definitional equality
    -- L := plant_n n φ r h_nvars_min h_dgLen, and plant_n sets n := φ.nvars, seedWidth := seedWidth_val
    -- So L.n = φ.nvars and L.seedWidth v = seedWidth_val v definitionally
    simp only [decode_entropy, plant_entropy]
    -- dsimp to reduce L.n and L.seedWidth to their definitions
    -- This closes the goal since both sides become definitionally equal
    dsimp only [L, plant_n, decode_entropy_from_randomness, plant_n_entropy]

  -- Step 2: Compute seeds from both entropies (they're equal by h_entropy_eq)
  let plant_seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull plant_entropy

  -- Step 3: Get the encoding equality from plant_n
  have h_encoded := plant_n_encodedφ_eq n φ r h_nvars_min h_dgLen

  -- Step 4: Apply OAP roundtrip cleanly via CNF equality

  unfold decodeφFromRandomness

  -- Use CNF.eq_iff to split into nvars and clauses components
  rw [CNF.eq_iff]
  constructor

  -- Part 1: nvars equality (straightforward)
  · simp only [LStar.OAP.decodeWithOAPDep]
    have h_enc_nvars : L.encodedφ.nvars = φ.nvars := by
      rw [h_encoded]
      unfold plant_n_encode_cnf
      simp only [LStar.OAP.encodeWithOAPDep]
    exact h_enc_nvars

  -- Part 2: clauses equality (the heart of the proof)
  · -- Get the clause length equality from encoding
    have h_enc_len : L.encodedφ.clauses.length = φ.clauses.length := by
      rw [h_encoded]
      unfold plant_n_encode_cnf
      exact LStar.OAP.encodeWithOAPDep_clauses_length φ _ _

    -- Apply List.ext_getElem with the length equality
    apply List.ext_getElem

    -- Length equality for decoded clauses
    · simp only [LStar.OAP.decodeWithOAPDep, List.length_map, List.length_range]
      exact h_enc_len

    -- Element-wise equality for each clause
    · intro i h_i_enc h_i_φ

      -- Define the clause vertex (used for both encode and decode)
      let vertexIdx := φ.nvars + 1 + i
      have h_valid : vertexIdx < dag.n := by
        simp only [dag, build3SATReductionDAG, Construction.build3SATReductionDAG,
                   Construction.totalNodes, Construction.reductionTreeSize]
        omega

      -- Key equality: seeds computed from decode_entropy = plant_seeds
      have h_seed_eq : ∀ v, L.toLStarInstanceFull.computeSeedChain decode_entropy v = plant_seeds v := by
        intro v
        exact LStar.LStarInstanceFull.computeSeedChain_ext L.toLStarInstanceFull decode_entropy plant_entropy h_entropy_eq v

      -- Define the common seed at the clause vertex
      let clause_seed := plant_seeds ⟨vertexIdx, h_valid⟩

      -- The decode seed equals the clause_seed (via h_seed_eq)
      have h_decode_seed_eq : L.toLStarInstanceFull.computeSeedChain decode_entropy ⟨vertexIdx, h_valid⟩ = clause_seed := by
        exact h_seed_eq ⟨vertexIdx, h_valid⟩

      -- Apply the helper theorem for the encoded clause
      have h_encoded_clause_eq := plant_n_encoded_clause_eq n φ r h_nvars_min h_dgLen i h_i_φ

      -- Step 1: Unfold the decoding to expose the clause structure
      simp only [LStar.OAP.decodeWithOAPDep, List.getElem_map, List.getElem_range]

      -- Get the actual bound we need
      have h_bound_enc : i < L.encodedφ.clauses.length := by rw [h_enc_len]; exact h_i_φ

      -- Simplify dite using h_bound_enc
      rw [dif_pos h_bound_enc]

      -- Simplify the getElem? to getElem
      have h_getElem_eq_some : L.encodedφ.clauses[i]? = some (L.encodedφ.clauses[i]'h_bound_enc) :=
        List.getElem?_eq_getElem h_bound_enc
      rw [h_getElem_eq_some]

      -- The decode dite condition: 1 + L.n + i < L.dag.n
      have h_dite_cond : 1 + L.n + i < L.dag.n := by
        simp only [L, plant_n, build3SATReductionDAG, Construction.build3SATReductionDAG,
                   Construction.totalNodes, Construction.reductionTreeSize]
        omega

      -- Key: 1 + L.n + i = φ.nvars + 1 + i (since L.n = φ.nvars = φ.nvars)
      have h_idx_eq : 1 + L.n + i = vertexIdx := by
        simp only [vertexIdx, h_L_n]
        omega

      -- The Fin indices are equal
      have h_fin_eq : (⟨1 + L.n + i, h_dite_cond⟩ : Fin L.dag.n) = ⟨vertexIdx, h_valid⟩ := by
        ext; exact h_idx_eq

      -- Rewrite the encoded clause
      conv_lhs => rw [h_encoded_clause_eq]

      -- Goal: decodeClause (encodeClause φ.clauses[i] clause_seed i) decode_seed i = φ.clauses[i]

      -- Apply clause_roundtrip_val_eq to skip the seed width dependency mismatch
      -- by proving the underlying values are equal.

      -- Simplify any remaining match structure from getElem?
      dsimp only

      apply LStar.OAP.clause_roundtrip_val_eq

      -- Helper: proof transport preserves .val for Seed (which is Fin)
      have h_cast_val : ∀ {n m : Nat} (h : n = m) (s : LStar.Seed n), (h ▸ s).val = s.val := by
        intros n m h s
        cases h
        rfl

      -- Goal: clause_seed.val = (if h : cond then h ▸ seed else ...).val
      -- First simplify the dite using h_dite_cond
      rw [dif_pos h_dite_cond]

      -- Strip the cast using h_cast_val
      rw [h_cast_val]

      -- Goal: ↑seed_lhs = ↑seed_rhs  (equality of Nat values)
      --
      -- LHS: (computeSeedChain plant_n_entropy ⟨φ.nvars+1+i, h_valid⟩).val
      -- RHS: (computeSeedChain inline_entropy ⟨1+L.n+(List.range ...)[i], ...⟩).val
      --
      -- Strategy: Show both seeds are equal (as Seed/Fin values), then .val equality follows.
      --
      -- Key facts:
      -- 1. plant_n_entropy and inline_entropy are definitionally equal
      -- 2. The indices have equal .val: φ.nvars+1+i = 1+L.n+(List.range ...)[i] = 1+L.n+i
      --    (since L.n = φ.nvars and List.range[i] = i)

      -- First, show List.range indexing simplifies
      have h_range_len : i < (List.range L.encodedφ.clauses.length).length := by
        simp only [List.length_range]; exact h_bound_enc
      have h_range_simp : (List.range L.encodedφ.clauses.length)[i]'h_range_len = i :=
        List.getElem_range h_range_len

      -- The RHS index .val equals 1 + L.n + i (after List.range simplification)
      -- Show: 1 + L.n + (List.range ...)[i] = 1 + L.n + i = vertexIdx
      -- We have h_idx_eq: 1 + L.n + i = vertexIdx

      -- Apply congrArg to show seed equality implies .val equality
      -- ↑a = ↑b when a = b (for Fin/Seed)

      -- Both sides compute via the SAME entropy function (plant_n_entropy = inline_entropy definitionally)
      -- at indices with the same .val.

      -- Show the seeds are equal by proving both equal clause_seed
      -- clause_seed = plant_seeds ⟨vertexIdx, h_valid⟩ = computeSeedChain plant_entropy ⟨vertexIdx, h_valid⟩

      -- For the RHS: computeSeedChain inline_entropy ⟨rhs_idx, ...⟩
      -- We need to show this equals clause_seed

      -- The inline entropy is definitionally plant_n_entropy = plant_entropy
      -- The RHS index has .val = 1 + L.n + i (where List.range[i] = i)
      -- = φ.nvars + 1 + i = vertexIdx.val

      -- Since computeSeedChain only depends on the entropy function and the index .val
      -- (seeds at indices with same .val under same entropy are equal), we're done.

      -- The inline entropy in the goal uses `(↑v == 0)` which equals `(v.val == 0)`
      -- and `(↑j == 0)` which equals `(j.val == 0)`. These should match plant_entropy.
      --
      -- However, the index in the goal uses (List.range ...)[i] which needs simplification.
      --
      -- Strategy: Use h_entropy_eq (decode_entropy = plant_entropy) and the fact that the
      -- inline entropy is definitionally decode_entropy. Then use computeSeedChain_ext to
      -- show the chains are equal, and finally align the indices.

      -- The inline entropy is definitionally equal to decode_entropy
      -- (both use the same structure with v.val/↑v comparisons)

      -- Use computeSeedChain_ext: if entropies are equal pointwise, chains are equal
      have h_chain_ext := LStar.LStarInstanceFull.computeSeedChain_ext L.toLStarInstanceFull
        decode_entropy plant_entropy h_entropy_eq

      -- The RHS index needs simplification. First get the index form.
      -- The RHS has index ⟨1 + L.n + (List.range ...)[i], some_proof⟩
      -- We want to show this equals ⟨vertexIdx, h_valid⟩

      -- Get the proof that the RHS index value equals i
      have h_rhs_idx_val : 1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len = vertexIdx := by
        simp only [h_range_simp, h_L_n, vertexIdx]
        omega

      -- The goal compares .val of two seeds
      -- LHS: (plant_seeds ⟨vertexIdx, h_valid⟩).val = (computeSeedChain plant_entropy ⟨vertexIdx, h_valid⟩).val
      -- RHS: (computeSeedChain inline_entropy ⟨rhs_idx, rhs_proof⟩).val

      -- Since inline_entropy = decode_entropy (definitionally) and decode_entropy = plant_entropy (by h_entropy_eq),
      -- the chains are equal at any index.

      -- Use h_seed_eq which already proves: computeSeedChain decode_entropy v = plant_seeds v
      -- This means: (computeSeedChain decode_entropy ⟨idx, proof⟩).val = (plant_seeds ⟨idx, proof⟩).val

      -- The RHS inline entropy should be decode_entropy, so use h_seed_eq

      -- First show the indices yield the same seed via h_seed_eq
      -- h_seed_eq at any index v gives: computeSeedChain decode_entropy v = plant_seeds v

      -- The goal is: ↑clause_seed = ↑(RHS computation)
      -- clause_seed = plant_seeds ⟨vertexIdx, h_valid⟩
      -- RHS = computeSeedChain inline_entropy ⟨rhs_idx, rhs_proof⟩

      -- Since inline_entropy = decode_entropy (definitionally), RHS = computeSeedChain decode_entropy ⟨rhs_idx, rhs_proof⟩
      -- By h_seed_eq: computeSeedChain decode_entropy v = plant_seeds v
      -- So RHS = plant_seeds ⟨rhs_idx, rhs_proof⟩

      -- Since rhs_idx.val = vertexIdx (by h_rhs_idx_val), we need Fin proof irrelevance

      -- Use the fact that Seeds with equal .val are equal (they're Fin types)
      -- If two Fin n values have equal underlying Nat, they're equal

      -- Approach: show LHS and RHS both equal the same Nat

      -- LHS = clause_seed.val = (plant_seeds ⟨vertexIdx, h_valid⟩).val
      -- RHS = (computeSeedChain inline_entropy ⟨rhs_idx, rhs_proof⟩).val
      --     = (computeSeedChain decode_entropy ⟨rhs_idx, rhs_proof⟩).val  [inline = decode_entropy def'ly]
      --     = (plant_seeds ⟨rhs_idx, rhs_proof⟩).val                       [by h_seed_eq]

      -- Now we need: (plant_seeds ⟨vertexIdx, h_valid⟩).val = (plant_seeds ⟨rhs_idx, rhs_proof⟩).val

      -- Since vertexIdx and rhs_idx have the same Nat value (by h_rhs_idx_val converted),
      -- and Seed is Fin, the .val only depends on the Nat value and the seed width.
      -- The seed widths are both L.seedWidth at indices with the same .val, so they're equal.

      -- The key: plant_seeds is defined as computeSeedChain plant_entropy
      -- computeSeedChain at index v only depends on v.val (not the proof), so
      -- plant_seeds ⟨a, p1⟩ = plant_seeds ⟨a, p2⟩ when both have the same Nat value a.

      -- Use Fin.ext to show the seeds are equal when indices have equal .val
      -- Actually, this is automatic since Fin.val only extracts the Nat component

      -- Goal: ↑(computeSeedChain plant_n_entropy ⟨vertexIdx, h_valid⟩) =
      --       ↑(computeSeedChain decode_entropy_from_randomness ⟨1 + L.n + range[i], proof⟩)
      --
      -- The key insight: decode_entropy_from_randomness L r and plant_n_entropy are
      -- structurally the same when L = plant_n ..., so they compute the same seeds.
      --
      -- Both entropy functions have identical structure:
      -- - if v.val == 0 then zero
      -- - else if v.val <= n then assignment bit
      -- - else if fg_gate_range then digest bit
      -- - else zero
      --
      -- Since L.n = φ.nvars, the conditions are equivalent.

      -- Use the fact that both entropies are equal pointwise
      -- h_entropy_eq : decode_entropy v = plant_entropy v (where decode_entropy = decode_entropy_from_randomness L r)

      -- The chains at any index must be equal since the entropies are equal
      -- Strategy: Both sides compute chains at indices with same .val
      -- LHS: plant_entropy at ⟨vertexIdx, h_valid⟩
      -- RHS: decode_entropy at ⟨1 + L.n + range[i], _⟩
      --
      -- Since decode_entropy = plant_entropy (by h_entropy_eq) and
      -- vertexIdx = 1 + L.n + range[i] (since range[i] = i and L.n = φ.nvars),
      -- both sides compute the same seed.

      -- Key insight: use Seed.get_eq_of_val_eq to handle seeds with same val but different indices
      -- The LHS seed is at ⟨vertexIdx, h_valid⟩
      -- The RHS seed is at ⟨1 + L.n + range[i], some_proof⟩ where 1 + L.n + range[i] = vertexIdx

      -- First establish the Nat equality of indices
      have h_rhs_idx_nat : 1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len = vertexIdx := by
        rw [h_range_simp, h_L_n]
        simp only [vertexIdx]
        omega

      -- The goal compares .val of two Seeds. We use the fact that:
      -- - Both chains are computed from entropy functions that are pointwise equal (h_entropy_eq)
      -- - The indices have the same .val (h_rhs_idx_nat)
      -- - computeSeedChain produces seeds of type Seed (seedWidth idx)
      -- - If idx1.val = idx2.val, then seedWidth idx1 = seedWidth idx2 (since seedWidth depends only on .val)

      -- Actually the goal is ↑lhs_seed = ↑rhs_seed where both are Seeds (which are Fin)
      -- So we need to prove the underlying Nat values are equal

      -- Use the chain extensionality on decode_entropy and plant_entropy at the vertexIdx
      simp only [decode_entropy] at h_chain_ext

      -- The LHS is: (plant_seeds ⟨vertexIdx, h_valid⟩).val
      --           = (computeSeedChain plant_entropy ⟨vertexIdx, h_valid⟩).val
      -- The RHS is: (computeSeedChain decode_entropy_from_randomness ⟨rhs_idx, _⟩).val

      -- Show RHS equals (computeSeedChain decode_entropy_from_randomness ⟨vertexIdx, h_valid⟩).val
      -- by using Fin proof irrelevance (the indices have equal .val)

      -- Use LStar.Seed.get_eq_of_val_eq: seeds with same underlying Nat have same bits
      -- So ↑seed1 = ↑seed2 when seed1.val = seed2.val (for Fin types, this is Fin.val_eq_val)

      -- Actually for Fin, if two Fin n values have equal underlying Nat, they're equal
      -- So we can use Fin.ext

      -- The crux: show (computeSeedChain decode_entropy_from_randomness L r ⟨rhs_idx, _⟩).val
      --                = (computeSeedChain plant_entropy ⟨vertexIdx, h_valid⟩).val

      -- Since decode_entropy_from_randomness L r = decode_entropy = plant_entropy (pointwise),
      -- computeSeedChain decode_entropy_from_randomness L r = computeSeedChain plant_entropy

      -- And since rhs_idx.val = vertexIdx, the result is the same

      -- Actually, seeds are Fin, so .val is coercion to Nat. Two Fin with same Nat are equal.
      -- The key is: computeSeedChain f ⟨n, h1⟩ = computeSeedChain f ⟨n, h2⟩ (proof irrelevance for Fin index)

      -- Strategy: Show both seeds have the same .val (underlying Nat)
      -- 1. decode_entropy_from_randomness = plant_entropy (from h_entropy_eq)
      -- 2. The Fin indices have equal .val (h_rhs_idx_nat)

      -- Construct the bound for the RHS index (needed below)
      have h_rhs_bound : 1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len < L.dag.n := by
        rw [h_range_simp]
        exact h_dite_cond

      -- The RHS Fin index equals the LHS (vertexIdx) - they have the same .val
      have h_idx_fin_eq : (⟨vertexIdx, h_valid⟩ : Fin L.dag.n) =
          ⟨1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len, h_rhs_bound⟩ := by
        ext
        exact h_rhs_idx_nat.symm

      -- Use h_chain_ext to show the chains are equal
      have h_rhs_chain := h_chain_ext ⟨1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len, h_rhs_bound⟩
      -- h_rhs_chain : computeSeedChain decode_entropy ⟨rhs_idx, _⟩ = computeSeedChain plant_entropy ⟨rhs_idx, _⟩

      -- The LHS is: (computeSeedChain plant_entropy ⟨vertexIdx, h_valid⟩).val
      -- The RHS is: (computeSeedChain decode_entropy ⟨rhs_idx, h_rhs_bound⟩).val

      -- Rewrite LHS index to RHS index using h_idx_fin_eq
      conv_lhs => rw [h_idx_fin_eq]

      -- Now LHS: (computeSeedChain plant_entropy ⟨rhs_idx, h_rhs_bound⟩).val
      -- RHS: (computeSeedChain decode_entropy ⟨rhs_idx, h_rhs_bound⟩).val

      -- By h_rhs_chain, the chains at the same index are equal
      -- h_rhs_chain: decode_entropy at idx = plant_entropy at idx
      -- Goal: ↑(plant_entropy at idx) = ↑(decode_entropy at idx')

      -- The LHS and RHS compute the same seed because:
      -- 1. decode_entropy = plant_entropy (by h_entropy_eq)
      -- 2. The indices have the same .val (by h_rhs_idx_nat)

      -- Use congrArg to reduce ↑a = ↑b to showing a.val = b.val
      -- Actually ↑ for Fin is just .val, so we're already comparing Nats

      -- Show both sides equal the same Nat
      -- LHS = (computeSeedChain plant_entropy ⟨idx, h_rhs_bound⟩).val
      -- RHS = (computeSeedChain decode_entropy ⟨idx', rhs_proof⟩).val

      -- Use transitivity: LHS = middle = RHS
      -- where middle = (computeSeedChain decode_entropy ⟨idx, h_rhs_bound⟩).val

      -- Step 1: LHS = middle (by h_rhs_chain.symm applied pointwise)
      -- Note: decode_entropy := decode_entropy_from_randomness L r h_dgLen_pos (by definition)
      -- So h_rhs_chain directly applies since the let-binding is definitionally equal
      have h_lhs_eq : (L.toLStarInstanceFull.computeSeedChain plant_entropy ⟨1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len, h_rhs_bound⟩).val =
          (L.toLStarInstanceFull.computeSeedChain decode_entropy ⟨1 + L.n + (List.range L.encodedφ.clauses.length)[i]'h_range_len, h_rhs_bound⟩).val := by
        rw [h_rhs_chain.symm]

      -- Step 2: middle = RHS (indices have same .val, so seeds are equal)
      -- The RHS index has the same .val as LHS index (after simplifying range[i] = i)

      -- Unfold let-bindings so h_lhs_eq pattern matches goal
      simp only [L, plant_entropy, dag, seedWidth_val, decode_entropy] at h_lhs_eq ⊢

      -- Use convert which is more flexible about proof term differences
      -- convert using 4 handles proof-irrelevance for Fin bound proofs
      convert h_lhs_eq using 4



/-- Build entropy from assignment (for seed computation).
    This mirrors the entropy pattern in decodeφFromAssignment. -/
def entropyFromAssignment (L : LStarInstanceFG) (a : Assignment L.n) (v : Fin L.dag.n) : Seed (L.seedWidth v) :=
  if v.val == 0 then
    LStar.ofBits _ (fun _ => false)
  else if v.val <= L.n then
    let varIdx := v.val - 1
    let bit := a.extend varIdx
    LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
  else
    LStar.ofBits _ (fun _ => false)

/-- The filter of FG gate vertices as a sorted list.

    This provides a canonical ordering of FG gates for iteration.
    The list is sorted by vertex index to ensure deterministic ordering. -/
noncomputable def fgGatesList (L : LStarInstanceFG) : List (Fin L.dag.n) :=
  (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).toList.mergeSort (·.val ≤ ·.val)

/-- FG gates list has length equal to numGates. -/
lemma fgGatesList_length (L : LStarInstanceFG) :
    (fgGatesList L).length = numGates L := by
  unfold fgGatesList numGates
  rw [List.length_mergeSort, Finset.length_toList]

/-- Every element in fgGatesList satisfies gateReq. -/
lemma fgGatesList_mem_gateReq (L : LStarInstanceFG) (v : Fin L.dag.n)
    (hv : v ∈ fgGatesList L) : L.fg.gateReq v := by
  unfold fgGatesList at hv
  -- mergeSort preserves membership (it's a permutation)
  have h_perm := List.mergeSort_perm (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).toList (·.val ≤ ·.val)
  rw [h_perm.mem_iff] at hv
  exact (Finset.mem_toList.mp hv |> Finset.mem_filter.mp).2

/-- Authoritative digest computation from assignment.

    This is the single source of truth for what digest bits should be.
    All witnesses must match this specification.

    **Architecture**: Iterates directly over FG gate vertices using L.R,
    ensuring length = totalRBits by construction. For each FG gate v:
    1. Compute the emergent config at v
    2. Extract ALL R bits (where R = L.R v)
    3. Concatenate into flat list

    **Length Guarantee**: Uses L.R directly, so total length = sum of L.R
    over FG gates = totalRBits L (by definition).

    Note: This version with explicit seeds parameter is used when seeds are
    pre-computed (e.g., from a witness with digest bits). -/
noncomputable def digestsFromAssignmentWithSeeds
    (L : LStarInstanceFG)
    (a : Assignment L.n)
    (seeds : (v : Fin L.dag.n) → Seed (L.seedWidth v))
    : List Bool :=
  -- Seed width function for clause indices (matches decodeφFromAssignment)
  let clauseSeedWidthFn : Fin L.encodedφ.clauses.length → Nat := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      L.seedWidth ⟨1 + L.n + i.val, h⟩
    else
      0
  -- Get seeds for clauses (matches decodeφFromAssignment)
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else
      LStar.ofBits _ (fun _ => false)
  -- Decode φ using dependent seed widths
  let φ := LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

  -- Create flat list: ALL R bits for each FG gate
  -- Layout: [gate0_bit0, gate0_bit1, ..., gate0_bitR-1, gate1_bit0, ...]
  -- Iterate over FG gates directly to ensure length = totalRBits L
  let gateDigests := (fgGatesList L).map (fun v =>
    -- Get L.R v bits for this gate
    let R := L.R v
    -- Compute emergent config using emergentConfigAtGate
    -- Note: gateIndex = v.val - (1 + L.n) for contiguous gates
    let gateIndex := v.val - (1 + L.n)
    match emergentConfigAtGate φ L.encodedφ.nvars_pos (numGates L) a.extend gateIndex with
    | none => List.replicate R false  -- Fallback: use L.R v bits
    | some ⟨R_cfg, cfg⟩ =>
        -- Use actual config bits, padded/truncated to L.R v
        let bits := extractAllBits cfg
        if bits.length = R then bits
        else List.replicate R false  -- Fallback if R mismatch
  )
  gateDigests.flatten

/-- Authoritative digest computation from assignment (convenience version).

    Computes seeds internally from the assignment using zero entropy for
    non-variable nodes. This is the standard pattern for OAP decoding. -/
noncomputable def digestsFromAssignment
    (L : LStarInstanceFG)
    (a : Assignment L.n)
    : List Bool :=
  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull (entropyFromAssignment L a)
  digestsFromAssignmentWithSeeds L a seeds

/-- FG-aware L* verifier: Uses W.digestBits for FG gate entropy AND enforces consistency.

    **Verification Steps**:
    1. Checks W.digestBits = digestsFromAssignment (digest consistency)
    2. Uses W.digestBits in decoding (FG-aware decoding)
    3. Checks decoded formula is satisfied

    **Digest Consistency Check**: The digest check ensures the witness is well-formed:
    W.digestBits must match what the assignment deterministically produces.
    This is a CONSISTENCY check, not an independent search dimension.

    **Where 2^R Hardness Comes From**: The 2^R lower bound is NOT enforced by this
    verifier checking independent secrets. Instead, it comes from SCL (Semantic
    Conservation Law, Layer 0), which proves that any algorithm solving L* must
    maintain ≥2^R distinguishable states to correctly compute seeds at the FG gate.
    This is a theorem about algorithmic state complexity.

    **Key Distinction**:
    - Verifier checks: consistency (digest derived from assignment)
    - SCL proves: algorithmic complexity (2^R states needed to solve)

    **Profile Parameter**: Must match the profile used during planting (default: exponential). -/
def LStarVerifierFG (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential) : Prop :=
  -- Digest consistency: W.digestBits must match what assignment produces
  W.digestBits = digestsFromAssignment L W.assignment ∧
  -- Satisfiability: decoded formula must be satisfied by assignment
  (decodeφFromWitness L W profile).satisfies W.assignment.extend

/-! ## Step 2: Proof-Carrying Witness Structure -/

/-- Helper: Extract entropy from witness for seed computation.

    **R-bit Layout**: W.digestBits is a flat list of ALL R bits for each gate:
    [gate0_bit0, gate0_bit1, ..., gate0_bitR-1, gate1_bit0, ...]

    **Note on 2^R Hardness**: The R bits are deterministically derived from the
    assignment. The 2^R lower bound comes from SCL (Layer 0), which proves any
    algorithm must maintain 2^R distinguishable states to traverse the FG gate.
    This is an algorithmic complexity theorem, not a verifier-enforced search.

    **Profile Parameter**: Determines R computation (default: exponential). -/
def entropyFromWitness (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential)
    (v : Fin L.dag.n) : Seed (L.seedWidth v) :=
  -- R = emergence rank at FG gates (= digest bits per gate)
  -- Computed via profile-specific formula for consistency
  let R := Foundations.computeR profile L.n
  if v.val == 0 then
    -- Source
    LStar.ofBits _ (fun _ => false)
  else if v.val <= L.n then
    -- Variable: use assignment bit
    let varIdx := v.val - 1
    let bit := W.assignmentInf varIdx
    LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
  else if L.fg.gateReq v then
    -- FG Gate: use ALL R bits from digestBits (derived from assignment)
    let clause_start := 1 + L.n
    let gate_idx := v.val - clause_start
    -- Use ONLY the first R bits of the seed from digestBits
    LStar.ofBits _ (fun i =>
      if i.val < R then
        let bit_idx := gate_idx * R + i.val
        if h : bit_idx < W.digestBits.length then
          W.digestBits.get ⟨bit_idx, h⟩
        else
          false
      else
        false)
  else
    -- Other
    LStar.ofBits _ (fun _ => false)

/-- Verified Witness: digests correct by construction.

    Type invariants:
    - `digest = digestsFromAssignment ...` (enforced by proof field)
    
    The check is:
    1. Extract entropy from W (assignment + digestBits)
    2. Compute seeds
    3. Decode φ
    4. Compute expected digests
    5. Assert W.digestBits = expected digests
    -/
structure VerifiedWitness (L : LStarInstanceFG) where
  /-- The underlying witness -/
  w : Witness L.n

  /-- Proof that digests match the authoritative computation -/
  digest_correct : w.digestBits = digestsFromAssignmentWithSeeds L w.assignment
    (LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull (entropyFromWitness L w))

/-- Structurally correct witness predicate. -/
def HasCorrectDigests (L : LStarInstanceFG) (W : Witness L.n) : Prop :=
  W.digestBits = digestsFromAssignmentWithSeeds L W.assignment
    (LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull (entropyFromWitness L W))

/-- Lift legacy witness to verified witness. -/
noncomputable def VerifiedWitness.ofLegacy
    (L : LStarInstanceFG)
    (W : Witness L.n)
    (h : HasCorrectDigests L W)
    : VerifiedWitness L :=
  { w := W
    digest_correct := h }

-- Note: canonicalize was removed because it's impossible for OAP without solving
-- the cryptographic fixed point problem. For planted instances, the correct seeds
-- come from the randomness r. For arbitrary instances, finding valid digests is hard
-- (that's the security property!).


/-! ## Step 4: Lemmas for Length and Value Equalities -/

/-- digestsFromAssignmentWithSeeds produces exactly totalRBits bits.

    **Theorem** (not axiom): The proof is unconditional - it works for ANY
    LStarInstanceFG by construction. Each gate produces exactly L.R v bits:
    - If emergentConfigAtGate succeeds with matching R: use actual bits
    - Otherwise: fallback to List.replicate (L.R v) false

    This fallback ensures correct length regardless of emergentConfigAtGate behavior.
    Sum of L.R over FG gates = totalRBits L by definition. -/
theorem digestsFromAssignmentWithSeeds_length_eq_totalRBits
    (L : LStarInstanceFG) (a : Assignment L.n)
    (seeds : (v : Fin L.dag.n) → LStar.Seed (L.seedWidth v))
    : (digestsFromAssignmentWithSeeds L a seeds).length = totalRBits L := by
  unfold digestsFromAssignmentWithSeeds
  simp only []

  -- Length of flatten = sum of lengths of sublists
  rw [List.length_flatten]

  -- Helper: compute function for each gate's bits (for cleaner proof)
  let gateBitsFn := fun (v : Fin L.dag.n) (φ : CNF) (h_nvars : φ.nvars > 0) =>
    let R := L.R v
    let gateIndex := v.val - (1 + L.n)
    match emergentConfigAtGate φ h_nvars (numGates L) a.extend gateIndex with
    | none => List.replicate R false
    | some ⟨R_cfg, cfg⟩ =>
        let bits := extractAllBits cfg
        if bits.length = R then bits else List.replicate R false

  -- Key lemma: each sublist has length L.R v by construction
  -- This holds because:
  -- - none case: List.replicate (L.R v) false has length L.R v
  -- - some case with match: bits has length L.R v
  -- - some case with mismatch: List.replicate (L.R v) false has length L.R v
  have h_each_len : ∀ (v : Fin L.dag.n) (φ : CNF) (h_nvars : φ.nvars > 0),
      (gateBitsFn v φ h_nvars).length = L.R v := by
    intro v φ h_nvars
    simp only [gateBitsFn]
    split
    · simp [List.length_replicate]
    · rename_i R_cfg cfg _
      split
      · assumption
      · simp [List.length_replicate]

  -- The sum of lengths = sum of L.R over fgGatesList
  -- Because each element in the map has length L.R v

  -- First, show map of lengths = map of L.R
  have h_lengths_eq : ∀ (φ : CNF) (h_nvars : φ.nvars > 0),
      ((fgGatesList L).map (fun v => gateBitsFn v φ h_nvars)).map List.length =
      (fgGatesList L).map (fun v => L.R v) := by
    intro φ h_nvars
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro v _
    exact h_each_len v φ h_nvars

  -- fgGatesList is a permutation of the filter's toList
  have h_perm : (fgGatesList L).Perm
      (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).toList := by
    unfold fgGatesList
    exact List.mergeSort_perm _ _

  -- Sum over fgGatesList = sum over filter = totalRBits
  unfold totalRBits

  -- Get the decoded φ
  let clauseSeedWidthFn : Fin L.encodedφ.clauses.length → Nat := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then L.seedWidth ⟨1 + L.n + i.val, h⟩ else 0
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else LStar.ofBits _ (fun _ => false)
  let φ := LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

  -- Apply the length equality
  have h_len_specific := h_lengths_eq φ L.encodedφ.nvars_pos
  simp only [gateBitsFn] at h_len_specific

  -- The goal reduces to showing map of lengths sums to totalRBits
  -- We have: map lengths = fgGatesList.map L.R (by h_len_specific)
  -- And: sum of fgGatesList.map L.R = sum over filter = totalRBits (by permutation)

  -- Step 1: Rewrite map lengths using h_len_specific
  have h_goal_transform : (List.map (fun v =>
          match emergentConfigAtGate (LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed)
            L.encodedφ.nvars_pos (numGates L) a.extend (v.val - (1 + L.n)) with
          | none => List.replicate (L.R v) false
          | some ⟨R_cfg, cfg⟩ =>
              if (extractAllBits cfg).length = L.R v then extractAllBits cfg
              else List.replicate (L.R v) false)
        (fgGatesList L)).map List.length =
        (fgGatesList L).map (fun v => L.R v) := h_len_specific

  rw [h_goal_transform]

  -- Step 2: Sum of fgGatesList.map L.R = sum over filter
  rw [List.Perm.sum_eq (h_perm.map _)]

  -- Final step: (s.toList.map f).sum = s.sum f
  -- Use List.sum_toFinset: l.toFinset.sum f = (l.map f).sum (when l.Nodup)
  -- For Finset s, s.toList.Nodup holds, and s.toList.toFinset = s
  have h_nodup : (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).toList.Nodup :=
    Finset.nodup_toList _
  conv_rhs => rw [← Finset.toList_toFinset (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v))]
  exact (List.sum_toFinset (fun v => L.R v) h_nodup).symm

-- Axiom audit: Standard Lean axioms only (propext, Classical.choice, Quot.sound)
#print axioms digestsFromAssignmentWithSeeds_length_eq_totalRBits

/-- digestsFromAssignment length equals totalRBits.

    This follows directly from digestsFromAssignmentWithSeeds_length_eq_totalRBits
    since digestsFromAssignment just computes seeds internally. -/
theorem digestsFromAssignment_length_eq_totalRBits
    (L : LStarInstanceFG) (a : Assignment L.n)
    : (digestsFromAssignment L a).length = totalRBits L := by
  unfold digestsFromAssignment
  exact digestsFromAssignmentWithSeeds_length_eq_totalRBits L a _

/-- Digest length equals totalRBits (sum of R values across all FG gates).

    With the FG bottleneck architecture, each gate produces R bits (not 1 parity bit).
    The digest length is the sum of R values for all FG gates.

    For single-gate planted instances: length = R_of φ numGates gateVertex = (log₂ n)². -/
theorem verified_witness_length_eq_totalRBits
    (L : LStarInstanceFG)
    (vw : VerifiedWitness L)
    : vw.w.digestBits.length = totalRBits L := by
  -- VerifiedWitness has digest_correct : w.digestBits = digestsFromAssignmentWithSeeds L ...
  rw [vw.digest_correct]
  exact digestsFromAssignmentWithSeeds_length_eq_totalRBits L vw.w.assignment _

/-- Witness with correct digests has correct length.

    Bridge theorem: Connects HasCorrectDigests to length equality. -/
theorem correct_digests_implies_correct_length
    (L : LStarInstanceFG)
    (W : Witness L.n)
    (h : HasCorrectDigests L W)
    : W.digestBits.length = totalRBits L := by
  -- HasCorrectDigests says W.digestBits = digestsFromAssignmentWithSeeds L W.assignment seeds
  unfold HasCorrectDigests at h
  rw [h]
  exact digestsFromAssignmentWithSeeds_length_eq_totalRBits L W.assignment _

/-- Legacy compatibility: For single-gate planted instances, totalRBits = R at the gate.

    This bridges the old `numGates` based length to the new `totalRBits` semantics. -/
theorem totalRBits_eq_R_for_single_gate
    (L : LStarInstanceFG)
    (h_single : numGates L = 1)
    (v : {v : Fin L.dag.n // L.fg.gateReq v})
    : totalRBits L = L.R v.val := by
  -- With exactly one gate, the sum over FG gates is just R at that gate
  -- h_single says the filter has cardinality 1, so the sum is a singleton
  unfold totalRBits
  -- Unfold numGates in h_single to get Finset.card form
  simp only [numGates] at h_single
  -- The filter has exactly one element, which is v
  -- Show the filter = {v.val} since cardinality = 1 and v is in the filter
  have h_v_mem : v.val ∈ Finset.univ.filter (fun u : Fin L.dag.n => L.fg.gateReq u) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, v.property⟩
  have h_eq_singleton : Finset.univ.filter (fun u : Fin L.dag.n => L.fg.gateReq u) = {v.val} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · exact h_v_mem
    · intro u h_u_mem
      -- Filter has cardinality 1 and both v and u are in filter, so v = u
      have h_subset : ({v.val, u} : Finset (Fin L.dag.n)) ⊆
          Finset.univ.filter (fun u : Fin L.dag.n => L.fg.gateReq u) := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h_v_mem, h_u_mem⟩
      have h_pair_card : ({v.val, u} : Finset (Fin L.dag.n)).card ≤
          (Finset.univ.filter (fun u : Fin L.dag.n => L.fg.gateReq u)).card :=
        Finset.card_le_card h_subset
      rw [h_single] at h_pair_card
      by_cases h_eq : v.val = u
      · exact h_eq.symm
      · -- {v.val, u} has card 2 since v.val ≠ u
        have h_ne : v.val ≠ u := h_eq
        have : ({v.val, u} : Finset (Fin L.dag.n)).card = 2 :=
          Finset.card_pair h_ne
        omega
  -- Sum over singleton is just the single element
  simp only [h_eq_singleton, Finset.sum_singleton]

/-- For planted instances, numGates equals r.gateDigests.length.

    Key structural property: In plant_n construction, FG gates are in 1-1
    correspondence with r.gateDigests entries.

    Precondition: Requires φ to have at least one clause (legitimate OWF requirement).
    This ensures the DAG has sufficient structure to place the FG gate. -/
theorem numGates_eq_gateDigests_length_for_planted
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_clauses : 0 < φ.clauses.length)
    : numGates (plant_n n φ r h_nvars h_dgLen) = r.gateDigests.length := by
  -- Key insight: This is a definitional property of plant_n construction.
  --
  -- In plant_n:
  --   let numGates_internal := r.gateDigests.length
  --   gateReq v := decide ((clause_start ≤ v) ∧ (v < clause_start + numGates_internal))
  --
  -- So gateReq filters vertices in range [clause_start, clause_start + r.gateDigests.length)
  -- The cardinality of this range is r.gateDigests.length (by definition of integer ranges)
  --
  -- With h_single_gate: r.gateDigests.length = 1
  -- So the range [clause_start, clause_start + 1) has exactly 1 element

  unfold numGates
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  rw [h_single]

  let L := plant_n n φ r h_nvars h_dgLen
  let clause_start := 1 + φ.nvars

  -- gateReq is definitionally: (clause_start ≤ v.val) ∧ (v.val < clause_start + 1)
  -- This is the range [clause_start, clause_start + 1), containing exactly clause_start

  -- Step 1: Show clause_start is in the DAG
  have h_clause_in_dag : clause_start < L.dag.n := by
    -- DAG structure: 1 + φ.nvars + φ.clauses.length + reductionTreeSize
    -- We have φ.clauses.length > 0, so dag.n > 1 + φ.nvars = clause_start
    have : L.dag.n = 1 + φ.nvars + φ.clauses.length + Construction.reductionTreeSize φ.clauses.length := by
      rfl  -- Definitional equality from build3SATReductionDAG
    rw [this]
    omega

  -- Step 2: Define the unique gate vertex
  let v_gate : Fin L.dag.n := ⟨clause_start, h_clause_in_dag⟩

  -- Step 3: Show v_gate satisfies gateReq
  have h_gate_satisfies : L.fg.gateReq v_gate = true := by
    -- By definition of plant_n, gateReq checks the range condition
    -- Use decide_eq_true_eq to convert Bool to Prop
    change decide ((clause_start ≤ v_gate.val) ∧ (v_gate.val < clause_start + r.gateDigests.length)) = true
    rw [h_single, decide_eq_true_eq]
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

  -- Step 4: Show v_gate is unique (no other vertex satisfies gateReq)
  have h_unique : ∀ v : Fin L.dag.n, L.fg.gateReq v = true → v = v_gate := by
    intro v h_req
    -- Convert Bool to Prop
    change decide ((clause_start ≤ v.val) ∧ (v.val < clause_start + r.gateDigests.length)) = true at h_req
    rw [h_single, decide_eq_true_eq] at h_req
    obtain ⟨h_ge, h_lt⟩ := h_req
    -- clause_start ≤ v.val < clause_start + 1 → v.val = clause_start
    have h_val_eq : v.val = clause_start := Nat.eq_of_le_of_lt_succ h_ge h_lt
    ext
    exact h_val_eq

  -- Step 5: Filter equals singleton
  have h_filter_eq : Finset.univ.filter (fun v => L.fg.gateReq v) = {v_gate} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h_unique v h
    · intro h; rw [h]; exact h_gate_satisfies

  -- Step 6: Apply card_singleton
  rw [h_filter_eq]
  exact Finset.card_singleton v_gate

/-- totalRBits is positive for planted instances with nvars ≥ 4.

    **Key lemma**: For planted instances, there's at least one FG gate with R > 0.
    This is the crucial bridge for proving digestBits.length > 0.

    Proof sketch:
    1. numGates L = r.gateDigests.length = 1 (by h_single_gate)
    2. So there's exactly one FG gate v
    3. L.R v = R_of φ numGates v.val = (log₂ nvars)² > 0 (by R_of_pos_at_fg_gate)
    4. totalRBits = sum over FG gates = L.R v > 0
-/
theorem totalRBits_pos_for_planted
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_clauses : 0 < φ.clauses.length)
    : totalRBits (plant_n n φ r h_nvars h_dgLen) > 0 := by
  -- Get the single FG gate
  let L := plant_n n φ r h_nvars h_dgLen
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  have h_numGates : numGates L = 1 := by
    have := numGates_eq_gateDigests_length_for_planted n φ r h_nvars h_dgLen h_clauses
    rw [this, h_single]

  -- totalRBits is the sum over FG gates
  unfold totalRBits

  -- Unfold numGates in h_numGates to get Finset.card = 1
  simp only [numGates] at h_numGates

  -- h_numGates says the filter has exactly one element → it's nonempty
  have h_nonempty : (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    rw [h_empty, Finset.card_empty] at h_numGates
    omega

  -- All R values at FG gates are positive (R = (log₂ nvars)² > 0)
  have h_all_pos : ∀ v ∈ (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)), L.R v > 0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    -- v is an FG gate, so L.R v = R_of φ numGates v.val > 0
    -- For plant_n, L.R = R_of φ r.gateDigests.length
    -- R_of_pos_at_fg_gate gives R > 0 for FG gates when nvars ≥ 4
    have h_R_eq : L.R v = Foundations.R_of φ r.gateDigests.length v.val := rfl
    rw [h_R_eq]
    apply Foundations.R_of_pos_at_fg_gate φ r.gateDigests.length v.val h_nvars
    -- Need to show v is in the FG range for R_of:
    -- (1 + φ.nvars ≤ v.val) ∧ (v.val < min (1 + φ.nvars + numGates) (1 + φ.nvars + nclauses))
    -- plant_n's gateReq gives: (1 + φ.nvars ≤ v.val) ∧ (v.val < 1 + φ.nvars + numGates)
    -- With numGates = 1 and nclauses ≥ 1: min (...+1) (...+nclauses) = ...+1
    -- hv : L.fg.gateReq v = true, where L = plant_n n φ r h_nvars h_dgLen
    -- Unfold L's definition to get the gateReq predicate
    change (plant_n n φ r h_nvars h_dgLen).fg.gateReq v = true at hv
    simp only [plant_n, decide_eq_true_eq] at hv
    constructor
    · exact hv.1
    · -- v.val < 1 + φ.nvars + r.gateDigests.length
      -- Need: v.val < min (1 + φ.nvars + numGates) (1 + φ.nvars + nclauses)
      -- Since numGates = 1 and nclauses ≥ 1, min picks ...+numGates
      have h_min : min (1 + φ.nvars + r.gateDigests.length) (1 + φ.nvars + φ.clauses.length) =
                   1 + φ.nvars + r.gateDigests.length := by
        apply Nat.min_eq_left
        rw [h_single]
        omega
      rw [h_min]
      exact hv.2

  -- Sum over nonempty set with all positive elements is positive
  exact Finset.sum_pos h_all_pos h_nonempty

/-- Witness with correct digests has length = totalRBits for planted instances.

    With R-bit architecture, digestBits.length = totalRBits L (sum of R values).
    For single-gate planted instances, this equals R_of φ numGates gateVertex.

    NOTE: This is NOT equal to r.gateDigests.length (= numGates = 1).
    The old equation was valid when each gate produced 1 bit, but now each
    gate produces R bits.

    Precondition: Requires φ to have at least one clause (legitimate OWF requirement). -/
theorem correct_digests_length_eq_totalRBits_planted
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_clauses : 0 < φ.clauses.length)
    (W : Witness φ.nvars)
    (h_correct : HasCorrectDigests (plant_n n φ r h_nvars h_dgLen) W)
    : W.digestBits.length = totalRBits (plant_n n φ r h_nvars h_dgLen) := by
  exact correct_digests_implies_correct_length (plant_n n φ r h_nvars h_dgLen) W h_correct

-- Note: canonicalized_digest_matches_assignment theorem removed
-- It depended on `canonicalize` which was removed due to OAP hardness
-- (Cannot compute valid digests without solving the cryptographic puzzle)

/-- Extract parity bit from gate digest vector.

    r.gateDigests[i] is a Vector Bool dgLen where position 0 stores the parity bit.
    This extracts that parity bit (what goes in w.digestBits[i]).

    Design: WellFormedRandomness guarantees `digest.get 0 = fgDigestBit cfg`,
    so we simply extract position 0 of the digest vector. -/
noncomputable def extractParityFromGateDigest {dgLen : Nat} (h_pos : 0 < dgLen) (vec : Vector Bool dgLen) : Bool :=
  vec.get ⟨0, h_pos⟩

/-- Totality theorem imported from PlantCore.lean.

    For valid gate indices in planted instances with well-formed randomness,
    emergentConfigAtGate returns Some. -/
theorem emergentConfigAtGate_isSome_for_planted_local
    (φ : CNF) (r : Randomness φ.nvars) (h_wf : WellFormedRandomness φ r)
    (h_clauses : 0 < φ.clauses.length)
    (i : Fin r.gateDigests.length)
    : (emergentConfigAtGate φ φ.nvars_pos r.gateDigests.length r.assignment.extend i.val).isSome :=
  -- Direct application of PlantCore theorem (defined in LStar.StructuralOWF namespace)
  LStar.StructuralOWF.emergentConfigAtGate_isSome_for_planted φ r h_wf h_clauses i

/-- Helper lemma: For valid gate indices in planted instances, emergentConfigAtGate returns some. -/
lemma emergentConfigAtGate_some_of_valid_index
    (φ : CNF) (r : Randomness φ.nvars) (h_wf : WellFormedRandomness φ r)
    (h_clauses : 0 < φ.clauses.length)
    (i : Nat) (h_i_bound : i < r.gateDigests.length)
    : ∃ R_val cfg, emergentConfigAtGate φ φ.nvars_pos r.gateDigests.length r.assignment.extend i = some ⟨R_val, cfg⟩ := by
  -- Use the local theorem
  have h_isSome := emergentConfigAtGate_isSome_for_planted_local φ r h_wf h_clauses ⟨i, h_i_bound⟩
  -- Convert isSome to exists
  rw [Option.isSome_iff_exists] at h_isSome
  obtain ⟨val, h_eq⟩ := h_isSome
  -- val has type PSigma, extract components
  obtain ⟨R_val, cfg⟩ := val
  use R_val, cfg

/-! ## Parity Equality from Gate Config Uniqueness

Alternative approach that uses minimal axiom `gate_configs_unique_on_gates` instead of
requiring full assignment equality.

Key difference:
- Old approach: Needs hypothesis `h_assign_eq : W.assignment = r.assignment`
  (strong requirement - full assignment equality on infinite space)
- New approach: Uses `gate_configs_unique_on_gates` directly
  (minimal axiom - only gate config equality)

Why this works:
1. Gate config equality implies parity equality (configs have same parity bit)
2. Parity equality implies digest equality (digests encode parities)
3. No need for full assignment equality

Migration path: Prefer this theorem over `assignment_eq_implies_parity_eq`.
-/

/-! ### Note on Parity Computation

Key insight: `digestsFromAssignment` is a pure function of the assignment.

```lean
def digestsFromAssignment (L : LStarInstanceFG) (a : Assignment) : List Bool :=
  let φ := decodeφFromAssignment L a
  List.ofFn (fun (i : Fin (numGates L)) =>
    match emergentConfigAtGate φ φ.nvars_pos (numGates L) a i.val with
    | none => false
    | some ⟨_R, cfg⟩ => computeGateDigest cfg  -- Pure computation
  )
```

No reference to planted randomness r. It only depends on:
1. The encoded formula L.encodedφ (decoded using a)
2. The assignment a (input)
3. Pure computation (emergentConfig → parity)

Implication: Middle layers (VerifiedWitness, TMToExecutionPrefix) can use witness
configs directly without comparing to planted randomness.

Where uniqueness matters: Only in Security.lean, where we need to show that
a successful inverter's output is consistent with the planted instance. That's
where the security assumption lives - not in the infrastructure.

Previous approach (overly strong):
- EmergentConfig: axiom about assignment/config equality
- VerifiedWitness: prove W's parity = r's parity using axiom
- TMToExecutionPrefix: use parity equality

Current approach (clean architecture):
- EmergentConfig: No axioms (pure structural lemmas)
- VerifiedWitness: use `digestsFromAssignment` directly (pure function)
- TMToExecutionPrefix: use witness's configs (no comparison to r)
- Security.lean: information-theoretic bounds (includes uniqueness where actually needed)

-/

/-! ## Summary: How This Eliminates Length and Value Equality Proofs

The Strategy:
1. Don't try to prove w.digestBits is correct (it's unconstrained)
2. Instead: Use `canonicalize L w` to recompute digests from w.assignment
3. The recomputed digests are correct by construction (rfl proof)

For length equality (`w.digestBits.length = r.gateDigests.length`):
```lean
let vw := canonicalize L w
have : vw.digest.toList.length = r.gateDigests.length := by
  apply correct_digests_length_eq_randomness_length
```
Uses: `numGates_eq_gateDigests_length_for_planted` (counting lemma)

For value equality (`w.digestBits[i] = r.gateDigests[i]`):
```lean
let vw := canonicalize L w
have : vw.digest.get i = r.gateDigests.get i := by
  apply assignment_eq_implies_digest_eq
  exact witness_assignment_eq_planted_assignment  -- existing axiom
```
Uses: `assignment_eq_implies_digest_eq` (expand WellFormedRandomness)

All proofs are mechanical Finset/Vector manipulation with no axioms needed.
-/

/-! ## LStarVerifier Bridge for Planted Instances

For planted instances with canonical witnesses (digestBits = digestsFromAssignment),
LStarVerifier L w ↔ φ.satisfies w.assignment.

Key insight: entropyFromWitness and entropyFromAssignment agree on source/variable
nodes, and clause seeds only depend on source/variable ancestors. Therefore the
decoded φ in LStarVerifier equals the decoded φ from decodeφFromAssignment.
-/

/-- entropyFromWitness agrees with entropyFromAssignment on source and variable nodes.

    For v.val = 0 (source) or v.val ≤ L.n (variable), both functions return the
    same entropy value (derived from the assignment).
-/
theorem entropyFromWitness_eq_entropyFromAssignment_on_source_variable
    (L : LStarInstanceFG) (W : Witness L.n) (v : Fin L.dag.n)
    (h_source_or_var : v.val = 0 ∨ v.val ≤ L.n) :
    entropyFromWitness L W .exponential v = entropyFromAssignment L W.assignment v := by
  unfold entropyFromWitness entropyFromAssignment
  cases h_source_or_var with
  | inl h_source => simp [h_source]
  | inr h_var =>
    by_cases h_zero : v.val == 0
    · simp [h_zero]
    · simp [h_zero, h_var, Witness.assignmentInf]

/-- entropyFromWitness equals entropyFromAssignment on non-gate clause nodes.

    For v.val > L.n and L.fg.gateReq v = false (non-gate clause nodes),
    both functions return zero entropy. -/
theorem entropyFromWitness_eq_entropyFromAssignment_on_non_gate_clause
    (L : LStarInstanceFG) (W : Witness L.n) (v : Fin L.dag.n)
    (h_not_var : v.val > L.n) (h_not_gate : L.fg.gateReq v = false) :
    entropyFromWitness L W .exponential v = entropyFromAssignment L W.assignment v := by
  unfold entropyFromWitness entropyFromAssignment
  -- v.val > L.n, so v.val ≠ 0 and v.val > L.n
  -- Both functions return zero entropy in this case
  -- Use split to handle all the if-then-else branches
  split_ifs <;>
    first
    | rfl
    | (simp only [beq_iff_eq] at *; omega)
    | (rename_i h; rw [h_not_gate] at h; simp at h)

/-- Clause seeds from entropyFromWitness equal clause seeds from entropyFromAssignment.

    For non-gate clause vertices (index = 1 + L.n + i where i ≥ numGates L), the seed
    depends only on source/variable ancestors. Since entropyFromWitness and
    entropyFromAssignment agree on source/variable nodes AND on non-gate clause nodes,
    the clause seeds are identical.

    The hypothesis i ≥ numGates L ensures we're looking at a non-gate clause position.
    With single-gate architecture (numGates = 1), this means i ≥ 1.

    Uses: computeSeedChain_ext_ancestors (only requires agreement on ancestors, not all smaller indices)
-/
theorem clause_seeds_eq_for_witness_and_assignment
    (L : LStarInstanceFG) (W : Witness L.n)
    (i : Nat) (h_i : 1 + L.n + i < L.dag.n)
    (h_not_gate : i ≥ numGates L)  -- Ensures target is a non-gate clause
    (h_target_not_gateReq : L.fg.gateReq ⟨1 + L.n + i, h_i⟩ = false)  -- Target is not in gateReq
    (h_ancestors_in_var_layer : ∀ u, LStar.LStarInstanceFull.isAncestorOf L.dag u ⟨1 + L.n + i, h_i⟩ → u.val ≤ L.n) :
    L.toLStarInstanceFull.computeSeedChain (entropyFromWitness L W) ⟨1 + L.n + i, h_i⟩ =
    L.toLStarInstanceFull.computeSeedChain (entropyFromAssignment L W.assignment) ⟨1 + L.n + i, h_i⟩ := by
  -- Apply computeSeedChain_ext_ancestors: only need agreement on ancestors and target
  apply LStar.LStarInstanceFull.computeSeedChain_ext_ancestors L.toLStarInstanceFull
    (entropyFromWitness L W) (entropyFromAssignment L W.assignment) ⟨1 + L.n + i, h_i⟩
  · -- Entropy agreement at target: both return zero since target is non-gate clause
    have h_target_not_var : (1 + L.n + i) > L.n := by omega
    exact entropyFromWitness_eq_entropyFromAssignment_on_non_gate_clause L W ⟨1 + L.n + i, h_i⟩ h_target_not_var h_target_not_gateReq
  · -- Entropy agreement on all ancestors: ancestors are in variable layer
    intro u h_ancestor
    have h_u_in_var : u.val ≤ L.n := h_ancestors_in_var_layer u h_ancestor
    exact entropyFromWitness_eq_entropyFromAssignment_on_source_variable L W u (Or.inr h_u_in_var)

end LStar.StructuralOWF.Foundations
