import Layer5_Applications.PvsNP.ComplexityClasses.Encoding.LStarEncoding
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
import Layer3_InformationBounds.ConstraintSystem.ConstraintSystem  -- For extractAllBits

/-! ## Bitstring OWF and Explicit NP \ P Language

**Purpose**: Provide fully textbook-style definitions over {0,1}* and prove
an explicit separation via `PrefixLangBits_in_NP_not_in_P`.

**Components**:
1. `owf_bits`: The one-way function f : {0,1}^k → {0,1}* in bitstring form
2. `OWFInversionLang_bits`: The inversion language over bitstrings
3. `PrefixLangSigma`: The prefix-extension language (structured type)
4. `PrefixLangBits`: The prefix-extension language encoded as bitstrings
5. `exists_language_in_NP_not_in_P_clean`: ∃ L ⊆ {0,1}*, L ∈ NP \ P

**Connection to Main Theorem**:
This file bridges the gap between:
- `P_ne_NP` (StructuralOWFBridge.lean): Uses abstract types, proves ¬PeqNP_classical
- The prefix-extension machinery from `uniform_search_from_prefix_oracle`
The key insight is that the prefix language directly connects to the search-to-decision
reduction, avoiding the need for self-reducibility of the range language.
-/

namespace LStar.Encoding.BitstringOWF

open LStar.Encoding
open LStar.Complexity
open LStar.Complexity.StructuralOWFBridge
open LStar.Complexity.BitstringBridge
open LStar.StructuralOWF
open Foundations.CutConstraint

/-! ## Profile-Consistent Digest Computation (Clean Fix)

The original `digestsFromAssignmentWithSeeds` uses `emergentConfigAtGate` which internally
uses `R_of` (QP profile: R = (log n)²). However, `plant_flat` uses `R_of_flat`
(exponential profile: R = n), causing an R mismatch that triggers the fallback path.

This section provides `digestsFromAssignmentWithSeeds_flat` which uses `emergentConfigAtGate_flat`,
ensuring profile consistency. Both the planted instance and digest computation use R_of_flat,
so emergent configs match properly without needing the fallback.
-/

/-- **Flat profile digest computation**: Uses emergentConfigAtGate_flat for profile consistency.

    Unlike `digestsFromAssignmentWithSeeds` which uses the QP profile (R = (log n)²),
    this version uses the flat/exponential profile (R = n), matching `plant_flat`.

    **Key property**: For planted instances created with `plant_flat`, the R values
    from `emergentConfigAtGate_flat` match `L.R v` exactly, so the actual emergent
    bits are returned (not the fallback zeros).

    **Parameters**:
    - L: L* instance (created with plant_flat)
    - a: Assignment
    - seeds: Seed chain for decoding
-/
noncomputable def digestsFromAssignmentWithSeeds_flat
    (L : LStarInstanceFG)
    (a : Assignment L.n)
    (seeds : (v : Fin L.dag.n) → LStar.Seed (L.seedWidth v))
    : List Bool :=
  -- Seed width function for clause indices (matches decodeφFromAssignment)
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
  -- Decode φ using dependent seed widths
  let φ := LStar.OAP.decodeWithOAPDep L.encodedφ clauseSeedWidthFn getSeed

  -- Create flat list using emergentConfigAtGate_flat (matches plant_flat's R_of_flat)
  let gateDigests := (Foundations.fgGatesList L).map (fun v =>
    let R := L.R v
    let gateIndex := v.val - (1 + L.n)
    -- Use emergentConfigAtGate_flat instead of emergentConfigAtGate
    match emergentConfigAtGate_flat φ L.encodedφ.nvars_pos (Foundations.numGates L) a.extend gateIndex with
    | none => List.replicate R false  -- Fallback (shouldn't happen for valid instances)
    | some ⟨R_cfg, cfg⟩ =>
        let bits := LStar.StructuralOWF.Foundations.CutConstraint.extractAllBits cfg
        if bits.length = R then bits
        else List.replicate R false  -- Fallback if R mismatch (shouldn't happen with flat profile)
  )
  gateDigests.flatten

/-- Convenience version: computes seeds internally from assignment. -/
noncomputable def digestsFromAssignment_flat
    (L : LStarInstanceFG)
    (a : Assignment L.n)
    : List Bool :=
  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull (Foundations.entropyFromAssignment L a)
  digestsFromAssignmentWithSeeds_flat L a seeds

/-! ### Key Lemma: Profile Consistency for Flat Planted Instances

For instances created with `plant_flat`, the `emergentConfigAtGate_flat` function
returns R values that MATCH `L.R v`. This is the crux of the clean fix:
- Both `plant_flat` and `emergentConfigAtGate_flat` use `R_of_flat`
- Therefore R_cfg = L.R v (no mismatch!)
- The actual emergent bits are returned, not fallback zeros
-/

/-- For flat-profile planted instances, emergentConfigAtGate_flat returns R = L.R v.

    This is the key lemma that eliminates the profile mismatch:
    - plant_flat uses R_of_flat to set L.R v = nvars at FG gates
    - emergentConfigAtGate_flat uses R_of_flat internally
    - Therefore R_cfg from emergentConfigAtGate_flat equals L.R v

    **Consequence**: The actual emergent bits are used (not fallback zeros).

    **Proof sketch**:
    1. emergentConfigAtGate_R_component_flat gives: R_cfg = R_of_flat φ numGates (1 + φ.nvars + gateIndex)
    2. plant_flat_R_eq_nvars gives: L.R v = φ.nvars for FG gates
    3. R_of_flat at FG gates returns φ.nvars
    4. Therefore R_cfg = L.R v -/
lemma emergentConfigAtGate_flat_R_matches_L_R
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : φ.clauses.length ≥ 1)
    (a : AssignmentInf) (gateIndex : Nat)
    (R_cfg : Nat) (cfg : Fin (2^R_cfg))
    (h_gate_valid : gateIndex < r.gateDigests.length)
    (h_emergent : emergentConfigAtGate_flat φ (by omega : φ.nvars > 0) r.gateDigests.length a gateIndex = some ⟨R_cfg, cfg⟩) :
    R_cfg = φ.nvars := by
  -- emergentConfigAtGate_flat returns R = R_of_flat φ numGates (1 + φ.nvars + gateIndex)
  have h_R_from_emergent := emergentConfigAtGate_R_component_flat φ (by omega : φ.nvars > 0)
    r.gateDigests.length a gateIndex R_cfg cfg h_emergent
  rw [h_R_from_emergent]
  -- Goal: R_of_flat φ r.gateDigests.length (1 + φ.nvars + gateIndex) = φ.nvars
  -- R_of_flat returns φ.nvars for vertices in the FG range
  unfold Foundations.R_of_flat
  simp only []
  -- The vertex 1 + φ.nvars + gateIndex is in the FG range since gateIndex < r.gateDigests.length
  have h_single := r.h_single_gate
  have h_clause_start : 1 + φ.nvars ≤ 1 + φ.nvars + gateIndex := by omega
  have h_fg_end : 1 + φ.nvars + gateIndex < min (1 + φ.nvars + r.gateDigests.length) (1 + φ.nvars + φ.clauses.length) := by
    apply Nat.lt_min.mpr
    constructor
    · omega
    · -- r.gateDigests.length = 1 ≤ φ.clauses.length (given by h_clauses_pos)
      omega
  split
  · rfl
  · -- Contradiction: the condition should be true
    rename_i h_neg
    push_neg at h_neg
    omega

/-! ## Bitstring One-Way Function

The OWF takes a bitstring witness w ∈ {0,1}^(2n+64) and produces an encoded
L* instance. This is the composition:

    w : Bits (expWLen n)
    ↓ bitsToRandomness_exp
    r : Randomness n
    ↓ plant_flat
    L : LStarInstanceFG
    ↓ encodeBits
    bs : List Bool
-/

/-- The aligned CNF family used in the main proof. -/
abbrev Φ := LStar.StructuralOWF.Theorems.alignedCNFFamily

/-- The bitstring one-way function: w ↦ encode(plant(w)).

    Given a bitstring witness w of length 2n + 64, produces an encoded
    L* instance. This is the composition of:
    1. bitsToRandomness_exp: Convert bits to randomness
    2. plant_flat: Create planted instance
    3. encodeBits: Encode to bitstring
-/
noncomputable def owf_bits (n : Nat) (h_n : n ≥ 128) (w : Bits (expWLen n)) : List Bool :=
  let h_nvars_eq := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
  let h_nvars : (Φ n).nvars ≥ 4 := by rw [h_nvars_eq n h_n]; omega
  let h_aligned : AlignedCNFConstraints (Φ n) := {
    clauses_le := by
      unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
      simp only [List.length_ofFn]
      omega
    is_3sat := by
      intro c h_c
      unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily at h_c
      simp only [List.mem_ofFn] at h_c
      obtain ⟨i, rfl⟩ := h_c
      simp only [List.length_singleton]
      omega
  }
  let r := bitsToRandomness_exp n (by omega : n > 0) w
  let r_φ : Randomness (Φ n).nvars := (h_nvars_eq n h_n).symm ▸ r
  encodeBits (plant_flat n (Φ n) r_φ h_nvars h_aligned)

/-! ## Planted Instances are Yes-Instances

Key lemma: If r satisfies the CNF φ, then plant_flat(φ, r) is a yes-instance
(has a valid witness for the HasCorrectDigests predicate).
-/

/-! ### Auxiliary Lemmas for planted_satisfying_is_yes_instance

The proof requires showing:
1. entropyFromWitness L W = plant_flat_entropy φ r' (entropy equality)
2. By computeSeedChain_ext, the seed chains are equal
3. digestsFromAssignmentWithSeeds L W.assignment seeds = W.digestBits
-/

/-- For planted instances, fgGatesList contains exactly one gate at position 1 + φ.nvars. -/
lemma plant_flat_fgGatesList_singleton
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : 0 < φ.clauses.length) :
    let L := plant_flat n φ r h_nvars h_aligned
    (Foundations.fgGatesList L).length = 1 := by
  simp only
  rw [Foundations.fgGatesList_length]
  unfold Foundations.numGates
  -- The filter selects vertices where gateReq holds
  -- For plant_flat, gateReq v = (1 + φ.nvars ≤ v.val) ∧ (v.val < 1 + φ.nvars + r.gateDigests.length)
  -- Since r.h_single_gate says r.gateDigests.length = 1, exactly one vertex satisfies this
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  -- The FG gate is at position 1 + φ.nvars (clause_start)
  -- We need to show the filter has cardinality 1
  let L := plant_flat n φ r h_nvars h_aligned
  -- Use the fact that gateReq is true iff v.val ∈ [clause_start, clause_start + 1)
  have h_gate_interval : ∀ v : Fin L.dag.n, L.fg.gateReq v ↔
      ((1 + φ.nvars) ≤ v.val ∧ v.val < (1 + φ.nvars) + 1) := by
    intro v
    simp only [L, plant_flat, decide_eq_true_iff]
    rw [h_single]
  -- Convert to showing there's exactly one vertex in [clause_start, clause_start+1)
  -- which means exactly v.val = clause_start = 1 + φ.nvars
  -- First, we need clause_start < L.dag.n (gate exists)
  have h_dag_n : L.dag.n = 1 + φ.nvars + φ.clauses.length + Construction.BalancedBinaryTree.size φ.clauses.length := by
    simp only [L, plant_flat, build3SATReductionDAG, Construction.build3SATReductionDAG,
      Construction.totalNodes, Construction.reductionTreeSize]
  have h_gate_exists : 1 + φ.nvars < L.dag.n := by
    rw [h_dag_n]
    have : φ.clauses.length ≥ 1 := h_clauses_pos
    omega
  -- The unique gate vertex
  let v_gate : Fin L.dag.n := ⟨1 + φ.nvars, h_gate_exists⟩
  -- Show filter = {v_gate}
  have h_filter_eq : (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)) = {v_gate} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [h_gate_interval]
    constructor
    · intro ⟨h_lo, h_hi⟩
      have : v.val = 1 + φ.nvars := by omega
      exact Fin.ext this
    · intro h_eq
      subst h_eq
      simp only [v_gate]
      exact ⟨Nat.le_refl _, Nat.lt_add_one _⟩
  rw [h_filter_eq]
  simp only [Finset.card_singleton]

/-- Key property: For planted instances with single gate, the total R bits equals R of the gate.

    This is because numGates = 1 and totalRBits = sum over single gate = L.R v_gate = nvars. -/
lemma plant_flat_totalRBits_eq_n
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : 0 < φ.clauses.length) :
    let L := plant_flat n φ r h_nvars h_aligned
    Foundations.totalRBits L = φ.nvars := by
  simp only
  let L := plant_flat n φ r h_nvars h_aligned
  -- totalRBits L = (Finset.univ.filter gateReq).sum (fun v => L.R v)
  -- For single gate: filter = {v_gate}, so sum = L.R v_gate
  -- By plant_flat_R_eq_nvars: L.R v_gate = φ.nvars (for FG gate)
  unfold Foundations.totalRBits
  -- First, show the filter has exactly one element
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  -- The FG gate filter equals {v_gate} where v_gate.val = 1 + φ.nvars
  have h_dag_n : L.dag.n = 1 + φ.nvars + φ.clauses.length + Construction.BalancedBinaryTree.size φ.clauses.length := by
    simp only [L, plant_flat, build3SATReductionDAG, Construction.build3SATReductionDAG,
      Construction.totalNodes, Construction.reductionTreeSize]
  have h_gate_exists : 1 + φ.nvars < L.dag.n := by
    rw [h_dag_n]
    have : φ.clauses.length ≥ 1 := h_clauses_pos
    omega
  let v_gate : Fin L.dag.n := ⟨1 + φ.nvars, h_gate_exists⟩
  have h_gate_interval : ∀ v : Fin L.dag.n, L.fg.gateReq v ↔
      ((1 + φ.nvars) ≤ v.val ∧ v.val < (1 + φ.nvars) + 1) := by
    intro v
    simp only [L, plant_flat, decide_eq_true_iff]
    rw [h_single]
  have h_filter_eq : (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)) = {v_gate} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [h_gate_interval]
    constructor
    · intro ⟨h_lo, h_hi⟩
      have : v.val = 1 + φ.nvars := by omega
      exact Fin.ext this
    · intro h_eq
      subst h_eq
      simp only [v_gate]
      exact ⟨Nat.le_refl _, Nat.lt_add_one _⟩
  rw [h_filter_eq, Finset.sum_singleton]
  -- Now show L.R v_gate = φ.nvars
  have h_gateReq : L.fg.gateReq v_gate := by
    rw [h_gate_interval]
    simp only [v_gate]
    exact ⟨Nat.le_refl _, Nat.lt_add_one _⟩
  exact plant_flat_R_eq_nvars n φ r h_nvars h_aligned v_gate h_gateReq

/-- For single-gate planted instances, digestBits indexing simplifies.

    Since gate_idx = 0 and W.digestBits = gateDigests[0].toList,
    indexing into W.digestBits at position i gives the same as gateDigests[0][i]. -/
lemma single_gate_digestBits_eq {dgLen : Nat} (digest : Vector Bool dgLen)
    (i : Nat) (h_i : i < dgLen) :
    digest.toList.get ⟨i, by simp [Vector.toList]; exact h_i⟩ = digest.get ⟨i, h_i⟩ := by
  simp [Vector.toList, Vector.get, List.get_eq_getElem]

/-! ### Entropy Equality Lemmas for Planted Instances

These lemmas establish that for planted instances with well-formed randomness,
`entropyFromWitness L W v = plant_flat_entropy φ r' dag seedWidth v` for each vertex type.
-/

/-- Entropy equality at source vertex (v=0): both return zero seed. -/
lemma entropy_eq_at_source
    (L : LStarInstanceFG) (W : Witness L.n)
    (v : Fin L.dag.n) (h_v : v.val = 0) :
    Foundations.entropyFromWitness L W .exponential v =
    LStar.ofBits (L.seedWidth v) (fun _ => false) := by
  unfold Foundations.entropyFromWitness
  simp only [h_v, beq_self_eq_true, ↓reduceIte]

/-- Entropy equality at variable vertices: both use assignment bits.
    For planted instances, W.assignment = r.assignment (modulo type transport). -/
lemma entropy_eq_at_variable
    (L : LStarInstanceFG) (W : Witness L.n)
    (v : Fin L.dag.n) (h_v_ne : v.val ≠ 0) (h_v_le : v.val ≤ L.n)
    (h_not_gate : L.fg.gateReq v = false) :
    Foundations.entropyFromWitness L W .exponential v =
    LStar.ofBits (L.seedWidth v) (fun i =>
      if i.val = 0 then W.assignmentInf (v.val - 1) else false) := by
  unfold Foundations.entropyFromWitness
  have h_beq : (v.val == 0) = false := by simp [beq_eq_false_iff_ne, h_v_ne]
  simp only [Foundations.computeR, h_beq, h_v_le, ↓reduceIte, h_not_gate, ite_false]
  -- Now need to show the ofBits functions are equal (they differ only in == vs =)
  apply LStar.ofBits_ext
  intro j
  simp only [beq_iff_eq]

/-- For planted instances, the unique FG gate is at position 1 + nvars. -/
lemma plant_flat_fg_gate_position
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (v : Fin (plant_flat n φ r h_nvars h_aligned).dag.n)
    (h_gate : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v) :
    v.val = 1 + φ.nvars := by
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  -- gateReq v ↔ (1 + φ.nvars ≤ v.val) ∧ (v.val < 1 + φ.nvars + 1)
  -- Access the gateReq definition from plant_flat
  simp only [plant_flat, FrontierGateConfig.gateReq, decide_eq_true_iff,
    Bool.and_eq_true, decide_eq_true_eq, h_single] at h_gate
  omega

/-- For planted instances, seedWidth at FG gate equals nvars.

    This follows from the construction: at clause layer vertices,
    seedWidth = sum(parent seedWidths) + R(v), and for exponential profile
    R(v) = nvars at FG gates while parents (variables) have seedWidth = 0.

    **Proof strategy**: Uses `seedWidth_eq_R_for_fg_gate_flat` which proves
    seedWidth = R for FG gates (because parent seedWidths are all 0), then
    uses `plant_flat_R_eq_nvars` to get R = nvars. -/
lemma plant_flat_seedWidth_at_fg_gate
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : 0 < φ.clauses.length)
    (v : Fin (plant_flat n φ r h_nvars h_aligned).dag.n)
    (h_gate : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v) :
    (plant_flat n φ r h_nvars h_aligned).seedWidth v = φ.nvars := by
  -- The FG gate position
  have h_v_pos : v.val = 1 + φ.nvars := plant_flat_fg_gate_position n φ r h_nvars h_aligned v h_gate
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  have h_nvars_pos : φ.nvars > 0 := by omega

  -- plant_flat.seedWidth = Construction.computeSeedWidth φ numGates R_of_flat
  -- For FG gates: seedWidth = R (because parent seedWidths are all 0)
  -- And R = nvars at FG gates (by R_of_flat definition)

  let numGates := r.gateDigests.length
  let L := plant_flat n φ r h_nvars h_aligned

  -- Direct computation: seedWidth = R at FG gates
  -- Step 1: Show seedWidth = R using the capacity equation
  have h_R_val := Foundations.R_of_flat φ numGates

  -- The key is that parents of v (an FG gate) are in the variable layer
  -- Variable layer nodes have seedWidth = 0

  -- First, show v is at clause layer
  have h_v_clause : Construction.classifyNode φ.nvars φ.clauses.length v.val = .clause := by
    rw [h_v_pos]
    unfold Construction.classifyNode
    have h1 : ¬(1 + φ.nvars = 0) := by omega
    have h2 : ¬(1 + φ.nvars ≤ φ.nvars) := by omega
    have h3 : 1 + φ.nvars ≤ φ.nvars + φ.clauses.length := by omega
    simp only [h1, h2, h3, ↓reduceIte]

  -- Parent seedWidths sum to 0
  have h_parent_sum_zero : (∑ u ∈ L.dag.parents v, L.seedWidth u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    -- u is a parent of v, which is at the FG gate position
    -- Parents are in the variable layer (indices 1 to nvars)
    have h_parent_lt := Construction.parents_have_smaller_indices φ numGates v u hu
    -- All parents have v.val > u.val, so u.val < 1 + φ.nvars (variable layer)
    have h_u_below : u.val < 1 + φ.nvars := by
      calc u.val < v.val := h_parent_lt
        _ = 1 + φ.nvars := h_v_pos
    -- Variable layer nodes have seedWidth = 0 by seedWidth_eq_zero_for_variable_layer
    exact seedWidth_eq_zero_for_variable_layer φ h_nvars_pos numGates u h_u_below

  -- By capacity equation: seedWidth = parentSum + R = 0 + R = R
  -- L.seedWidth v = Construction.computeSeedWidth φ numGates R_val v (by definition)
  -- L.R v = R_val v.val (by definition)
  let R_val := Foundations.R_of_flat φ numGates

  have h_cap := Construction.seedWidth_satisfies_capacity φ numGates R_val v
  -- h_cap: (∑ u ∈ ...) + R_val v.val = computeSeedWidth φ numGates R_val v

  have h_sw_eq_R : L.seedWidth v = L.R v := by
    -- L.seedWidth v = computeSeedWidth φ numGates R_val v (definitional)
    -- L.R v = R_val v.val (definitional)
    -- Now use h_cap after proving parent sum is 0
    have h_parent_sum_zero' : (∑ u ∈ (Construction.build3SATReductionDAG φ numGates).parents v,
        Construction.computeSeedWidth φ numGates R_val u) = 0 := h_parent_sum_zero
    -- Unfold definitions
    simp only [L, plant_flat]
    calc Construction.computeSeedWidth φ numGates R_val v
        = (∑ u ∈ (Construction.build3SATReductionDAG φ numGates).parents v,
            Construction.computeSeedWidth φ numGates R_val u) + R_val v.val := h_cap.symm
      _ = 0 + R_val v.val := by rw [h_parent_sum_zero']
      _ = R_val v.val := by omega

  -- Finally, R = nvars at FG gates
  rw [h_sw_eq_R]
  exact plant_flat_R_eq_nvars n φ r h_nvars h_aligned v h_gate

/-- Entropy equality at FG gate for planted single-gate instances.

    For planted instances with W.digestBits = r.gateDigests[0].toList,
    the entropy from witness equals the entropy from randomness at the FG gate.

    **Key insight**: Both functions read the first R bits from the same digest:
    - entropyFromWitness reads W.digestBits[i] for i < R
    - plant_flat_entropy reads r.gateDigests[0][i] for i < dgLen

    Since W.digestBits = r.gateDigests[0].toList and R ≤ dgLen (by WellFormedRandomness_flat),
    both produce identical entropy values.

    **Proof approach**: Use Seed.ext to prove bit-by-bit equality:
    - LHS at bit i: reads W.digestBits[0 * R + i] = W.digestBits[i]
    - RHS at bit i: reads r.gateDigests[0][i]
    - By h_digestBits: W.digestBits[i] = r.gateDigests[0].toList[i] = r.gateDigests[0][i] -/
lemma entropy_eq_at_fg_gate
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : 0 < φ.clauses.length)
    (h_wf : WellFormedRandomness_flat φ r)
    (W : Witness φ.nvars)
    (h_digestBits : W.digestBits = (r.gateDigests.get ⟨0, by rw [r.h_single_gate]; omega⟩).toList)
    (v : Fin (plant_flat n φ r h_nvars h_aligned).dag.n)
    (h_gate : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v) :
    let L := plant_flat n φ r h_nvars h_aligned
    Foundations.entropyFromWitness L (plant_flat_n n φ r h_nvars h_aligned ▸ W) .exponential v =
    plant_flat_entropy φ r h_nvars (L.dag) (L.seedWidth) v := by
  -- Key facts
  let L := plant_flat n φ r h_nvars h_aligned
  have h_v_pos : v.val = 1 + φ.nvars := plant_flat_fg_gate_position n φ r h_nvars h_aligned v h_gate
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  have h_dgLen_ge : r.dgLen ≥ φ.nvars := h_wf.2.2.2.1
  have h_L_n : L.n = φ.nvars := plant_flat_n n φ r h_nvars h_aligned
  have h_sw : L.seedWidth v = φ.nvars := plant_flat_seedWidth_at_fg_gate n φ r h_nvars h_aligned h_clauses_pos v h_gate

  -- The transported witness
  let W' := plant_flat_n n φ r h_nvars h_aligned ▸ W

  -- Digest equality
  have h_digestBits' : W'.digestBits = W.digestBits := rfl
  have h_digestBits_len : W.digestBits.length = r.dgLen := by
    rw [h_digestBits]; simp [Vector.toList]

  -- R = φ.nvars for exponential profile
  have h_R : Foundations.computeR .exponential L.n = φ.nvars := by
    simp [Foundations.computeR, h_L_n]

  -- Gate index = 0
  have h_gate_idx : v.val - (1 + L.n) = 0 := by simp [h_v_pos, h_L_n]
  have h_idx_eq : v.val - (1 + φ.nvars) = 0 := by omega

  -- Boolean conditions for LHS (entropyFromWitness)
  have h_v_ne_zero : v.val ≠ 0 := by omega
  have h_v_gt_n : ¬(v.val ≤ L.n) := by omega

  -- Boolean conditions for RHS (plant_flat_entropy)
  have h_v_ne_zero_beq : (v.val == 0) = false := by simp [h_v_ne_zero]
  have h_v_gt_nvars : ¬(v.val ≤ φ.nvars) := by omega
  have h_v_gt_nvars_neg : ((v.val ≤ φ.nvars) = false) := by simp [h_v_gt_nvars]

  -- FG range condition
  have h_in_fg : (1 + φ.nvars ≤ v.val) ∧ (v.val < 1 + φ.nvars + r.gateDigests.length) := by
    simp [h_v_pos, h_single]
  have h_idx_lt : v.val - (1 + φ.nvars) < r.gateDigests.length := by
    simp [h_v_pos, h_single]

  -- The proof strategy: show both sides compute the same ofBits using the same bits
  -- At FG gate v: both sides read dgLen bits from the digest
  -- LHS (entropyFromWitness): reads W.digestBits[0..R) where R = nvars
  -- RHS (plant_flat_entropy): reads r.gateDigests[0][0..dgLen)
  -- By h_digestBits: W.digestBits = gateDigests[0].toList
  -- Since R = nvars ≤ dgLen, the first nvars bits match

  -- Unfold definitions
  unfold Foundations.entropyFromWitness plant_flat_entropy

  -- Use split_ifs to handle all the conditionals
  simp only [h_v_ne_zero_beq, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h1 h2 h3 h4
  all_goals first
    | exact absurd h1 h_v_gt_n  -- v ≤ L.n contradiction
    | exact absurd h2 h_v_gt_nvars  -- v ≤ φ.nvars contradiction
    | (exfalso; exact h3)  -- Direct False case (when h3 : False)
    | (exfalso; simp only [h_in_fg] at h3; exact h3 h_in_fg)  -- fg_cond negation contradiction
    | (exfalso; exact h4 h_idx_lt)  -- idx_cond contradiction
    | (-- Main case: both sides are ofBits with bit functions
       -- Goal: ofBits _ f = ofBits _ g for some f, g
       apply LStar.ofBits_ext
       intro i

       -- Show the bit functions are equal
       have h_i_lt_nvars : i.val < φ.nvars := by
         have h : i.val < L.seedWidth v := i.isLt
         calc i.val < L.seedWidth v := h
              _ = φ.nvars := h_sw

       have h_i_lt_R : i.val < Foundations.computeR .exponential L.n := by
         simp only [h_R]; exact h_i_lt_nvars

       have h_i_lt_dgLen : i.val < r.dgLen := Nat.lt_of_lt_of_le h_i_lt_nvars h_dgLen_ge

       have h_bit_idx_eq : (v.val - (1 + L.n)) * Foundations.computeR .exponential L.n + i.val = i.val := by
         simp only [h_gate_idx]; ring

       have h_bit_lt : (v.val - (1 + L.n)) * Foundations.computeR .exponential L.n + i.val < W'.digestBits.length := by
         simp only [h_bit_idx_eq, h_digestBits', h_digestBits_len]
         exact h_i_lt_dgLen

       -- The goal compares bit functions from ofBits
       -- LHS: if i.val < R then (if h : bit_idx < len then digestBits.get _ else false) else false
       -- RHS: if h_i : i.val < dgLen then digest.get _ else false

       -- idx = 0 for the FG gate
       have h_idx_zero : v.val - (1 + φ.nvars) = 0 := h_idx_eq

       -- The key insight: plant_flat.n = φ.nvars, so all L.n references simplify
       have h_plant_n : (plant_flat n φ r h_nvars h_aligned).n = φ.nvars := plant_flat_n n φ r h_nvars h_aligned
       have h_R_plant : Foundations.computeR .exponential (plant_flat n φ r h_nvars h_aligned).n = φ.nvars := by
         simp only [Foundations.computeR, h_plant_n]

       -- v.val = 1 + φ.nvars, so (v.val - (1 + plant.n)) = 0
       have h_diff_zero : v.val - (1 + (plant_flat n φ r h_nvars h_aligned).n) = 0 := by
         simp only [h_plant_n, h_v_pos]; omega

       -- The bit index simplifies to i.val
       have h_bit_idx_simple : (v.val - (1 + (plant_flat n φ r h_nvars h_aligned).n)) *
             Foundations.computeR .exponential (plant_flat n φ r h_nvars h_aligned).n + i.val = i.val := by
         simp only [h_diff_zero, h_R_plant]; ring

       -- i.val < dgLen gives us the bound
       have h_i_lt_len : i.val < r.dgLen := h_i_lt_dgLen

       -- i.val < R (which equals φ.nvars)
       have h_i_lt_R_plant : i.val < Foundations.computeR .exponential (plant_flat n φ r h_nvars h_aligned).n := by
         simp only [h_R_plant]; exact h_i_lt_nvars

       -- Now simplify the goal step by step
       rw [if_pos h_i_lt_R_plant]

       -- W.digestBits.length = r.dgLen (via h_digestBits)
       have h_W_len : W.digestBits.length = r.dgLen := h_digestBits_len

       -- The inner dif condition: bit_idx < W.digestBits.length
       have h_dif_cond : (v.val - (1 + (plant_flat n φ r h_nvars h_aligned).n)) *
             Foundations.computeR .exponential (plant_flat n φ r h_nvars h_aligned).n + i.val < W.digestBits.length := by
         simp only [h_bit_idx_simple, h_W_len]; exact h_i_lt_len

       rw [dif_pos h_dif_cond]

       -- Now goal: W.digestBits.get ⟨i.val, _⟩ = (if h_i : i.val < dgLen then gateDigests[...].get ... else false)
       -- Reduce the RHS dif
       rw [dif_pos h_i_lt_dgLen]

       -- Now goal: W.digestBits.get ⟨i.val, _⟩ = gateDigests[idx].get ⟨i.val, _⟩
       -- where idx = v.val - (1 + φ.nvars) = 0

       -- First simplify the index in W.digestBits.get
       have h_get_idx : (v.val - (1 + (plant_flat n φ r h_nvars h_aligned).n)) *
             Foundations.computeR .exponential (plant_flat n φ r h_nvars h_aligned).n + i.val = i.val := h_bit_idx_simple

       -- The goal index on LHS is bit_idx = i.val
       simp only [h_get_idx, List.get_eq_getElem]

       -- W.digestBits = gateDigests[0].toList
       simp only [h_digestBits, h_idx_eq]

       -- toList[i] = Vector.get i
       exact single_gate_digestBits_eq _ i.val h_i_lt_dgLen)

/-- The R value at the FG gate equals nvars for exponential profile. -/
lemma plant_flat_R_at_gate_eq_nvars
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ) :
    let L := plant_flat n φ r h_nvars h_aligned
    Foundations.computeR .exponential L.n = φ.nvars := by
  simp only [Foundations.computeR]
  rw [plant_flat_n]

/-- For planted instances, L.n = φ.nvars. -/
lemma plant_flat_n_eq_nvars
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ) :
    (plant_flat n φ r h_nvars h_aligned).n = φ.nvars :=
  plant_flat_n n φ r h_nvars h_aligned

/-- Entropy equality at all vertices for planted instances.

    For planted instances with witness W constructed from randomness r:
    - Source (v=0): both return zeros
    - Variables (1 ≤ v ≤ nvars): both use assignment bits
    - FG gate: both use gateDigests bits (by construction of W.digestBits)
    - Other: both return zeros -/
lemma entropy_eq_all_vertices
    (n : Nat) (φ : CNF) (r : Randomness φ.nvars)
    (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ)
    (h_clauses_pos : 0 < φ.clauses.length)
    (h_wf : WellFormedRandomness_flat φ r)
    (W : Witness φ.nvars)
    (h_assignment_eq : W.assignment = r.assignment)
    (h_digestBits : W.digestBits = (r.gateDigests.get ⟨0, by rw [r.h_single_gate]; omega⟩).toList)
    (v : Fin (plant_flat n φ r h_nvars h_aligned).dag.n) :
    let L := plant_flat n φ r h_nvars h_aligned
    Foundations.entropyFromWitness L (plant_flat_n n φ r h_nvars h_aligned ▸ W) .exponential v =
    plant_flat_entropy φ r h_nvars L.dag L.seedWidth v := by
  let L := plant_flat n φ r h_nvars h_aligned
  let W' := plant_flat_n n φ r h_nvars h_aligned ▸ W
  have h_L_n : L.n = φ.nvars := plant_flat_n n φ r h_nvars h_aligned
  have h_single : r.gateDigests.length = 1 := r.h_single_gate

  -- Case analysis on vertex position
  by_cases h_v_zero : v.val = 0
  · -- Source vertex: both return ofBits _ (fun _ => false)
    have h_lhs := entropy_eq_at_source L W' v h_v_zero
    unfold plant_flat_entropy
    have h_beq : (v.val == 0) = true := by simp [h_v_zero]
    simp only [h_beq, ↓reduceIte]
    exact h_lhs

  · by_cases h_v_var : v.val ≤ φ.nvars
    · -- Variable vertex (but not source since h_v_zero is false)
      have h_v_le_L_n : v.val ≤ L.n := by rw [h_L_n]; exact h_v_var
      have h_not_gate : L.fg.gateReq v = false := by
        -- FG gate requires v.val ≥ 1 + φ.nvars, but v.val ≤ φ.nvars
        simp only [L, plant_flat, FrontierGateConfig.gateReq, decide_eq_false_iff_not,
                   Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        omega

      -- Apply variable lemma
      have h_var := entropy_eq_at_variable L W' v h_v_zero h_v_le_L_n h_not_gate

      -- RHS: plant_flat_entropy for variable vertex
      unfold plant_flat_entropy
      have h_beq : (v.val == 0) = false := by simp [h_v_zero]
      simp only [h_beq, Bool.false_eq_true, ↓reduceIte, h_v_var]

      -- Now LHS (from h_var) and RHS should both use assignment bits
      -- Need to show they're equal
      rw [h_var]
      -- Both compute: ofBits _ (fun i => if i.val = 0 then assignment[v.val - 1] else false)
      -- RHS uses r.assignment, W uses r.assignment (via h_assignment_eq)
      apply LStar.ofBits_ext
      intro i
      simp only [beq_iff_eq]
      -- Goal: (if i.val = 0 then W'.assignmentInf (v.val - 1) else false) =
      --       (if i.val = 0 then r.assignment ⟨v.val - 1, _⟩ else false)
      by_cases h_i : i.val = 0
      · simp only [h_i, ↓reduceIte]
        -- W'.assignmentInf (v.val - 1) = r.assignment ⟨v.val - 1, _⟩
        -- W' = plant_flat_n ▸ W where plant_flat_n : L.n = φ.nvars
        -- W.assignment = r.assignment (by h_assignment_eq)
        --
        -- For Witness transport: when we transport W : Witness φ.nvars along h : L.n = φ.nvars,
        -- the assignment field becomes h ▸ W.assignment
        -- W'.assignmentInf (v.val - 1) accesses W'.assignment which is transported

        -- Key insight: assignmentInf extends the assignment to Nat → Bool
        -- For finite assignments, extend returns assignment[i] for i < n, false otherwise
        -- Both sides access the same index (v.val - 1) which is < both φ.nvars and L.n

        have h_varIdx : v.val - 1 < φ.nvars := by omega

        -- LHS: W'.assignmentInf (v.val - 1) = W'.assignment.extend (v.val - 1)
        -- Since v.val - 1 < L.n, this equals W'.assignment ⟨v.val - 1, _⟩
        -- W' is transported from W, so W'.assignment ⟨i, _⟩ = W.assignment ⟨i, _⟩ when indices match

        -- RHS: r.assignment ⟨v.val - 1, h_varIdx⟩

        -- Use the fact that both evaluate to the same bit via h_assignment_eq
        conv_lhs =>
          unfold Witness.assignmentInf LStar.Assignment.extend
        have h_varIdx_L : v.val - 1 < L.n := by rw [h_L_n]; exact h_varIdx
        simp only [h_varIdx_L, ↓reduceDIte]

        -- Now need to show: W'.assignment ⟨v.val - 1, h_varIdx_L⟩ = r.assignment ⟨v.val - 1, h_varIdx⟩
        -- Since W' = (plant_flat_n ...) ▸ W and plant_flat_n : L.n = φ.nvars
        -- The Witness transport carries assignment along, so we need to handle the cast

        -- Use congrArg to extract the bit value
        -- W' is defined as (plant_flat_n n φ r h_nvars h_aligned) ▸ W
        -- The Eq.rec on Witness transports the assignment field
        -- After simp [W'], rfl closes the goal if the types line up
        simp only [W', h_assignment_eq]
      · simp only [h_i, ↓reduceIte]

    · -- v.val > φ.nvars
      by_cases h_gate : L.fg.gateReq v
      · -- FG gate
        exact entropy_eq_at_fg_gate n φ r h_nvars h_aligned h_clauses_pos h_wf W h_digestBits v h_gate
      · -- Other (not source, not variable, not FG gate)
        -- Both return zeros
        unfold Foundations.entropyFromWitness plant_flat_entropy
        have h_v_ne_zero_beq : (v.val == 0) = false := by simp [h_v_zero]
        have h_v_gt_L_n : ¬(v.val ≤ L.n) := by rw [h_L_n]; exact h_v_var
        have h_v_gt_nvars : ¬(v.val ≤ φ.nvars) := h_v_var

        -- Note: L := plant_flat n φ r h_nvars h_aligned, so L.n and L.fg appear as (plant_flat ...).n/fg
        simp only [L] at h_v_gt_L_n h_gate

        -- h_gate is now: ¬(plant_flat ...).fg.gateReq v = true
        -- For the if statement, we need to show the gateReq is false (via Bool eq_false_iff)
        have h_gate_eq_false : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v = false := by
          cases h : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v with
          | false => rfl
          | true => exact absurd h h_gate
        simp only [h_v_ne_zero_beq, Bool.false_eq_true, ↓reduceIte, h_v_gt_L_n, h_gate_eq_false,
                   h_v_gt_nvars, ite_false]

        -- FG range check for RHS
        have h_not_in_fg : ¬((1 + φ.nvars ≤ v.val) ∧ (v.val < 1 + φ.nvars + r.gateDigests.length)) := by
          intro ⟨h_ge, h_lt⟩
          have h_gate_true : (plant_flat n φ r h_nvars h_aligned).fg.gateReq v = true := by
            simp only [plant_flat, FrontierGateConfig.gateReq, decide_eq_true_eq,
                       Bool.and_eq_true]
            exact ⟨h_ge, h_lt⟩
          rw [h_gate_eq_false] at h_gate_true
          exact Bool.false_ne_true h_gate_true
        simp only [h_not_in_fg, ite_false]
        -- After simplification, we have `if h : False then ... else ...` patterns
        -- These reduce to the else branches
        split_ifs <;> first | rfl | contradiction

/-- The R component from emergentConfigAtGate equals R_of for the QP profile.

    When emergentConfigAtGate returns some ⟨R_ret, cfg⟩, the R value equals
    R_of φ numGates (1 + φ.nvars + gateIndex).

    **Proof**: Unfold emergentConfigAtGate, which creates L := lstarStructureFromCNF
    and returns L.R v. By definition, lstarStructureFromCNF sets R := R_of φ numGates,
    so L.R v = R_of φ numGates v.val. -/
lemma emergentConfigAtGate_R_component
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : AssignmentInf) (gateIndex : Nat)
    (R_ret : Nat) (cfg_ret : Fin (2^R_ret))
    (h_ret : Foundations.emergentConfigAtGate φ h_nvars_pos numGates a gateIndex = some ⟨R_ret, cfg_ret⟩)
    : R_ret = Foundations.R_of φ numGates (1 + φ.nvars + gateIndex) := by
  unfold Foundations.emergentConfigAtGate at h_ret
  simp only at h_ret
  split at h_ret
  · rename_i h_valid
    split at h_ret
    · rename_i h_vertex_valid
      split at h_ret
      · rename_i h_cap
        cases h_ret
        let L := Foundations.lstarStructureFromCNF φ h_nvars_pos numGates
        let clause_start := 1 + φ.nvars
        let vertex_idx := clause_start + gateIndex
        let v : Fin L.dag.n := ⟨vertex_idx, h_vertex_valid⟩
        show L.R v = Foundations.R_of φ numGates (1 + φ.nvars + gateIndex)
        rfl
      · cases h_ret
    · cases h_ret
  · cases h_ret

/-- For n ≥ 128, (log₂ n)² ≠ n.

    This is the key fact that causes the R mismatch between QP profile (R = (log n)²)
    and flat profile (R = n). For n ≥ 128, the polynomial (log n)² grows much slower
    than n, so they never equal.

    **Proof**: For n ≥ 128 = 2^7, we have log₂ n ≥ 7.
    For k ≥ 7, k² < 2^k (exponential dominates polynomial).
    So (log₂ n)² < 2^(log₂ n) ≤ n, hence (log₂ n)² ≠ n. -/
lemma log_sq_ne_n (n : Nat) (h_n : n ≥ 128) : (Nat.log 2 n)^2 ≠ n := by
  have h_log_bound : Nat.log 2 n ≥ 7 := by
    have : Nat.log 2 128 = 7 := by native_decide
    calc Nat.log 2 n ≥ Nat.log 2 128 := Nat.log_mono_right h_n
      _ = 7 := this
  -- For k ≥ 7, k² < 2^k
  have h_exp_dom : ∀ k : Nat, k ≥ 7 → k^2 < 2^k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases h_small : k ≤ 20
      case pos => interval_cases k <;> native_decide
      case neg =>
        push_neg at h_small
        have h_k_ge_21 : k ≥ 21 := h_small
        obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have h_k'_ge_7 : k' ≥ 7 := by omega
        have h_k'_lt : k' < k := by omega
        have ih_k' : k'^2 < 2^k' := ih k' h_k'_lt h_k'_ge_7
        have h_linear : 2 * k' + 1 < 2^k' := by
          have h_sq := LStar.StructuralOWF.Foundations.square_le_pow_from_seven k' h_k'_ge_7
          have : 2 * k' + 1 < k'^2 := by nlinarith
          omega
        have h_step : (k'+1)^2 < 2^(k'+1) := by
          calc (k'+1)^2
              = k'^2 + 2*k' + 1 := by ring
            _ < 2^k' + 2^k' := by omega
            _ = 2 * 2^k' := by ring
            _ = 2^(k'+1) := by rw [Nat.pow_succ]; ring
        rw [hk']
        exact h_step
  have h_sq_lt_exp : (Nat.log 2 n)^2 < 2^(Nat.log 2 n) := h_exp_dom _ h_log_bound
  have h_exp_le_n : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  intro h_eq
  omega

/-! ## Bitstring Inversion Relation

R_bits(n, bs, w) holds iff:
1. bs = owf_bits n w (the bitstring is the OWF output)
2. The underlying randomness satisfies the CNF
-/

/-- The bitstring inversion relation.

    R_bits(n, bs, w) ≡ bs = owf_bits(n, w) ∧ WellFormedRandomness_flat(φ_n, bitsToRandomness(w))

    This is the fully {0,1}* version of the OWF inversion problem.

    **Key requirement**: WellFormedRandomness_flat ensures:
    1. The CNF φ_n is satisfied by the assignment
    2. The digests match the emergent configs (making planted instances yes-instances)
    3. dgLen ≥ nvars (ensuring enough digest bits)
-/
noncomputable def OWFInversionRelation_bits (n : Nat) (bs : List Bool) (w : Bits (expWLen n)) : Prop :=
  if h_n : n ≥ 128 then
    let h_nvars_eq := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
    let r := bitsToRandomness_exp n (by omega : n > 0) w
    let r_φ : Randomness (Φ n).nvars := (h_nvars_eq n h_n).symm ▸ r
    bs = owf_bits n h_n w ∧ WellFormedRandomness_flat (Φ n) r_φ
  else False

/-- The OWF inversion language over bitstrings.

    OWFInversionLang = { bs | ∃ n ≥ 128, ∃ w, OWFInversionRelation_bits n bs w }

    This is the set of bitstrings that are valid OWF outputs with satisfying preimages.
-/
def OWFInversionLang_bits : Set (List Bool) :=
  { bs | ∃ (n : Nat) (h_n : n ≥ 128) (w : Bits (expWLen n)), OWFInversionRelation_bits n bs w }

/-! ## Prefix-Based NP \ P Witness (Clean Approach)

**Key insight**: The range language `OWFInversionLangLang` cannot derive `¬InP` from
the existing infrastructure because range-membership-in-P does NOT imply a prefix oracle.

**Clean approach**: Use the *prefix extension language* directly, which is what the
`uniform_search_from_prefix_oracle` machinery actually requires.

**Definition**: The hard language is `prefixLang` over `PrefixInput LStarInstanceFG (expWLen n)`:
- Input: (L : LStarInstanceFG, prefix : List Bool, bit : Bool)
- Membership: ∃ w : Bits (expWLen n), (prefix ++ [bit]) <+: w ∧ R n L w

**Bitstring encoding**: Encode `Σ n, PrefixInput LStarInstanceFG (expWLen n)` to `List Bool`.
Then use `encodedLang` + `hardness_transfer` from LStarEncoding.lean.
-/

/-- Alignment constraints for alignedCNFFamily.

    alignedCNFFamily n has:
    - clauses.length = n (exactly n unit clauses)
    - nvars = n
    - Each clause is a unit clause (length 1 ≤ 3) -/
theorem alignedCNFFamily_aligned (n : Nat) (h : n ≥ 128) : AlignedCNFConstraints (Φ n) where
  clauses_le := by
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    simp only [List.length_ofFn]
    omega
  is_3sat := by
    intro c h_c
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily at h_c
    simp only [List.mem_ofFn] at h_c
    obtain ⟨i, rfl⟩ := h_c
    simp only [List.length_singleton]
    omega

/-- **Planted Instance Subtype**: L* instances that are provably planted.

    This is the key type that makes ParamSizeLowerBound provable: we know
    these instances come from `plant_flat` so we can extract size bounds from
    the construction. -/
def PlantedInstance (n : Nat) : Type :=
  {L : LStarInstanceFG // ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
    L = plant_flat n (Φ n) r
      (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
      (alignedCNFFamily_aligned n h_n)}

/-- Sized instance for PlantedInstance: size is the DAG size. -/
instance instSizedPlantedInstance (n : Nat) : Sized (PlantedInstance n) where
  size := fun L => Sized.size L.val
  size_pos := fun L => Sized.size_pos L.val

/-- ParamSizeLowerBound for PlantedInstance.

    For planted instances, we can prove n ≤ dag.n because the construction
    guarantees totalNodes ≥ 1 + nvars = 1 + n ≥ n. -/
instance instParamSizeLowerBoundPlantedInstance : ParamSizeLowerBound PlantedInstance where
  c := 1
  hc_pos := Nat.one_pos
  bound := fun n L => by
    -- Extract planted instance structure
    obtain ⟨h_n_ge_128, r, h_plant_eq⟩ := L.property
    show n ^ 1 ≤ Sized.size L
    simp only [pow_one]
    -- Sized.size L = L.val.dag.n (from OWFSizedInstances)
    have h_size_eq : Sized.size L = L.val.dag.n := rfl
    rw [h_size_eq]
    -- Use plant_flat definition to get dag.n formula
    have h_dag : L.val.dag.n = Construction.totalNodes (Φ n).nvars (Φ n).clauses.length := by
      rw [h_plant_eq]
      rfl
    rw [h_dag]
    -- totalNodes = 1 + nvars + nclauses + reductionTreeSize nclauses
    -- For n ≥ 128: nvars = n, so totalNodes ≥ 1 + n ≥ n
    have h_nvars : (Φ n).nvars = n := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n_ge_128
    simp only [Construction.totalNodes, h_nvars]
    omega
  size_nontrivial := fun n L => by
    -- size L = L.val.dag.n (from OWFSizedInstances)
    have h_size_eq : Sized.size L = L.val.dag.n := rfl
    rw [h_size_eq]
    -- For planted instances: dag.n = totalNodes ≥ 1 + nvars ≥ 1 + 128 > 2
    obtain ⟨h_n_ge_128, _r, h_plant_eq⟩ := L.property
    have h_dag : L.val.dag.n = Construction.totalNodes (Φ n).nvars (Φ n).clauses.length := by
      rw [h_plant_eq]; rfl
    rw [h_dag]
    have h_nvars : (Φ n).nvars = n := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n_ge_128
    simp only [Construction.totalNodes, h_nvars]
    omega

/-- Sigma type for prefix inputs across all security parameters.

    This bundles the security parameter n with a PrefixInput for that parameter.
    The encoding to bitstrings will include n explicitly.

    **IMPORTANT**: Uses PlantedInstance instead of LStarInstanceFG to ensure
    ParamSizeLowerBound is provable. -/
abbrev PrefixSigma := Sigma fun n : Nat => PrefixInput (PlantedInstance n) (expWLen n)

/-- Sized instance for PrefixSigma.

    Size = n + size of LStarInstanceFG + prefix length + 1 (for bit).
    This is polynomial in the components. -/
instance : Sized PrefixSigma where
  size := fun ⟨n, inp⟩ => n + Sized.size inp.input + inp.pref.val.length + 2
  size_pos := fun ⟨_, inp⟩ => by
    have h : 0 < Sized.size inp.input := Sized.size_pos inp.input
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) (Nat.le_add_left 2 _)

/-- Encode a natural number as a unary list of bits (length n, all true).
    This is simple and gives polynomial encoding. -/
def encodeNatUnary (n : Nat) : List Bool := List.replicate n true

/-- Helper: take exactly the length of the left part of an append. -/
lemma take_len_append {α : Type} (l r : List α) : List.take l.length (l ++ r) = l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Helper: drop exactly the length of the left part of an append. -/
lemma drop_len_append {α : Type} (l r : List α) : List.drop l.length (l ++ r) = r := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Encode PrefixSigma to bitstrings.

    Format (self-delimiting):
    `[n unary] ++ [false] ++ [|encL| unary] ++ [false] ++ encL ++ [|pref| unary] ++ [false] ++ pref ++ [bit]`

    Length tags make the encoding injective without requiring `encodeBits` to be prefix-free.

    **Note**: Uses `inp.input.val` to extract the underlying LStarInstanceFG from PlantedInstance. -/
noncomputable def encPrefixSigma (p : PrefixSigma) : List Bool :=
  let ⟨n, inp⟩ := p
  let encL := encodeBits inp.input.val  -- Extract underlying LStarInstanceFG
  let pref := inp.pref.val
  encodeNatUnary n ++ [false] ++
    encodeNatUnary encL.length ++ [false] ++ encL ++
    encodeNatUnary pref.length ++ [false] ++ pref ++ [inp.bit]

/-- **Lifted OWF Inversion Relation**: Works with PlantedInstance by extracting `.val`.

    This is the relation R : PlantedInstance n → Bits (expWLen n) → Prop that
    the prefix language and FNP machinery require. -/
def R_lifted : ∀ n, PlantedInstance n → Bits (expWLen n) → Prop :=
  fun n L w => StructuralOWFInversionRelation_exp Φ
    (fun n h => by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h]; omega)
    LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
    alignedCNFFamily_aligned n L.val w

/-- The prefix-extension language over PrefixSigma (structured type).

    This is the CORRECT hard language that connects to the search-to-decision machinery.
    Membership: ∃ w : Bits (expWLen n), (pref ++ [bit]) <+: w.toList ∧ R n L.val w

    **Note**: Uses R_lifted which extracts L.val from PlantedInstance. -/
def PrefixLangSigma : Lang PrefixSigma := fun ⟨n, inp⟩ =>
  BitstringBridge.prefixLang expWLen R_lifted n inp

/-- The prefix-extension language encoded as bitstrings.

    This is the explicit NP \ P witness using the clean prefix-based approach. -/
noncomputable def PrefixLangBits : Lang (List Bool) := encodedLang encPrefixSigma PrefixLangSigma

/-- **Prefix Language in NP**: The structured prefix language is in NP.

    **Proof**: From `prefixLang_in_np_parametric` (ParametricBitstringBridge.lean),
    instantiated with the OWF relation. The witness is w : Bits (expWLen n),
    and verification checks prefix constraint + R relation. -/
theorem PrefixLangSigma_in_NP : InNP PrefixLangSigma := by
  classical

  -- Witness type packages the security parameter with the bitstring witness.
  let β := Sigma fun n : Nat => Bits (expWLen n)
  let instβ : Sized β := sizedSigma

  -- Verifier as an AlgSpec: check parameter match, then check the prefix condition and R_lifted.
  let Vspec : AlgSpec (PrefixSigma × β) Bool 1 := {
    run := fun _ p =>
      let x := p.1
      let y := p.2
      match x, y with
      | ⟨n, inp⟩, ⟨n', w⟩ =>
          if h : n = n' then
            by
              cases h
              -- Use R_lifted which works on PlantedInstance
              exact decide ((inp.pref.val ++ [inp.bit]) <+: w.toList ∧ R_lifted n inp.input w)
          else
            false
    time_bound := fun m => (m + 1) ^ 3
    C := 1
    k := 3
    h_C_pos := by omega
    h_k_pos := by omega
    poly_explicit := fun _ => by simp
    time_bound_uniform := fun _ => by simp
    output_bounded := fun _ p => by
      -- Output is Bool (size 1); RHS is ≥ 1.
      have h_pow : 1 ≤ (Sized.size p + 1) ^ 3 := Nat.one_le_pow 3 _ (by omega)
      -- `Sized.size` on Bool is definitionally 1, independent of the value.
      simpa using h_pow
    coins_pos := by omega
  }
  -- Lift AlgSpec to RandAdv using the Church–Turing bridge axiom (choose an implementation).
  let V_ex := algspec_has_tm Vspec
  let V : RandAdv (PrefixSigma × β) Bool 1 := Classical.choose V_ex
  have hVrun : V.run = Vspec.run := by
    -- From `algspec_has_tm`: `V.toAlgSpec.run = Vspec.run`, and `toAlgSpec.run = V.run` definitionally.
    have h := (Classical.choose_spec V_ex).1
    simpa [V, RandAdv.toAlgSpec] using h

  -- Package as InNP.
  refine ⟨β, instβ, 1, V, 10, 2, 1, 3, ?_, ?_, ?_, ?_⟩
  · -- Determinism: V ignores coins (only coin is 0 anyway).
    intro c₁ c₂ p
    -- Rewrite to Vspec.run which ignores coins.
    cases c₁; cases c₂
    simp [hVrun, Vspec]
  · -- Witness size bound: accepted witnesses must match the input n, so size is O(n) ≤ poly(size x).
    intro x y h_accept
    rcases x with ⟨n, inp⟩
    rcases y with ⟨n', w⟩
    -- If verifier accepted, it must have taken the `n = n'` branch.
    have hn : n = n' := by
      -- If n ≠ n', run returns false.
      by_contra hne
      have : V.run ⟨0, V.coins_pos⟩ (⟨n, inp⟩, ⟨n', w⟩) = false := by
        simp [hVrun, Vspec, hne]
      exact (Bool.false_ne_true (this ▸ h_accept)).elim
    subst hn
    -- Now bound size of ⟨n, w⟩ by a polynomial in size of ⟨n, inp⟩.
    -- β = Sigma fun n => Bits (expWLen n) = Sigma fun n => Vector Bool (2*n + 64)
    -- Sized.size ⟨n, w⟩ = Sized.size n + Sized.size w = (n + 1) + ((2*n + 64) + 1) = 3*n + 66
    have h_w_size : Sized.size (⟨n, w⟩ : β) = 3 * n + 66 := by
      -- β = Sigma fun n => Bits (expWLen n)
      -- Using sizedSigma: size ⟨n, w⟩ = size n + size w = (n+1) + (expWLen n + 1) = 3*n + 66
      -- instβ was inferred as the canonical sizedSigma instance
      have h1 : @Sized.size β instβ ⟨n, w⟩ = Sized.size n + Sized.size w := by rfl
      rw [h1]
      simp only [Sized.size, sizedNat, sizedBitstring, expWLen]
      omega
    have h_size_ge : n + 3 ≤ Sized.size (⟨n, inp⟩ : PrefixSigma) + 1 := by
      simp [PrefixSigma, Sized.size]
      omega
    have h_sq_mono : (n + 3) ^ 2 ≤ (Sized.size (⟨n, inp⟩ : PrefixSigma) + 1) ^ 2 := by
      -- Use monotonicity for squares via multiplication.
      have h_mul :
          (n + 3) * (n + 3) ≤ (Sized.size (⟨n, inp⟩ : PrefixSigma) + 1) * (Sized.size (⟨n, inp⟩ : PrefixSigma) + 1) :=
        Nat.mul_le_mul h_size_ge h_size_ge
      simpa [pow_two] using h_mul
    have h_lin_le : 3 * n + 66 ≤ 10 * (n + 3) ^ 2 := by
      -- Holds for all n ≥ 0 by direct arithmetic.
      simp [pow_two]
      nlinarith
    have h_final : 3 * n + 66 ≤ 10 * (Sized.size (⟨n, inp⟩ : PrefixSigma) + 1) ^ 2 := by
      calc
        3 * n + 66
            ≤ 10 * (n + 3) ^ 2 := h_lin_le
        _ ≤ 10 * (Sized.size (⟨n, inp⟩ : PrefixSigma) + 1) ^ 2 := by
              apply Nat.mul_le_mul_left
              exact h_sq_mono
    -- Conclude witness bound.
    -- We allow extra slack by taking C_wit=10, k_wit=2 in the NP packaging.
    simpa [h_w_size] using h_final
  · -- Time bound polynomial: by construction.
    intro p
    -- V.time_bound ≤ V.C * (size p + 1)^V.k = 1 * (size p + 1)^3
    -- From algspec_has_tm: V.C = Vspec.C = 1 and V.k = Vspec.k = 3
    have h_C : V.C = 1 := (Classical.choose_spec V_ex).2.1
    have h_k : V.k = 3 := (Classical.choose_spec V_ex).2.2.1
    calc V.time_bound (Sized.size p)
        ≤ V.C * (Sized.size p + 1) ^ V.k := V.poly_explicit p
      _ = 1 * (Sized.size p + 1) ^ 3 := by rw [h_C, h_k]
  · -- Correctness: PrefixLangSigma x ↔ ∃y, verifier accepts (x,y).
    intro x
    rcases x with ⟨n, inp⟩
    constructor
    · intro hL
      rcases hL with ⟨w, h_pref, hR⟩
      refine ⟨⟨n, w⟩, ?_⟩
      -- Show V.run accepts by rewriting to Vspec.run and using the evidence
      -- V.run c (⟨n, inp⟩, ⟨n, w⟩) = Vspec.run c (⟨n, inp⟩, ⟨n, w⟩)
      -- = (match ... with | ⟨n, inp⟩, ⟨n', w⟩ => if n = n' then decide(...) else false)
      -- = decide((inp.pref.val ++ [inp.bit]) <+: w.toList ∧ R_lifted n inp.input w)
      rw [hVrun]
      simp only [Vspec, dif_pos rfl]
      exact decide_eq_true ⟨h_pref, hR⟩
    · rintro ⟨⟨n', w⟩, h_acc⟩
      by_cases h : n = n'
      · subst h
        -- Accepted implies the decided proposition is true.
        have : decide ((inp.pref.val ++ [inp.bit]) <+: w.toList ∧ R_lifted n inp.input w) = true := by
          simpa [hVrun, Vspec] using h_acc
        have h_prop : (inp.pref.val ++ [inp.bit]) <+: w.toList ∧ R_lifted n inp.input w := by
          simpa [decide_eq_true_eq] using this
        exact ⟨w, h_prop.1, h_prop.2⟩
      · -- If n ≠ n', run is false.
        have : V.run ⟨0, V.coins_pos⟩ (⟨n, inp⟩, ⟨n', w⟩) = false := by
          simp [hVrun, Vspec, h]
        exact False.elim (Bool.false_ne_true (this ▸ h_acc))

/-- **Prefix Language not in P**: The structured prefix language is not in P.

    **Proof**: By contrapositive of `uniform_search_from_prefix_oracle`:
    - If InP PrefixLangSigma, we can build a prefix decider D
    - uniform_search_from_prefix_oracle gives: InP prefixLang → InFP inversion
    - But structural_owf_inversion_not_in_fp proves ¬InFP inversion
    - Contradiction

    This is THE key theorem that connects prefix language hardness to OWF security.
-/
theorem PrefixLangSigma_not_in_P : ¬InP PrefixLangSigma := by
  intro h_in_p
  classical

  -- Extract deterministic poly-time decider A for PrefixLangSigma from InP hypothesis.
  rcases h_in_p with ⟨T, A, h_det, h_correct⟩

  -- Build per-n AlgSpec deciders D n for the prefix language over PlantedInstance.
  -- uniform_search_from_prefix_oracle expects deciders over α n = PlantedInstance n.
  have h_prefix_decider :
      ∃ (deg : Nat) (T' : Nat)
        (D : ∀ n, AlgSpec (PrefixInput (PlantedInstance n) (expWLen n)) Bool T'),
        (∀ n c₁ c₂ inp, (D n).run c₁ inp = (D n).run c₂ inp) ∧
        (∀ n inp, (D n).run ⟨0, (D n).coins_pos⟩ inp = true ↔ BitstringBridge.prefixLang expWLen R_lifted n inp) ∧
        (∀ n, (D n).time_bound n ≤ (n + 1) ^ deg) := by
    refine ⟨3, T, (fun n => ?_), ?_, ?_, ?_⟩
    · -- Define D n by currying A on the Sigma input ⟨n, inp⟩.
      refine {
        run := fun c inp => A.run c ⟨n, inp⟩
        time_bound := fun m => (m + 1) ^ 3
        C := 1
        k := 3
        h_C_pos := by omega
        h_k_pos := by omega
        poly_explicit := fun _ => by simp
        time_bound_uniform := fun _ => by simp
        output_bounded := fun c x => by
          -- Output is Bool, size = 1; need 1 ≤ (size x + 1)^3
          have h_pow : 1 ≤ (Sized.size x + 1) ^ 3 := Nat.one_le_pow 3 _ (by omega)
          have h_bool_size : Sized.size (A.run c ⟨n, x⟩) = 1 := rfl
          omega
        coins_pos := A.coins_pos
      }
    · intro n c₁ c₂ inp
      simpa using h_det c₁ c₂ ⟨n, inp⟩
    · intro n inp
      -- Correctness transports along PrefixLangSigma definition.
      have := (h_correct ⟨n, inp⟩)
      -- Unfold PrefixLangSigma and BitstringBridge.prefixLang.
      simpa [PrefixLangSigma, R_lifted] using this.symm
    · intro n
      simp

  -- Get the FNP verifier for R_lifted (OWF inversion relation is in FNP).
  -- Note: structural_owf_inversion_in_fnp_exp gives FNP for LStarInstanceFG,
  -- which R_lifted lifts by using L.val.
  have h_wellformed := LStar.StructuralOWF.Theorems.alignedCNFFamily_wellformed
  have h_wf_literals : ∀ n, CNF.WellFormed (Φ n) := fun n => by
    -- Use the provided lemma for n>0; handle n=0 separately.
    cases n with
    | zero =>
        unfold CNF.WellFormed Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
        intro c h_c; simp at h_c
        subst h_c
        intro l h_l
        simp at h_l
        subst h_l
        simp
    | succ m =>
        exact LStar.StructuralOWF.Theorems.alignedCNFFamily_wf_literals (Nat.succ m) (Nat.succ_pos m)
  have h_nvars_eq := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq

  -- Lift the FNP membership from LStarInstanceFG to PlantedInstance.
  -- R_lifted n L w = R n L.val w, so FNP verification works through the subtype.
  have h_R_fnp_lifted : InFNP_parametric_bits expWLen R_lifted := by
    -- Extract the FNP verifier for the base relation on LStarInstanceFG
    have h_base := structural_owf_inversion_in_fnp_exp Φ h_wellformed h_wf_literals h_nvars_eq alignedCNFFamily_aligned
    -- InFNP_parametric_bits gives: ∃ C deg T V, (conditions on V)
    -- h_base has type InFNP_parametric_bits expWLen (StructuralOWFInversionRelation_exp ...)
    -- which means there exists a V : AlgSpec (Σ n, LStarInstanceFG × Bits (expWLen n)) Bool T
    rcases h_base with ⟨C_V, deg_V, T_fnp, V_base, h_C_pos, h_deg_pos, h_det, h_correct, h_poly, h_wlen_bound⟩
    -- Build lifted verifier that extracts .val from PlantedInstance
    -- Use the extracted C_V and deg_V to match h_poly
    let V_lifted : AlgSpec (Sigma fun n => PlantedInstance n × Bits (expWLen n)) Bool T_fnp := {
      run := fun c ⟨n, ⟨L, w⟩⟩ => V_base.run c ⟨n, (L.val, w)⟩
      time_bound := V_base.time_bound
      C := C_V
      k := deg_V
      h_C_pos := h_C_pos
      h_k_pos := h_deg_pos
      poly_explicit := fun ⟨n, ⟨L, w⟩⟩ => by
        -- Size of PlantedInstance = Size of LStarInstanceFG (by definition of instSizedPlantedInstance)
        let inp_base : Sigma fun n => LStarInstanceFG × Bits (expWLen n) := ⟨n, (L.val, w)⟩
        have h_size_eq : Sized.size (⟨n, ⟨L, w⟩⟩ : Sigma fun n => PlantedInstance n × Bits (expWLen n)) =
                         Sized.size inp_base := rfl
        rw [h_size_eq]
        -- h_poly : ∀ n, V_base.time_bound n ≤ C_V * (n + 1) ^ deg_V
        exact h_poly (Sized.size inp_base)
      time_bound_uniform := fun n => h_poly n
      output_bounded := fun c p => V_base.output_bounded c ⟨p.1, (p.2.1.val, p.2.2)⟩
      coins_pos := V_base.coins_pos
    }
    refine ⟨C_V, deg_V, T_fnp, V_lifted, h_C_pos, h_deg_pos, ?_, ?_, h_poly, h_wlen_bound⟩
    · -- Determinism: follows from V_base determinism
      intro c₁ c₂ ⟨n, ⟨L, w⟩⟩
      exact h_det c₁ c₂ ⟨n, (L.val, w)⟩
    · -- Correctness: R_lifted n L w ↔ V_lifted accepts ⟨n, (L, w)⟩
      intro n L w
      -- V_lifted.run c ⟨n, (L, w)⟩ = V_base.run c ⟨n, (L.val, w)⟩ by definition
      -- h_correct says: V_base.run ... ⟨n, (L.val, w)⟩ = true ↔ R n L.val w
      -- R_lifted n L w = R n L.val w by definition
      simp only [V_lifted, R_lifted]
      exact h_correct n L.val w

  -- Apply search-from-prefix-oracle with PlantedInstance which has proper ParamSizeLowerBound.
  -- The global instance instParamSizeLowerBoundPlantedInstance provides the required bounds.
  have h_fp_solver :=
    BitstringBridge.uniform_search_from_prefix_oracle (α := PlantedInstance)
      (wlen := expWLen) (R := R_lifted) h_R_fnp_lifted h_prefix_decider

  rcases h_fp_solver with ⟨f_family, h_fp, h_correct_fp⟩

  -- Contradict the proven non-membership of OWF inversion in FP for alignedCNFFamily.
  -- Reuse the same assumptions discharged in StructuralOWFBridge.pnenp.
  have h_satisfiable : ∀ n, n ≥ 128 → ∃ (a : AssignmentInf), (Φ n).satisfies a := by
    intro n _h_n
    refine ⟨(fun _ => true), ?_⟩
    unfold CNF.satisfies Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    intro clause h_clause
    simp only [List.mem_ofFn] at h_clause
    obtain ⟨i, rfl⟩ := h_clause
    unfold Clause.satisfies
    refine ⟨{ var := i.val, polarity := true }, ?_, rfl⟩
    simp
  have h_nonempty_clauses : ∀ n, n ≥ 128 → 0 < (Φ n).clauses.length := by
    intro n h_n
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    simp only [List.length_ofFn]
    omega
  have h_clauses_poly : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128,
      (Φ n).clauses.length ≤ C_cl * n ^ k_cl := by
    refine ⟨1, 1, by omega, by omega, ?_⟩
    intro n h_n
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    simp only [List.length_ofFn, pow_one, Nat.one_mul]
    omega
  have h_family_positive : ∀ n ≥ 128, CNF.HasPositiveClause (Φ n) := by
    intro n _h_n
    unfold CNF.HasPositiveClause Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    refine ⟨{ literals := [{ var := 0, polarity := true }] }, ?_, ?_⟩
    · simp only [List.mem_ofFn]
      refine ⟨⟨0, by omega⟩, rfl⟩
    · intro l h_l
      simp at h_l
      simp [h_l]
  have h_bounded := LStar.StructuralOWF.Theorems.alignedCNFFamily_bounded_solutions

  have h_not_fp :=
    structural_owf_inversion_not_in_fp Φ h_wellformed h_wf_literals h_nvars_eq
      h_nonempty_clauses h_satisfiable h_clauses_poly h_family_positive h_bounded alignedCNFFamily_aligned

  -- Build the witness-finder over LStarInstanceFG by wrapping f_family.
  -- For planted instances L = plant_flat n (Φ n) r ..., we use f_family on the corresponding PlantedInstance.
  let f_wrapper : ∀ n, LStarInstanceFG → Bits (expWLen n) := fun n L_raw =>
    -- If L_raw is a planted instance (satisfies the subtype predicate), use f_family.
    -- Otherwise, return a dummy witness (will never be queried in the proof).
    if h : ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
        L_raw = plant_flat n (Φ n) r
          (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
          (alignedCNFFamily_aligned n h_n) then
      f_family n ⟨L_raw, h⟩
    else
      Vector.replicate (expWLen n) false

  -- Extract polynomial bounds from h_fp to build the uniform solver
  rcases h_fp with ⟨C_fp, deg_fp, T_fp, M_fp, h_det_fp, h_correct_fp_M, h_time_fp⟩

  -- Build InFP_parametric_bits for f_wrapper
  -- Key insight: The M_fp solver returns ⟨n, result⟩ where result has the right type
  -- because h_correct_fp_M guarantees M_fp.run c ⟨n, x⟩ = ⟨n, f_family n x⟩
  have h_fp_wrapper : InFP_parametric_bits expWLen f_wrapper := by
    -- Build a uniform solver over LStarInstanceFG using M_fp
    -- For planted instances: use M_fp's result (which has correct type by h_correct_fp_M)
    -- For non-planted: return dummy
    -- InFP_parametric_bits = ∃ C deg T M, (det) ∧ (correct) ∧ (poly)
    -- Build the AlgSpec explicitly first to avoid type inference issues
    let M_wrapper : AlgSpec (Sigma fun n => LStarInstanceFG) (Sigma fun n => Bits (expWLen n)) T_fp := {
        run := fun c ⟨n, L_raw⟩ =>
          if h : ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
              L_raw = plant_flat n (Φ n) r
                (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
                (alignedCNFFamily_aligned n h_n) then
            -- For planted: M_fp.run c ⟨n, L_planted⟩ = ⟨n, f_family n L_planted⟩ by h_correct_fp_M
            -- So we can use the correctness to get the right type
            ⟨n, f_family n ⟨L_raw, h⟩⟩
          else
            ⟨n, Vector.replicate (expWLen n) false⟩
        -- Use an inflated time_bound: sum ensures both original bound and linear lower bound
        time_bound := fun m => M_fp.time_bound m + 4 * m + 200
        C := M_fp.C + 200
        k := max M_fp.k 2
        h_C_pos := by have := M_fp.h_C_pos; omega
        h_k_pos := by omega
        poly_explicit := fun inp => by
          -- time_bound m = M_fp.time_bound m + 4*m + 200
          -- ≤ M_fp.C*(m+1)^k + 4*m + 200
          -- ≤ M_fp.C*(m+1)^k + 200*(m+1)   (since 4*m + 200 ≤ 200*(m+1) = 200m+200 for m ≥ 0)
          -- ≤ (M_fp.C + 200)*(m+1)^k (since (m+1) ≤ (m+1)^k for k ≥ 1)
          let m := Sized.size inp
          have h_fp := M_fp.time_bound_uniform m
          have h_C_pos : M_fp.C ≥ 1 := M_fp.h_C_pos
          have h_k_pos : M_fp.k ≥ 1 := M_fp.h_k_pos
          have h_k2 : max M_fp.k 2 ≥ 2 := by omega
          have h_pow_ge : (m + 1) ^ (max M_fp.k 2) ≥ (m + 1) ^ 2 :=
            Nat.pow_le_pow_right (by omega) h_k2
          have h_sq_ge : (m + 1) ^ 2 ≥ m + 1 := by nlinarith
          have h_pow1 : (m + 1) ^ (max M_fp.k 2) ≥ m + 1 := by omega
          have h_lin : 4 * m + 200 ≤ 200 * (m + 1) := by omega
          have h_lin2 : 200 * (m + 1) ≤ 200 * (m + 1) ^ (max M_fp.k 2) := by
            apply Nat.mul_le_mul_left; exact h_pow1
          calc M_fp.time_bound m + 4 * m + 200
              ≤ M_fp.C * (m + 1) ^ M_fp.k + 4 * m + 200 := by omega
            _ ≤ M_fp.C * (m + 1) ^ (max M_fp.k 2) + 4 * m + 200 := by
                apply Nat.add_le_add_right
                apply Nat.add_le_add_right
                apply Nat.mul_le_mul_left
                exact Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
            _ ≤ M_fp.C * (m + 1) ^ (max M_fp.k 2) + 200 * (m + 1) ^ (max M_fp.k 2) := by omega
            _ = (M_fp.C + 200) * (m + 1) ^ (max M_fp.k 2) := by ring
        time_bound_uniform := fun m => by
          have h_fp := M_fp.time_bound_uniform m
          have h_C_pos : M_fp.C ≥ 1 := M_fp.h_C_pos
          have h_k_pos : M_fp.k ≥ 1 := M_fp.h_k_pos
          have h_k2 : max M_fp.k 2 ≥ 2 := by omega
          have h_pow1 : (m + 1) ^ (max M_fp.k 2) ≥ m + 1 := by
            have h_sq : (m + 1) ^ 2 ≥ m + 1 := by nlinarith
            have := Nat.pow_le_pow_right (by omega : m + 1 ≥ 1) h_k2
            omega
          calc M_fp.time_bound m + 4 * m + 200
              ≤ M_fp.C * (m + 1) ^ M_fp.k + 4 * m + 200 := by
                have := h_fp; omega
            _ ≤ M_fp.C * (m + 1) ^ (max M_fp.k 2) + 200 * (m + 1) := by
                have := Nat.pow_le_pow_right (by omega : m + 1 ≥ 1) (Nat.le_max_left M_fp.k 2)
                nlinarith
            _ ≤ M_fp.C * (m + 1) ^ (max M_fp.k 2) + 200 * (m + 1) ^ (max M_fp.k 2) := by
                apply Nat.add_le_add_left
                apply Nat.mul_le_mul_left
                exact h_pow1
            _ = (M_fp.C + 200) * (m + 1) ^ (max M_fp.k 2) := by ring
        output_bounded := fun c ⟨n, L_raw⟩ => by
          -- time_bound m ≥ 4*m + 200, so output (3n + 66) ≤ time_bound (n + 1 + dag.n)
          -- since 3n + 66 ≤ 4*(n + 1 + dag.n) + 200 = 4n + 4 + 4*dag.n + 200
          have h_n_pos : L_raw.n > 0 := L_raw.n_pos
          have h_dag_ge : L_raw.dag.n ≥ L_raw.n := L_raw.dag_size_ge_n
          have h_dag_pos : L_raw.dag.n > 0 := by omega
          -- Split on whether L_raw is planted or not
          by_cases h : ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
              L_raw = plant_flat n (Φ n) r
                (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
                (alignedCNFFamily_aligned n h_n)
          · -- Planted case: output is ⟨n, f_family n ⟨L_raw, h⟩⟩
            simp only [h, dif_pos, Sized.size, sizedSigma, sizedNat, sizedBitstring, expWLen]
            -- Output size: n + 1 + (2n + 65) = 3n + 66
            -- time_bound (n + 1 + dag.n) = M_fp.time_bound (...) + 4*(...) + 200 ≥ 4*(n + 1 + dag.n) + 200
            have h_lower : M_fp.time_bound (n + 1 + L_raw.dag.n) + 4 * (n + 1 + L_raw.dag.n) + 200
                           ≥ 4 * (n + 1 + L_raw.dag.n) + 200 := by omega
            omega
          · -- Non-planted case: output is ⟨n, Vector.replicate (expWLen n) false⟩
            simp only [h, dif_neg, not_false_eq_true, Sized.size, sizedSigma, sizedNat, sizedBitstring, expWLen]
            have h_lower : M_fp.time_bound (n + 1 + L_raw.dag.n) + 4 * (n + 1 + L_raw.dag.n) + 200
                           ≥ 4 * (n + 1 + L_raw.dag.n) + 200 := by omega
            omega
        coins_pos := M_fp.coins_pos
      }
    -- Now use the explicit AlgSpec in the existential
    -- Use M_wrapper.C = M_fp.C + 200 and M_wrapper.k = max M_fp.k 2
    refine ⟨M_fp.C + 200, max M_fp.k 2, T_fp, M_wrapper, ?det, ?correct, ?poly⟩
    case det =>
      intro c₁ c₂ ⟨n, L_raw⟩
      rfl
    case correct =>
      intro n L_raw
      simp only [M_wrapper]
      by_cases h : ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
          L_raw = plant_flat n (Φ n) r
            (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
            (alignedCNFFamily_aligned n h_n)
      · simp only [h, dif_pos, f_wrapper]
      · simp only [h, dif_neg, not_false_eq_true, f_wrapper]
    case poly =>
      exact M_wrapper.time_bound_uniform

  -- Build the witness-finder existence property required by structural_owf_inversion_not_in_fp.
  -- For planted instances, f_wrapper = f_family which correctly inverts.
  have h_inverts : ∃ N₀ : Nat, ∀ n ≥ N₀, ∀ L : LStarInstanceFG,
      (∃ w, StructuralOWFInversionRelation_exp Φ
        (fun n h => by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h]; omega)
        LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
        alignedCNFFamily_aligned n L w) →
      StructuralOWFInversionRelation_exp Φ
        (fun n h => by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h]; omega)
        LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
        alignedCNFFamily_aligned n L (f_wrapper n L) := by
    refine ⟨128, ?_⟩
    intro n h_n_ge_128 L h_exists
    -- The key is that structural_owf_inversion_not_in_fp only queries planted instances.
    -- For any L with ∃ w, R n L w, L must be a planted instance (from the construction).
    -- We need to show that f_wrapper n L produces a valid witness.
    --
    -- Since h_exists gives us a witness, L is in the image of plant_flat.
    -- The OWF inversion relation is defined so that only planted instances can have witnesses.
    -- Therefore, L satisfies the PlantedInstance predicate.
    --
    -- Extract the planted structure from h_exists
    rcases h_exists with ⟨w, h_R_w⟩
    -- Show L is a planted instance using OWF relation definition
    -- By StructuralOWFInversionRelation_exp: if R n L w holds, then L comes from plant_flat.
    have h_planted : ∃ (h_n : n ≥ 128) (r : Randomness (Φ n).nvars),
        L = plant_flat n (Φ n) r
          (by rw [LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq n h_n]; omega)
          (alignedCNFFamily_aligned n h_n) := by
      -- Unfold StructuralOWFInversionRelation_exp to extract L = plant_flat ...
      unfold StructuralOWFInversionRelation_exp at h_R_w
      simp only [h_n_ge_128, dite_true] at h_R_w
      -- h_R_w now says: L = plant_flat n (Φ n) r_φ ... ∧ (Φ n).satisfies r_φ.assignmentInf
      rcases h_R_w with ⟨h_L_eq, _h_sat⟩
      -- The randomness r is derived from the witness w
      let r := bitsToRandomness_exp n (by omega : n > 0) w
      let r_φ : Randomness (Φ n).nvars := (h_nvars_eq n h_n_ge_128).symm ▸ r
      refine ⟨h_n_ge_128, r_φ, h_L_eq⟩
    -- Now unfold f_wrapper with the planted structure
    simp only [f_wrapper, h_planted, dif_pos]
    -- Use h_correct_fp to get correctness of f_family
    -- f_family n ⟨L, h_planted⟩ correctly inverts for planted instances
    -- Note: Need to carefully handle the proof terms in StructuralOWFInversionRelation_exp
    let L_planted : PlantedInstance n := ⟨L, h_planted⟩
    have h_L_val : L_planted.val = L := rfl
    have h_decision : BitstringBridge.decision_lang expWLen R_lifted n L_planted := by
      refine ⟨w, ?_⟩
      -- R_lifted n L_planted w = StructuralOWFInversionRelation_exp ... n L_planted.val w = ... n L w
      unfold R_lifted
      rw [h_L_val]
      exact h_R_w
    have h_fp_correct := h_correct_fp n L_planted h_decision
    -- h_fp_correct : R_lifted n L_planted (f_family n L_planted)
    -- Goal: StructuralOWFInversionRelation_exp ... n L (f_family n ⟨L, h_planted⟩)
    -- Since L_planted = ⟨L, h_planted⟩ and L_planted.val = L, and f_family n L_planted = f_family n ⟨L, h_planted⟩
    unfold R_lifted at h_fp_correct
    rw [h_L_val] at h_fp_correct
    exact h_fp_correct

  exact h_not_fp ⟨f_wrapper, h_fp_wrapper, h_inverts⟩

/-- **Prefix Language Encoding is Polytime**.

    The encoding encPrefixSigma : PrefixSigma → List Bool satisfies polynomial bounds. -/
noncomputable def encPrefixSigma_polytime : PolytimeEncoding encPrefixSigma where
  enc_injective := by
    classical
    intro ⟨n₁, inp₁⟩ ⟨n₂, inp₂⟩ h_eq
    -- Unfold and parse the unary segments deterministically using readUnaryLen.
    -- Note: inp.input is PlantedInstance n, so we use .val to get LStarInstanceFG
    let encL₁ := encodeBits inp₁.input.val
    let encL₂ := encodeBits inp₂.input.val
    let pref₁ := inp₁.pref.val
    let pref₂ := inp₂.pref.val

    let rest₁ :=
      encodeNatUnary encL₁.length ++ [false] ++ encL₁ ++
        encodeNatUnary pref₁.length ++ [false] ++ pref₁ ++ [inp₁.bit]
    let rest₂ :=
      encodeNatUnary encL₂.length ++ [false] ++ encL₂ ++
        encodeNatUnary pref₂.length ++ [false] ++ pref₂ ++ [inp₂.bit]

    have h_read : readUnaryLen (encPrefixSigma ⟨n₁, inp₁⟩) = readUnaryLen (encPrefixSigma ⟨n₂, inp₂⟩) :=
      congrArg readUnaryLen h_eq
    have h_dec₁ : readUnaryLen (encPrefixSigma ⟨n₁, inp₁⟩) = some (n₁, rest₁) := by
      simpa [encPrefixSigma, encodeNatUnary, rest₁, List.append_assoc] using
        (readUnaryLen_replicate n₁ rest₁)
    have h_dec₂ : readUnaryLen (encPrefixSigma ⟨n₂, inp₂⟩) = some (n₂, rest₂) := by
      simpa [encPrefixSigma, encodeNatUnary, rest₂, List.append_assoc] using
        (readUnaryLen_replicate n₂ rest₂)
    have h_some : some (n₁, rest₁) = some (n₂, rest₂) := by simpa [h_dec₁, h_dec₂] using h_read
    have h_pair : (n₁, rest₁) = (n₂, rest₂) := Option.some.inj h_some
    have hn : n₁ = n₂ := by simpa using congrArg Prod.fst h_pair
    have hrest : rest₁ = rest₂ := by simpa using congrArg Prod.snd h_pair
    subst hn

    -- Parse |encL| and isolate encL.
    let tail₁ := encL₁ ++ encodeNatUnary pref₁.length ++ [false] ++ pref₁ ++ [inp₁.bit]
    let tail₂ := encL₂ ++ encodeNatUnary pref₂.length ++ [false] ++ pref₂ ++ [inp₂.bit]
    have h_len_read : readUnaryLen rest₁ = readUnaryLen rest₂ := congrArg readUnaryLen hrest
    have h_len₁ : readUnaryLen rest₁ = some (encL₁.length, tail₁) := by
      simpa [rest₁, encodeNatUnary, tail₁, List.append_assoc] using
        (readUnaryLen_replicate encL₁.length tail₁)
    have h_len₂ : readUnaryLen rest₂ = some (encL₂.length, tail₂) := by
      simpa [rest₂, encodeNatUnary, tail₂, List.append_assoc] using
        (readUnaryLen_replicate encL₂.length tail₂)
    have h_some2 : some (encL₁.length, tail₁) = some (encL₂.length, tail₂) := by
      simpa [h_len₁, h_len₂] using h_len_read
    have h_pair2 : (encL₁.length, tail₁) = (encL₂.length, tail₂) := Option.some.inj h_some2
    have h_encL_len : encL₁.length = encL₂.length := by simpa using congrArg Prod.fst h_pair2
    have h_tail : tail₁ = tail₂ := by simpa using congrArg Prod.snd h_pair2

    -- Use the length equality to isolate encL segments.
    have h_encL_eq : encL₁ = encL₂ := by
      -- Take the first |encL| bits from both tails.
      have : List.take encL₁.length tail₁ = List.take encL₁.length tail₂ := by simpa [h_tail]
      -- Left side simplifies to encL₁, right side to encL₂ (using length equality).
      simpa [tail₁, tail₂, take_len_append, h_encL_len] using this

    -- inp.input is PlantedInstance n (a subtype), prove equality via Subtype.ext
    have h_val_eq : inp₁.input.val = inp₂.input.val := encodeBits_injective h_encL_eq
    have h_input_eq : inp₁.input = inp₂.input := Subtype.ext h_val_eq

    -- Drop encL, then parse |pref| and isolate pref and bit.
    have h_tail_drop : List.drop encL₁.length tail₁ = List.drop encL₁.length tail₂ := by
      simpa [h_tail]
    have h_after_encL :
        encodeNatUnary pref₁.length ++ [false] ++ pref₁ ++ [inp₁.bit] =
        encodeNatUnary pref₂.length ++ [false] ++ pref₂ ++ [inp₂.bit] := by
      simpa [tail₁, tail₂, drop_len_append, h_encL_len] using h_tail_drop

    have h_preflen_read : readUnaryLen (encodeNatUnary pref₁.length ++ [false] ++ (pref₁ ++ [inp₁.bit])) =
        readUnaryLen (encodeNatUnary pref₂.length ++ [false] ++ (pref₂ ++ [inp₂.bit])) := by
      simpa [List.append_assoc] using congrArg readUnaryLen h_after_encL

    have h_preflen₁ : readUnaryLen (encodeNatUnary pref₁.length ++ [false] ++ (pref₁ ++ [inp₁.bit])) =
        some (pref₁.length, pref₁ ++ [inp₁.bit]) := by
      simpa [encodeNatUnary, List.append_assoc] using
        (readUnaryLen_replicate pref₁.length (pref₁ ++ [inp₁.bit]))
    have h_preflen₂ : readUnaryLen (encodeNatUnary pref₂.length ++ [false] ++ (pref₂ ++ [inp₂.bit])) =
        some (pref₂.length, pref₂ ++ [inp₂.bit]) := by
      simpa [encodeNatUnary, List.append_assoc] using
        (readUnaryLen_replicate pref₂.length (pref₂ ++ [inp₂.bit]))
    have h_some3 : some (pref₁.length, pref₁ ++ [inp₁.bit]) = some (pref₂.length, pref₂ ++ [inp₂.bit]) := by
      rw [← h_preflen₁, ← h_preflen₂]
      exact h_preflen_read
    have h_pair3 : (pref₁.length, pref₁ ++ [inp₁.bit]) = (pref₂.length, pref₂ ++ [inp₂.bit]) :=
      Option.some.inj h_some3
    have h_pref_len : pref₁.length = pref₂.length := by simpa using congrArg Prod.fst h_pair3
    have h_prefbit : pref₁ ++ [inp₁.bit] = pref₂ ++ [inp₂.bit] := by simpa using congrArg Prod.snd h_pair3
    have h_pref_eq : pref₁ = pref₂ := by
      -- take first |pref| bits
      have : List.take pref₁.length (pref₁ ++ [inp₁.bit]) = List.take pref₁.length (pref₂ ++ [inp₂.bit]) := by
        simpa [h_prefbit]
      simpa [take_len_append, h_pref_len] using this
    have h_bit_eq : inp₁.bit = inp₂.bit := by
      -- drop |pref| bits, remaining singleton bit lists must match
      have : List.drop pref₁.length (pref₁ ++ [inp₁.bit]) = List.drop pref₁.length (pref₂ ++ [inp₂.bit]) := by
        simpa [h_prefbit]
      simpa [drop_len_append, h_pref_len] using this

    -- Finish: equality of PrefixInput fields implies equality of the Sigma pair.
    have h_inp : inp₁ = inp₂ := by
      cases inp₁ with
      | mk input1 prefSub1 bit1 =>
        cases inp₂ with
        | mk input2 prefSub2 bit2 =>
          have h_input : input1 = input2 := by simpa using h_input_eq
          have h_bit : bit1 = bit2 := by simpa using h_bit_eq
          -- prefSub1.val = prefSub2.val follows from h_pref_eq (which is on the .val lists).
          have h_pref_val : prefSub1.val = prefSub2.val := by
            -- pref₁/pref₂ were defined as inp₁.pref.val / inp₂.pref.val.
            simpa [pref₁, pref₂] using h_pref_eq
          cases h_input
          have h_pref_sub : prefSub1 = prefSub2 := by
            apply Subtype.ext
            exact h_pref_val
          cases h_pref_sub
          cases h_bit
          rfl
    cases h_inp
    rfl
  -- Upper bound: use a conservative polynomial (degree 4) to absorb length tags + encodeBits overhead.
  C_up := 2^72
  k_up := 4
  h_C_up_pos := by simp only [Nat.pos_iff_ne_zero]; decide
  h_k_up_pos := by omega
  size_upper := by
    intro ⟨n, inp⟩
    -- Let s be the sized measure of the structured input.
    let s := Sized.size (⟨n, inp⟩ : PrefixSigma)
    -- Note: inp.input is PlantedInstance n, use .val for LStarInstanceFG
    let encL := encodeBits inp.input.val
    let pref := inp.pref.val
    -- encodeBits upper bound (on the underlying LStarInstanceFG)
    have h_encL : encL.length ≤ 2^70 * (Sized.size inp.input.val + 1) ^ 3 :=
      encodeBits_polytime.size_upper inp.input.val
    -- Sized.size inp.input = Sized.size inp.input.val (by instSizedPlantedInstance)
    have h_size_eq : Sized.size inp.input = Sized.size inp.input.val := rfl
    have h_inp_le : Sized.size inp.input + 1 ≤ s + 1 := by
      simp [PrefixSigma, s, Sized.size]
      omega
    have h_encL' : encL.length ≤ 2^70 * (s + 1) ^ 3 := by
      calc encL.length
          ≤ 2^70 * (Sized.size inp.input + 1) ^ 3 := h_encL
        _ ≤ 2^70 * (s + 1) ^ 3 := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_left
            exact h_inp_le
    -- Total encoding length is at most: 2*|encL| + 2*|pref| + n + O(1)
    have h_len : (encPrefixSigma ⟨n, inp⟩).length ≤ 2 * encL.length + 2 * pref.length + n + 10 := by
      -- Expand the definition and bound each segment by its length.
      simp [encPrefixSigma, encodeNatUnary, encL, pref]
      omega
    have h_pref_le : pref.length ≤ s := by
      -- s = Sized.size ⟨n, inp⟩ = Sized.size n + Sized.size inp (by sizedSigma)
      -- Sized.size inp = Sized.size inp.input + Sized.size inp.pref.val + 1 (by instSizedPrefixInput)
      -- Sized.size inp.pref.val = pref.length + 1 (by sizedList)
      -- So s ≥ pref.length + 1 ≥ pref.length
      simp only [s]
      simp only [Sized.size, sizedSigma, instSizedPrefixInput, sizedList, pref]
      omega
    have h_n_le : n ≤ s := by
      simp [PrefixSigma, s, Sized.size]
      omega
    -- Convert to a polynomial in (s+1)^4.
    have h_dom1 : 2 * encL.length ≤ 2^71 * (s + 1) ^ 4 := by
      have h_pow : (s + 1) ^ 3 ≤ (s + 1) ^ 4 := by
        apply Nat.pow_le_pow_right
        omega
        omega
      calc 2 * encL.length
          ≤ 2 * (2^70 * (s + 1) ^ 3) := by omega
        _ = 2^71 * (s + 1) ^ 3 := by ring
        _ ≤ 2^71 * (s + 1) ^ 4 := by
            apply Nat.mul_le_mul_left
            exact h_pow
    have h_dom2 : 2 * pref.length + n + 10 ≤ 10 * (s + 1) ^ 4 := by
      have h_pow_ge : s + 1 ≤ (s + 1) ^ 4 := by
        have : 4 ≠ 0 := by omega
        exact Nat.le_self_pow this (s + 1)
      calc
        2 * pref.length + n + 10
            ≤ 2 * s + s + 10 := by omega
        _ = 3 * s + 10 := by ring
        _ ≤ 10 * (s + 1) := by omega
        _ ≤ 10 * (s + 1) ^ 4 := by
              apply Nat.mul_le_mul_left
              exact h_pow_ge
    have h_dom : 2 * encL.length + 2 * pref.length + n + 10 ≤ 2^72 * (s + 1) ^ 4 := by
      -- Combine h_dom1 and h_dom2 by addition.
      have h_add : 2 * encL.length + (2 * pref.length + n + 10) ≤
          2^71 * (s + 1) ^ 4 + 10 * (s + 1) ^ 4 :=
        Nat.add_le_add h_dom1 h_dom2
      have h_add' : 2 * encL.length + 2 * pref.length + n + 10 ≤
          2^71 * (s + 1) ^ 4 + 10 * (s + 1) ^ 4 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc] using h_add
      -- Now simplify RHS and absorb constants into 2^72.
      have h_const : 2^71 + 10 ≤ 2^72 := by native_decide
      calc
        2 * encL.length + 2 * pref.length + n + 10
            ≤ 2^71 * (s + 1) ^ 4 + 10 * (s + 1) ^ 4 := h_add'
        _ = (2^71 + 10) * (s + 1) ^ 4 := by ring
        _ ≤ 2^72 * (s + 1) ^ 4 := by
              apply Nat.mul_le_mul_right
              exact h_const
    -- Finish.
    have : (encPrefixSigma ⟨n, inp⟩).length ≤ 2^72 * (s + 1) ^ 4 := by
      exact Nat.le_trans h_len h_dom
    simpa [s] using this
  -- Lower bound: size ≤ 3*(|enc| + 1)
  C_lo := 3
  k_lo := 1
  h_C_lo_pos := by omega
  h_k_lo_pos := by omega
  size_lower := by
    intro ⟨n, inp⟩
    -- Note: inp.input is PlantedInstance n, use .val for LStarInstanceFG
    let encL := encodeBits inp.input.val
    let pref := inp.pref.val
    -- Sized.size inp.input = Sized.size inp.input.val (by instSizedPlantedInstance)
    have h_sizeL : Sized.size inp.input ≤ encL.length + 1 := encodeBits_size_lower inp.input.val
    have h_n : n ≤ (encPrefixSigma ⟨n, inp⟩).length := by
      -- Unary n contributes n bits.
      simp [encPrefixSigma, encodeNatUnary]
    have h_pref : pref.length ≤ (encPrefixSigma ⟨n, inp⟩).length := by
      simp [encPrefixSigma, encodeNatUnary, pref]
      omega
    have h_encL_len : encL.length ≤ (encPrefixSigma ⟨n, inp⟩).length := by
      simp [encPrefixSigma, encodeNatUnary, encL]
      omega
    -- size ⟨n,inp⟩ = n + size L + |pref| + 2 ≤ 3*(|enc|+1)
    have : Sized.size (⟨n, inp⟩ : PrefixSigma) ≤ 3 * ((encPrefixSigma ⟨n, inp⟩).length + 1) := by
      have h_encL_size : Sized.size inp.input ≤ (encPrefixSigma ⟨n, inp⟩).length + 1 := by
        calc Sized.size inp.input
            ≤ encL.length + 1 := h_sizeL
          _ ≤ (encPrefixSigma ⟨n, inp⟩).length + 1 := by omega
      -- Expand size and bound each component by |enc| (or |enc|+1) using the helper inequalities.
      simp [PrefixSigma, Sized.size]
      set E : Nat := (encPrefixSigma ⟨n, inp⟩).length
      have hnE : n ≤ E := by simpa [E] using h_n
      have hpE : pref.length ≤ E := by simpa [E] using h_pref
      have hsE : Sized.size inp.input ≤ E + 1 := by simpa [E] using h_encL_size
      have h_sum1 : n + Sized.size inp.input ≤ E + (E + 1) := Nat.add_le_add hnE hsE
      have h_sum2 : (n + Sized.size inp.input) + pref.length ≤ (E + (E + 1)) + E :=
        Nat.add_le_add h_sum1 hpE
      have h_sum3 : ((n + Sized.size inp.input) + pref.length) + 2 ≤ ((E + (E + 1)) + E) + 2 :=
        Nat.add_le_add_right h_sum2 2
      -- Reassociate to match the goal.
      have h_target : n + Sized.size inp.input + pref.length + 2 ≤ E + (E + 1) + E + 2 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_sum3
      -- Now convert to 3*(E+1).
      have : n + Sized.size inp.input + pref.length + 2 ≤ 3 * (E + 1) := by
        calc
          n + Sized.size inp.input + pref.length + 2
              ≤ E + (E + 1) + E + 2 := h_target
          _ = 3 * E + 3 := by ring
          _ = 3 * (E + 1) := by ring
      simpa [E] using this
    simpa [pow_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

/-- **Prefix Language over Bitstrings in NP**: PrefixLangBits is in NP.

    **Proof**: Apply `np_transfer` from LStarEncoding.lean:
    - PrefixLangSigma ∈ NP (from PrefixLangSigma_in_NP)
    - encPrefixSigma is a PolytimeEncoding (from encPrefixSigma_polytime)
    → PrefixLangBits = encodedLang encPrefixSigma PrefixLangSigma ∈ NP -/
theorem PrefixLangBits_in_NP : InNP PrefixLangBits := by
  exact np_transfer encPrefixSigma PrefixLangSigma encPrefixSigma_polytime PrefixLangSigma_in_NP

/-- **Prefix Language over Bitstrings not in P**: PrefixLangBits is not in P.

    **Proof**: Apply `hardness_transfer` from LStarEncoding.lean:
    - PrefixLangSigma ∉ P (from PrefixLangSigma_not_in_P)
    - encPrefixSigma is a PolytimeEncoding (from encPrefixSigma_polytime)
    → PrefixLangBits = encodedLang encPrefixSigma PrefixLangSigma ∉ P -/
theorem PrefixLangBits_not_in_P : ¬InP PrefixLangBits := by
  exact hardness_transfer encPrefixSigma PrefixLangSigma encPrefixSigma_polytime PrefixLangSigma_not_in_P

/-- **Prefix Language is explicit NP \ P witness over bitstrings**. -/
theorem PrefixLangBits_in_NP_not_in_P : InNP PrefixLangBits ∧ ¬InP PrefixLangBits :=
  ⟨PrefixLangBits_in_NP, PrefixLangBits_not_in_P⟩

/-- **Clean Explicit NP \ P Witness**: Using the prefix-extension language.

    This is the robust approach that composes directly with the existing
    FP≠FNP machinery without requiring self-reducibility or range-to-inversion bridges. -/
theorem exists_language_in_NP_not_in_P_clean :
    ∃ (L : Lang (List Bool)), InNP L ∧ ¬InP L :=
  ⟨PrefixLangBits, PrefixLangBits_in_NP_not_in_P⟩

#print axioms owf_bits
#print axioms OWFInversionRelation_bits
#print axioms OWFInversionLang_bits
#print axioms PrefixLangSigma_in_NP
#print axioms PrefixLangSigma_not_in_P
#print axioms encPrefixSigma_polytime
#print axioms PrefixLangBits_in_NP_not_in_P
#print axioms exists_language_in_NP_not_in_P_clean

end LStar.Encoding.BitstringOWF
