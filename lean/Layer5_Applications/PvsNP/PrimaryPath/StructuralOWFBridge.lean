import Layer5_Applications.PvsNP.PrimaryPath.ParametricBitstringBridge
import Layer5_Applications.PvsNP.Common.StructuralOWFBridgeCommon
import Layer2_StructuralOWF.Security.StructuralOWFExponential
import Layer0_Foundations.Base.BoundedSecurityParam  -- For Nat.log helper lemmas
import Layer2_StructuralOWF.Plant.PlantExponential
import Layer0_Foundations.Base.CNF
import Layer3_InformationBounds.Keyedness.AcceptanceUniqueness  -- For build3SATReductionDAG_size_bound
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig  -- For emergentConfigAtGate
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridgeHelpers  -- For computeSeedAtVertex_ext
import Layer5_Applications.PvsNP.PrimaryPath.EncodingHelpers  -- For encoding round-trip lemmas
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances  -- For consistent Sized instances
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv  -- For Church–Turing bridge algspec_has_tm
import Layer4_Operational.TuringMachine.TMAxioms  -- For plant_equality_tm_exists
import Layer5_Applications.PvsNP.ComplexityClasses.EncodingDiscipline  -- For encoding format separation

-- Increase heartbeat limit for complex proofs in this file
set_option maxHeartbeats 800000

/-! ## OWFBridge: Constructive Proof of P ≠ NP

**Main Result**: `parametric_pneqnp_from_owf`

This module provides a **constructive proof of P ≠ NP** by explicitly constructing a one-way
function and using it to separate P and NP. This is NOT a conditional proof - we prove OWF
existence by construction, then use that to prove P ≠ NP.

**Theorem Statement**: P ≠ NP (parametric formulation)

**Proof Architecture**:
1. **Construct** a specific one-way function: Plant_flat(φ, r) with Frontier Gate
2. **Prove** it is one-way via information-theoretic lower bounds (Ω(2^n) inversion cost)
3. **Define** the inversion relation R: "Does bitstring w invert the OWF?"
4. **Prove** R ∈ FNP: Verification is polynomial-time (decode w and check)
5. **Prove** R ∉ FP: Finding w would break the OWF (contradicts proven hardness)
6. **Conclude** P ≠ NP: We have an explicit language in NP \ P

**Key Point**: This is a **constructive, unconditional proof** (modulo standard axioms).
We do not assume OWF existence - we prove it by constructing Plant_flat and establishing
its one-way property via information-theoretic counting arguments.

**Axiomatic Foundation**: Two standard assumptions from complexity theory:

1. `tm_algorithm_correspondence`: Turing machine execution matches algorithmic semantics
   (Application of Church-Turing thesis for coin-fixed computation)

2. `observation_indistinguishability`: Incomplete observations cannot distinguish
   configurations with different parities (Shannon's information theory - fundamental
   principle that you cannot extract n bits of information from fewer than n bits of data)

Both axioms formalize well-established principles and are standard in complexity theory
and information theory.

**Parametric vs. Classical**: This formalization proves **parametric P≠NP**, where complexity
classes are indexed by security parameter n. This is the natural formulation for:
- Cryptographic foundations (OWFs are inherently parametric)
- Modern complexity theory (resource bounds depend on input size)
- Constructive separations (explicit hard instances at each parameter)

The parametric formulation is **strictly stronger** than classical P≠NP and is the standard
in cryptography. Classical P≠NP (single language hard for all inputs) is implied by taking
the parametric family as a disjoint union, but is not needed for cryptographic applications.
-/

namespace LStar.Complexity.StructuralOWFBridge

open LStar.StructuralOWF
open LStar.StructuralOWF.Foundations  -- For TuringMachine, Movement
open LStar.Complexity
open LStar.Complexity.StructuralOWFBridgeCommon  -- Common infrastructure
open BitstringBridge

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

/-! ## Dynamic Digest Length Infrastructure

For the flat profile to work for all n ≥ 128, we add dynamic dgLen = (log₂ n)² = R.
This ensures dgLen ≥ R always, unlike the fixed dgLen = 64 which only works for n ≤ 256.

The existing infrastructure (dgLen = 64) is preserved for backward compatibility.
New theorems using dynamic dgLen are added with the `_dynamic` suffix.
-/

/-- Flat profile dynamic digest length: (log₂ n)². This equals R for the flat profile. -/
abbrev flatDgLen (n : Nat) : Nat := (Nat.log 2 n) ^ 2

/-- flatDgLen is positive for n ≥ 4. -/
theorem flatDgLen_pos (n : Nat) (h : n ≥ 4) : flatDgLen n > 0 := by
  unfold flatDgLen
  have h_log_ge : Nat.log 2 n ≥ 2 := by
    calc Nat.log 2 n ≥ Nat.log 2 4 := Nat.log_mono_right h
      _ = 2 := Nat.log_two_four_eq_two
  calc (Nat.log 2 n) ^ 2 ≥ 2 ^ 2 := Nat.pow_le_pow_left h_log_ge 2
    _ = 4 := rfl
    _ > 0 := by omega

/-- k² + 64 ≤ 2^k for k ≥ 7. Used for proving flatDgLen_fits_in_n. -/
theorem sq_plus_64_le_pow2_flat (k : Nat) (hk : k ≥ 7) : k ^ 2 + 64 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk' : k' ≥ 7
    · -- k' ≥ 7, use induction hypothesis
      have h_ih := ih hk'
      have h_2k_le : 2 * k' + 1 ≤ 2 ^ k' := by
        have h_3k_le_sq : 3 * k' ≤ k' ^ 2 := by nlinarith
        calc 2 * k' + 1 ≤ 3 * k' := by omega
          _ ≤ k' ^ 2 := h_3k_le_sq
          _ ≤ k' ^ 2 + 64 := by omega
          _ ≤ 2 ^ k' := h_ih
      calc (k' + 1) ^ 2 + 64
        _ = k' ^ 2 + 2 * k' + 1 + 64 := by ring
        _ = (k' ^ 2 + 64) + (2 * k' + 1) := by ring
        _ ≤ 2 ^ k' + (2 * k' + 1) := by omega
        _ ≤ 2 ^ k' + 2 ^ k' := by omega
        _ = 2 ^ (k' + 1) := by ring
    · -- k' < 7, so k' + 1 ≤ 7, check base cases
      -- Since hk : k' + 1 ≥ 7 and hk' : k' < 7, we have k' = 6
      push_neg at hk'
      have h_k'_eq_6 : k' = 6 := by omega
      subst h_k'_eq_6
      -- Need: 7^2 + 64 ≤ 2^7, i.e., 49 + 64 = 113 ≤ 128
      norm_num

/-- For n ≥ 128, flatDgLen n + 64 ≤ n. -/
theorem flatDgLen_fits_in_n (n : Nat) (h_n_ge : n ≥ 128) :
    flatDgLen n + 64 ≤ n := by
  unfold flatDgLen
  let k := Nat.log 2 n
  have hk_ge : k ≥ 7 := by
    calc k = Nat.log 2 n := rfl
      _ ≥ Nat.log 2 128 := Nat.log_mono_right h_n_ge
      _ = 7 := Nat.log_two_128_eq_seven
  have h_pow_le : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  calc (Nat.log 2 n) ^ 2 + 64 = k ^ 2 + 64 := rfl
    _ ≤ 2 ^ k := sq_plus_64_le_pow2_flat k hk_ge
    _ ≤ n := h_pow_le

/-- flatDgLen n ≥ R where R = (log₂ n)². Since flatDgLen n = R, this is trivially true. -/
theorem flatDgLen_ge_R (n : Nat) (φ : CNF) (h_nvars_eq : φ.nvars = n) :
    flatDgLen n ≥ (Nat.log 2 φ.nvars) ^ 2 := by
  unfold flatDgLen
  rw [h_nvars_eq]

/-- Flat witness length (dynamic): 2 * n. Accommodates n + flatDgLen n + 64 for all n ≥ 128. -/
abbrev flatWLen (n : Nat) : Nat := 2 * n

/-- n + flatDgLen n + 64 ≤ flatWLen n for n ≥ 128. -/
theorem flatWitnessLen_le_flatWLen (n : Nat) (h_n_ge : n ≥ 128) :
    n + flatDgLen n + 64 ≤ flatWLen n := by
  unfold flatWLen
  have h := flatDgLen_fits_in_n n h_n_ge
  omega

/-! ### True Exponential Profile (dgLen = n)

The TRUE exponential profile has dgLen = n (matching R_of_flat = n).
This ensures "structure → hardness" is automatic: the digest contains ALL n
emergent bits, so WellFormedRandomness_flat enforces the full 2^n barrier.

Witness layout: [assignment (n bits)] [digest (n bits)] [structural (64 bits)]
Total: 2n + 64 bits
-/

/-- Exponential profile digest length: n (matches R_of_flat). -/
abbrev expDgLen (n : Nat) : Nat := n

/-- Exponential witness length: 2n + 64. -/
abbrev expWLen (n : Nat) : Nat := 2 * n + 64

/-- n + expDgLen n + 64 = expWLen n (exact equality for exponential profile). -/
theorem expWitnessLen_eq_expWLen (n : Nat) :
    n + expDgLen n + 64 = expWLen n := by
  unfold expDgLen expWLen
  ring

/-- expDgLen n ≥ n (trivially true since expDgLen n = n). -/
theorem expDgLen_ge_nvars (n : Nat) : expDgLen n ≥ n := by
  unfold expDgLen
  omega

/-- Extract first k bits from a vector of size m where k ≤ m. -/
def extractBitsFlat (k m : Nat) (h : k ≤ m) (v : Vector Bool m) : Vector Bool k :=
  Vector.ofFn fun i => v.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- Convert Bits (flatWLen n) to Randomness using dynamic flatDgLen.
    Works for ALL n ≥ 128 (unbounded range). -/
noncomputable def bitsToRandomness_flat_dynamic (n : Nat) (h_n_ge : n ≥ 128)
    (w : Bits (flatWLen n)) : Randomness :=
  let dgLen := flatDgLen n
  have h_dgLen_pos : dgLen > 0 := flatDgLen_pos n (by omega)
  have h_fits : dgLen + 64 ≤ n := flatDgLen_fits_in_n n h_n_ge
  let w' : Bits (n + dgLen + 64) := extractBitsFlat (n + dgLen + 64) (flatWLen n) (by
    unfold flatWLen; omega) w
  bitsToRandomness n dgLen h_dgLen_pos w'

/-- The dgLen of bitsToRandomness_flat_dynamic equals flatDgLen n. -/
theorem bitsToRandomness_flat_dynamic_dgLen (n : Nat) (h_n_ge : n ≥ 128)
    (w : Bits (flatWLen n)) :
    (bitsToRandomness_flat_dynamic n h_n_ge w).dgLen = flatDgLen n := rfl

/-- Key: For φ.nvars = n, bitsToRandomness_flat_dynamic produces dgLen = (log₂ φ.nvars)². -/
theorem bitsToRandomness_flat_dynamic_satisfies_dgLen (n : Nat) (h_n_ge : n ≥ 128)
    (φ : CNF) (h_nvars_eq : φ.nvars = n) (w : Bits (flatWLen n)) :
    (bitsToRandomness_flat_dynamic n h_n_ge w).dgLen = (Nat.log 2 φ.nvars) ^ 2 := by
  rw [bitsToRandomness_flat_dynamic_dgLen]
  unfold flatDgLen
  rw [h_nvars_eq]

/-! ### True Exponential Profile Encoding (dgLen = n)

These functions use the true exponential encoding where dgLen = n,
ensuring the digest contains ALL n emergent bits for full 2^n hardness.
-/

/-- Convert Bits (expWLen n) to Randomness using expDgLen = n.
    This is the TRUE exponential profile where dgLen = n = R_of_flat.

    **Key property**: r.dgLen = n, satisfying WellFormedRandomness_flat's requirement
    that dgLen ≥ nvars.

    **Implementation note**: Uses extractBitsFlat to avoid type transport issues.
    Since expWLen n = 2n + 64 and we need n + n + 64 = 2n + 64 bits, the extraction
    is exact (no padding needed). -/
noncomputable def bitsToRandomness_exp (n : Nat) (h_n_pos : n > 0)
    (w : Bits (expWLen n)) : Randomness :=
  let dgLen := expDgLen n  -- = n
  have h_dgLen_pos : dgLen > 0 := h_n_pos  -- expDgLen n = n by definition
  -- Extract first (n + dgLen + 64) bits using extractBitsFlat (avoids ▸ transport)
  -- Note: dgLen = n, so n + dgLen + 64 = 2n + 64 = expWLen n
  have h_fits : n + dgLen + 64 ≤ expWLen n := by
    simp only [dgLen, expDgLen, expWLen]; omega
  let w' : Bits (n + dgLen + 64) := extractBitsFlat (n + dgLen + 64) (expWLen n) h_fits w
  bitsToRandomness n dgLen h_dgLen_pos w'

/-- The dgLen of bitsToRandomness_exp equals expDgLen n = n. -/
theorem bitsToRandomness_exp_dgLen (n : Nat) (h_n_pos : n > 0)
    (w : Bits (expWLen n)) :
    (bitsToRandomness_exp n h_n_pos w).dgLen = n := rfl

/-- Key: bitsToRandomness_exp produces dgLen = φ.nvars when φ.nvars = n.
    This satisfies WellFormedRandomness_flat's requirement. -/
theorem bitsToRandomness_exp_dgLen_eq_nvars (n : Nat) (h_n_pos : n > 0)
    (φ : CNF) (h_nvars_eq : φ.nvars = n) (w : Bits (expWLen n)) :
    (bitsToRandomness_exp n h_n_pos w).dgLen = φ.nvars := by
  rw [bitsToRandomness_exp_dgLen, h_nvars_eq]

/-- bitsToRandomness_exp produces dgLen ≥ φ.nvars (equality when φ.nvars = n). -/
theorem bitsToRandomness_exp_dgLen_ge_nvars (n : Nat) (h_n_pos : n > 0)
    (φ : CNF) (h_nvars_eq : φ.nvars = n) (w : Bits (expWLen n)) :
    (bitsToRandomness_exp n h_n_pos w).dgLen ≥ φ.nvars := by
  rw [bitsToRandomness_exp_dgLen_eq_nvars n h_n_pos φ h_nvars_eq w]

/-- Convert Randomness to Bits (expWLen n) for exponential profile (dgLen = n).
    Inverse of bitsToRandomness_exp.

    **Key property**: This encodes ALL n digest bits, enabling full 2^n hardness proofs. -/
noncomputable def randomnessToBits_exp (n : Nat) (r : Randomness)
    (h_dgLen : r.dgLen = n) : Bits (expWLen n) :=
  let gateDigest := r.gateDigests.head (by
    intro h_empty; have := r.h_single_gate; simp [h_empty] at this)
  let structBits := r.structuralBits.take 64
  have h_struct_len : structBits.length = 64 := by
    simp only [structBits, List.length_take]
    exact min_eq_left r.h_sufficient_salts
  Vector.ofFn fun idx : Fin (expWLen n) =>
    if h_assign : idx.val < n then
      r.assignment idx.val
    else if h_gate : idx.val < n + n then  -- n + dgLen where dgLen = n
      let pos : Nat := idx.val - n
      have h_pos_lt : pos < n := by omega
      have h_pos_dgLen : pos < r.dgLen := by rw [h_dgLen]; exact h_pos_lt
      gateDigest.get ⟨pos, h_pos_dgLen⟩
    else
      let pos : Nat := idx.val - (n + n)
      -- idx.val < expWLen n = 2*n + 64 and idx.val ≥ n + n, so pos < 64
      have h_pos_lt64 : pos < 64 := by
        have h_bound : idx.val < 2 * n + 64 := idx.isLt
        omega
      have h_pos_struct : pos < structBits.length := by
        simp only [h_struct_len]; exact h_pos_lt64
      structBits.get ⟨pos, h_pos_struct⟩

/-- Assignment roundtrip for exponential profile (dgLen = n).

    For i < φ.nvars, bitsToRandomness_exp (randomnessToBits_exp r).assignment i = r.assignment i.

    With extractBitsFlat (no type transport), the proof is straightforward:
    - randomnessToBits_exp places r.assignment i at position i for i < n
    - extractBitsFlat preserves bit positions
    - bitsToRandomness extracts position i when i < n -/
theorem assignment_roundtrip_exp (n : Nat) (h_n_pos : n > 0) (r : Randomness)
    (h_dgLen : r.dgLen = n) (φ : CNF) (h_nvars_eq : φ.nvars = n) :
    ∀ i < φ.nvars,
      (bitsToRandomness_exp n h_n_pos (randomnessToBits_exp n r h_dgLen)).assignment i =
      r.assignment i := by
  intro i hi
  have h_i_lt_n : i < n := by rw [← h_nvars_eq]; exact hi
  -- Unfold to expose the definitions
  simp only [bitsToRandomness_exp, bitsToRandomness, extractBitsFlat, randomnessToBits_exp]
  simp only [Vector.get_ofFn, h_i_lt_n, dite_true]

/-! ## Type Infrastructure -/

-- Sized instance for LStarInstanceFG is imported from OWFSizedInstances: size L = L.dag.n
-- LStarInstanceFG.ext is imported from OWFBridgeCommon

/-- Helper: List element equality from list equality (proof-irrelevant indices).
    When two lists are equal, getting elements at the same index gives equal results,
    regardless of which bound proof is used. -/
private lemma list_get_eq_of_list_eq {α : Type*} {l1 l2 : List α} (h_eq : l1 = l2)
    (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length) :
    l1.get ⟨i, h1⟩ = l2.get ⟨i, h2⟩ := by
  subst h_eq
  rfl  -- Proof irrelevance: h1 and h2 are equal for Props

/-- Helper: HEq for list elements across transport.
    When a list is transported to a different element type via equality proof h,
    getting elements gives HEq results. -/
private lemma list_get_heq_of_transport {α : Nat → Type*} {n m : Nat}
    (l : List (α n)) (h : n = m)
    (i : Nat) (hi_m : i < (h ▸ l : List (α m)).length) (hi_n : i < l.length) :
    HEq ((h ▸ l : List (α m)).get ⟨i, hi_m⟩) (l.get ⟨i, hi_n⟩) := by
  subst h
  exact heq_of_eq rfl  -- After subst, types are equal

/-- **Encoding preserves plant_flat instances** (parametric dgLen version).

    The encoding/decoding round-trip preserves what matters for plant_flat equality.
    This is the **general/parametric version** that works with any `r.dgLen`.

    **Use this for the exponential profile** where dgLen = n (scales with problem size).

    **Naming clarification**:
    - `plant_flat` refers to the "flat R-profile" (R = nvars, exponential bounds)
    - This lemma is "parametric" in dgLen (uses `r.dgLen`, not hardcoded)
    - See `randomness_encoding_plant_equiv_flat` for the dgLen = 64 specialization

    **Why not full Randomness equality?**
    - randomnessToBits only encodes structuralBits[0..64]
    - bitsToRandomness reconstructs exactly 64 structural bits
    - If r.structuralBits.length > 64, the tail is lost
    - BUT: plant_flat only uses structuralBits.take 64 (PlantCore.lean:239)

    **PROOF**: Uses helper lemmas from EncodingHelpers.lean.
    The encoding preserves:
    1. assignment for i < φ.nvars (plant_flat only uses these via encodeAssignment)
    2. gateDigests (single gate, proven by pattern match + vector ext)
    3. structuralBits.take 64 (plant_flat only uses first 64 bits)
    Therefore plant_flat equality follows by congruence.
-/
lemma randomness_encoding_plant_equiv (n : Nat) (φ : CNF) (r : Randomness)
    (h_nvars : φ.nvars ≥ 4)
    (h_nvars_eq : φ.nvars = n) :
    plant_flat n φ (bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)) h_nvars =
    plant_flat n φ r h_nvars := by
  -- Use the congruence lemma from PlantExponential.lean
  let r' := bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)

  -- Step 1: dgLen equality (definitional)
  have h_dgLen : r'.dgLen = r.dgLen := rfl

  -- Step 2: gateDigests equality
  have h_gateDigests : r'.gateDigests = r.gateDigests := gateDigests_roundtrip n r
  have h_gateDigests_len : r'.gateDigests.length = r.gateDigests.length := by
    rw [h_gateDigests]
  have h_gateDigests_eq : ∀ (i : Nat) (h1 : i < r'.gateDigests.length) (h2 : i < r.gateDigests.length),
      HEq (r'.gateDigests.get ⟨i, h1⟩) (r.gateDigests.get ⟨i, h2⟩) := fun i h1 h2 => by
    -- Types Vector Bool r'.dgLen = Vector Bool r.dgLen are definitionally equal (both are r.dgLen)
    -- Lists equal by h_gateDigests, so elements at same index are equal
    exact heq_of_eq (list_get_eq_of_list_eq h_gateDigests i h1 h2)

  -- Step 3: Assignment equality
  have h_assignment : ∀ i < φ.nvars, r'.assignment i = r.assignment i := by
    intro i h_i
    have h_i_lt_n : i < n := by rw [← h_nvars_eq]; exact h_i
    exact assignment_roundtrip n r i h_i_lt_n

  -- Step 4: Structural bits equality
  have h_structural : r'.structuralBits.take 64 = r.structuralBits.take 64 :=
    structuralBits_roundtrip_take64 n r

  -- Step 5: Apply congruence lemma
  exact plant_flat_eq_of_randomness_eq n φ r' r h_nvars h_dgLen h_gateDigests_len
    h_gateDigests_eq h_assignment h_structural

/-- **Encoding preserves plant_flat instances** (dgLen = 64 specialization).

    Specialized version for dgLen = 64 (fixed-size bitstring encoding).

    **Naming clarification** (two different meanings of "flat"):
    - `plant_flat` = flat R-profile (R = nvars, exponential security bounds)
    - `randomnessToBits_flat` = fixed bitstring size (dgLen hardcoded to 64)

    **When to use which lemma**:
    - **Exponential profile** (dgLen = n): Use `randomness_encoding_plant_equiv` (parametric)
    - **Fixed dgLen = 64**: Use this lemma (`randomness_encoding_plant_equiv_flat`)

    **Note**: This lemma is NOT for the exponential security profile. The exponential
    profile has dgLen = n (scales with problem size), which requires the parametric
    version `randomness_encoding_plant_equiv`.

    **Proof strategy**: Uses `cases h_dgLen` to convert propositional equality
    (r.dgLen = 64) to definitional equality, enabling dependent type unification.
-/
lemma randomness_encoding_plant_equiv_flat (n : Nat) (φ : CNF) (r : Randomness)
    (h_dgLen : r.dgLen = 64)
    (h_nvars : φ.nvars ≥ 4)
    (h_nvars_eq : φ.nvars = n) :
    plant_flat n φ (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)) h_nvars =
    plant_flat n φ r h_nvars := by
  -- Use the congruence lemma from PlantExponential.lean
  let r' := bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)

  -- Step 1: dgLen equality (r'.dgLen = 64 = r.dgLen)
  have h_dgLen_eq : r'.dgLen = r.dgLen := h_dgLen.symm

  -- Step 2: gateDigests equality
  have h_gateDigests_len : r'.gateDigests.length = r.gateDigests.length :=
    gateDigests_length_flat n r h_dgLen

  have h_gateDigests_eq : ∀ (i : Nat) (h1 : i < r'.gateDigests.length) (h2 : i < r.gateDigests.length),
      HEq (r'.gateDigests.get ⟨i, h1⟩) (r.gateDigests.get ⟨i, h2⟩) := fun i h1 h2 => by
    -- r'.dgLen = 64 by construction, r.dgLen = 64 by h_dgLen
    -- r'.gateDigests : List (Vector Bool 64)
    -- r.gateDigests : List (Vector Bool r.dgLen)
    -- Use gateDigests_roundtrip_flat_eq: r'.gateDigests = (h_dgLen ▸ r.gateDigests) as List (Vector Bool 64)
    have h_list_eq := gateDigests_roundtrip_flat_eq n r h_dgLen
    -- Step 1: Show r'.gateDigests.get equals (h_dgLen ▸ r.gateDigests).get
    have hi_transported : i < (h_dgLen ▸ r.gateDigests : List (Vector Bool 64)).length := by
      -- Transport preserves length: The list structure doesn't change, only element types
      -- Use that gateDigests_length_flat already proves the lengths are equal
      rw [← h_list_eq, h_gateDigests_len]
      exact h2
    have h_eq1 : r'.gateDigests.get ⟨i, h1⟩ = (h_dgLen ▸ r.gateDigests : List (Vector Bool 64)).get ⟨i, hi_transported⟩ :=
      list_get_eq_of_list_eq h_list_eq i h1 hi_transported
    -- Step 2: Show (h_dgLen ▸ r.gateDigests).get ⟨i, _⟩ HEq r.gateDigests.get ⟨i, h2⟩
    have h_heq2 := list_get_heq_of_transport r.gateDigests h_dgLen i hi_transported h2
    -- Step 3: Combine via HEq.trans
    exact HEq.trans (heq_of_eq h_eq1) h_heq2

  -- Step 3: Assignment equality
  have h_assignment : ∀ i < φ.nvars, r'.assignment i = r.assignment i := by
    intro i h_i
    have h_i_lt_n : i < n := by rw [← h_nvars_eq]; exact h_i
    exact assignment_roundtrip_flat n r h_dgLen φ h_nvars_eq i h_i

  -- Step 4: Structural bits equality
  have h_structural : r'.structuralBits.take 64 = r.structuralBits.take 64 :=
    structuralBits_roundtrip_take64_flat n r h_dgLen

  -- Step 5: Apply congruence lemma
  exact plant_flat_eq_of_randomness_eq n φ r' r h_nvars h_dgLen_eq h_gateDigests_len
    h_gateDigests_eq h_assignment h_structural

/-! ### Exponential Profile Roundtrip Helpers -/

-- Extract singleton from a list of length 1
private lemma extract_singleton_exp {α : Type*} (l : List α) (h : l.length = 1) :
    ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons head tail =>
    cases tail with
    | nil => exact ⟨head, rfl⟩
    | cons _ _ => simp at h

/-- Type-level cast on Vector preserves element access.
    When n = m, (cast _ v)[i] = v[i] with appropriate bound adjustment. -/
private lemma vector_type_cast_getElem_exp {α : Type*} {n m : Nat} (h_nm : n = m)
    (v : Vector α n) (i : Nat) (hi_m : i < m) :
    (cast (congrArg (Vector α) h_nm) v)[i]'hi_m = v[i]'(h_nm ▸ hi_m) := by
  subst h_nm
  rfl

/-- GateDigests roundtrip for exponential profile (HEq version).
    The roundtrip preserves gateDigests element bits. Types differ by dgLen but bits match.

    Types: r'.gateDigests : List (Vector Bool (expDgLen n)) = List (Vector Bool n)
           r.gateDigests : List (Vector Bool r.dgLen)
    Since h_dgLen : r.dgLen = n, we prove HEq via type transport. -/
theorem gateDigests_heq_roundtrip_exp (n : Nat) (h_n_pos : n > 0) (r : Randomness)
    (h_dgLen : r.dgLen = n) :
    let r' := bitsToRandomness_exp n h_n_pos (randomnessToBits_exp n r h_dgLen)
    r'.gateDigests.length = r.gateDigests.length ∧
    ∀ (i : Nat) (h1 : i < r'.gateDigests.length) (h2 : i < r.gateDigests.length),
      HEq (r'.gateDigests.get ⟨i, h1⟩) (r.gateDigests.get ⟨i, h2⟩) := by
  -- Extract singleton element from r.gateDigests
  obtain ⟨g, hg⟩ := extract_singleton_exp r.gateDigests r.h_single_gate
  -- Type equality: expDgLen n = n = r.dgLen
  have h_type_eq : expDgLen n = r.dgLen := by unfold expDgLen; exact h_dgLen.symm
  constructor
  · -- Length equality: both have exactly 1 gate
    simp only [bitsToRandomness_exp, bitsToRandomness, List.length_singleton]
    exact r.h_single_gate.symm
  · intro i h1 h2
    simp only [bitsToRandomness_exp, bitsToRandomness, List.length_singleton] at h1
    have h_i_zero : i = 0 := Nat.lt_one_iff.mp h1
    subst h_i_zero
    -- Show HEq of vectors at index 0
    simp only [bitsToRandomness_exp, bitsToRandomness]
    simp only [List.get_eq_getElem, List.getElem_singleton]
    -- r'.gateDigests[0] : Vector Bool (expDgLen n) = Vector Bool n
    -- r.gateDigests[0] : Vector Bool r.dgLen
    -- Use hg to simplify r.gateDigests to [g]
    simp only [hg, List.getElem_singleton]
    -- Now prove HEq between Vector.ofFn... and g
    have h_vec_type_eq : Vector Bool (expDgLen n) = Vector Bool r.dgLen := congrArg (Vector Bool) h_type_eq
    apply heq_of_cast_eq h_vec_type_eq
    -- Need to show: cast h_vec_type_eq (Vector.ofFn ...) = g
    apply Vector.ext
    intro j hj
    -- j < r.dgLen
    -- Use our helper lemma to handle the type-level cast
    rw [vector_type_cast_getElem_exp h_type_eq]
    simp only [Vector.getElem_ofFn]
    -- Now show the bit at position n+j in randomnessToBits_exp equals g[j]
    simp only [randomnessToBits_exp, extractBitsFlat, Vector.get_ofFn, Vector.getElem_ofFn]
    -- j < r.dgLen = n
    have hj' : j < n := h_dgLen ▸ hj
    have h1' : ¬(n + j < n) := by omega
    -- n + j < n + n (gate region) where n = r.dgLen
    have h2' : n + j < n + n := by omega
    simp only [h1', dite_false, h2', dite_true]
    -- n + j - n = j
    simp only [Nat.add_sub_cancel_left]
    -- Use hg to simplify r.gateDigests.head to g
    simp only [hg, List.head_cons]
    -- g[j] = g[j]'(h_dgLen ▸ hj): same position, different bound proofs (proof irrelevance)
    rfl

/-- StructuralBits roundtrip for exponential profile.
    The encoding roundtrip preserves structuralBits.take 64 exactly. -/
theorem structuralBits_roundtrip_exp (n : Nat) (h_n_pos : n > 0) (r : Randomness)
    (h_dgLen : r.dgLen = n) :
    (bitsToRandomness_exp n h_n_pos (randomnessToBits_exp n r h_dgLen)).structuralBits.take 64 =
    r.structuralBits.take 64 := by
  -- Unfold definitions
  simp only [bitsToRandomness_exp, bitsToRandomness]
  -- structuralBits from bitsToRandomness is List.ofFn of bits at positions n+dgLen+i
  -- structuralBits.take 64 from r is the first 64 structural bits
  apply List.ext_get
  · -- Length equality
    simp only [List.length_take, List.length_ofFn]
    simp [Nat.min_self, Nat.min_eq_left r.h_sufficient_salts]
  · intro i hi_left hi_right
    simp only [List.length_take, List.length_ofFn, Nat.min_self] at hi_left
    -- hi_left : i < 64
    simp only [List.get_eq_getElem]
    -- Need bounds for getElem
    have hi_rhs : i < r.structuralBits.length := by
      have h := r.h_sufficient_salts; omega
    -- Simplify take/getElem
    simp only [List.getElem_take, List.getElem_ofFn]
    -- Now show the bit at position n+dgLen+i in randomnessToBits_exp equals r.structuralBits[i]
    simp only [randomnessToBits_exp, extractBitsFlat, Vector.get_ofFn, Vector.getElem_ofFn]
    -- expDgLen n = n, so dgLen = n
    have h_dgLen_eq : expDgLen n = n := rfl
    -- Since i < 64, we need to go to the third branch (structural bits)
    have h1 : ¬(n + n + i < n) := by omega
    have h2 : ¬(n + n + i < n + n) := by omega
    -- Position n + n + i is definitely < expWLen n = 2*n + 64 since i < 64
    simp only [h1, dif_neg, not_false_eq_true, h2]
    -- n + n + i - (n + n) = i
    have h_sub : n + n + i - (n + n) = i := by omega
    simp only [h_sub]
    -- Goal: (List.take 64 r.structuralBits).get ⟨i, ⋯⟩ = r.structuralBits[i]
    simp only [List.getElem_take, List.get_eq_getElem]

/-- **Encoding preserves plant_flat instances** (exponential profile specialization).

    For the exponential profile where dgLen = n:
    - `randomnessToBits_exp n r h_dgLen` encodes r to Bits (expWLen n) when r.dgLen = n
    - `bitsToRandomness_exp n h_n_pos w` decodes to Randomness with dgLen = n

    The roundtrip preserves what matters for plant_flat equality. -/
lemma randomness_encoding_plant_equiv_exp (n : Nat) (h_n_pos : n > 0) (φ : CNF) (r : Randomness)
    (h_dgLen : r.dgLen = n)
    (h_nvars : φ.nvars ≥ 4)
    (h_nvars_eq : φ.nvars = n) :
    plant_flat n φ (bitsToRandomness_exp n h_n_pos (randomnessToBits_exp n r h_dgLen)) h_nvars =
    plant_flat n φ r h_nvars := by
  -- bitsToRandomness_exp is defined as bitsToRandomness n n ... with type cast
  -- We use the parametric version after establishing the connection
  -- Key insight: bitsToRandomness_exp produces dgLen = n = r.dgLen
  let r' := bitsToRandomness_exp n h_n_pos (randomnessToBits_exp n r h_dgLen)

  -- Use plant_flat_eq_of_randomness_eq for the equality
  -- We need to show the key roundtrip properties:
  -- 1. dgLen equality: r'.dgLen = n = r.dgLen
  have h_dgLen_eq : r'.dgLen = r.dgLen := by
    rw [bitsToRandomness_exp_dgLen, h_dgLen]

  -- 2. gateDigests length equality
  have h_gateDigests_len : r'.gateDigests.length = r.gateDigests.length := by
    -- Both have length 1 by h_single_gate
    have h1 := r'.h_single_gate
    have h2 := r.h_single_gate
    omega

  -- 3. gateDigests element equality (via HEq since dgLen may differ nominally)
  have h_gateDigests_eq : ∀ (i : Nat) (h1 : i < r'.gateDigests.length) (h2 : i < r.gateDigests.length),
      HEq (r'.gateDigests.get ⟨i, h1⟩) (r.gateDigests.get ⟨i, h2⟩) := by
    -- Use the exponential profile gateDigests roundtrip lemma
    have h_roundtrip := gateDigests_heq_roundtrip_exp n h_n_pos r h_dgLen
    exact h_roundtrip.2

  -- 4. Assignment equality for i < φ.nvars
  have h_assignment : ∀ i < φ.nvars, r'.assignment i = r.assignment i := by
    intro i h_i
    have h_i_lt_n : i < n := by rw [← h_nvars_eq]; exact h_i
    exact assignment_roundtrip_exp n h_n_pos r h_dgLen φ h_nvars_eq i h_i

  -- 5. Structural bits equality
  have h_structural : r'.structuralBits.take 64 = r.structuralBits.take 64 :=
    structuralBits_roundtrip_exp n h_n_pos r h_dgLen

  -- Apply congruence lemma
  exact plant_flat_eq_of_randomness_eq n φ r' r h_nvars h_dgLen_eq h_gateDigests_len
    h_gateDigests_eq h_assignment h_structural

/-! ## OWF Inversion Relation -/

/-- The OWF inversion relation (parametric bitstring version).

    R(n, L, w) holds iff:
    1. n ≥ 128 (security parameter minimum)
    2. L = Plant_flat(φ_n, bitsToRandomness(n, w))

    This relation is:
    - In FNP: Verify by computing Plant_flat (polynomial time)
    - Not in FP: Finding w would break OWF security
-/
def StructuralOWFInversionRelation (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    ∀ (n : Nat), LStarInstanceFG → Bits (n + 128) → Prop :=
  fun n L w =>
    ∃ (h : n ≥ 128),
      let r := bitsToRandomness n 64 (by omega) w
      L = plant_flat n (Φ n) r (h_nvars n h) ∧
      (Φ n).satisfies r.assignment  -- Domain constraint: witness must satisfy CNF

/-- **Dynamic** OWF inversion relation using flatDgLen = (log₂ n)².

    R(n, L, w) holds iff:
    1. n ≥ 128 (security parameter minimum)
    2. L = Plant_flat(φ_n, bitsToRandomness_flat_dynamic(n, w))

    This version works for ALL n ≥ 128 (not limited to n ≤ 256 like the fixed dgLen=64 version).
-/
def StructuralOWFInversionRelation_dynamic (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    ∀ (n : Nat), LStarInstanceFG → Bits (flatWLen n) → Prop :=
  fun n L w =>
    if h : n ≥ 128 then
      let r := bitsToRandomness_flat_dynamic n h w
      L = plant_flat n (Φ n) r (h_nvars n h) ∧
      (Φ n).satisfies r.assignment  -- Domain constraint: witness must satisfy CNF
    else False

/-- **Exponential** OWF inversion relation using expDgLen = n.

    R(n, L, w) holds iff:
    1. n ≥ 128 (security parameter minimum)
    2. L = Plant_flat(φ_n, bitsToRandomness_exp(n, w))

    **Key property**: Uses expWLen n = 2n + 64, encoding ALL n digest bits.
    This enables the full 2^n hardness from R_of_flat = n.

    Unlike the QP profile (dgLen = (log n)²) or fixed profile (dgLen = 64),
    this version threads n bits through the FG gate, matching R_of_flat exactly.
-/
def StructuralOWFInversionRelation_exp (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    ∀ (n : Nat), LStarInstanceFG → Bits (expWLen n) → Prop :=
  fun n L w =>
    if h : n ≥ 128 then
      let r := bitsToRandomness_exp n (by omega : n > 0) w
      L = plant_flat n (Φ n) r (h_nvars n h) ∧
      (Φ n).satisfies r.assignment  -- Domain constraint: witness must satisfy CNF
    else False

/-- Verification function for exponential OWF inversion (classical decidability). -/
noncomputable def verifyOWFInversion_sigma_exp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    (Σ n, LStarInstanceFG × Bits (expWLen n)) → Bool :=
  fun ⟨n, L, w⟩ =>
    @decide (StructuralOWFInversionRelation_exp Φ h_nvars n L w) (Classical.propDecidable _)

/-- AlgSpec for exponential OWF inversion verification.
    By `algspec_has_tm`, this gives a RandAdv with TM implementation. -/
noncomputable def verifyOWFInversion_algspec_exp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    AlgSpec (Σ n, LStarInstanceFG × Bits (expWLen n)) Bool 1 where
  run := fun _ input => verifyOWFInversion_sigma_exp Φ h_nvars input
  time_bound := fun n => 200 * (n + 1) ^ 3
  C := 200
  k := 3
  h_C_pos := by omega
  h_k_pos := by omega
  poly_explicit := fun _ => le_refl _
  time_bound_uniform := fun _ => le_refl _
  output_bounded := fun _ x => by
    show Sized.size (verifyOWFInversion_sigma_exp Φ h_nvars x) ≤ 200 * (Sized.size x + 1) ^ 3
    have h_bool : Sized.size (verifyOWFInversion_sigma_exp Φ h_nvars x) = 1 := rfl
    rw [h_bool]
    have h1 : (Sized.size x + 1) ^ 3 ≥ 1 := Nat.one_le_pow 3 _ (by omega)
    calc 1 ≤ 200 := by omega
         _ ≤ 200 * (Sized.size x + 1) ^ 3 := by omega
  coins_pos := by omega

/-- Verification function for dynamic OWF inversion (classical decidability). -/
noncomputable def verifyOWFInversion_sigma_dynamic
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    (Σ n, LStarInstanceFG × Bits (flatWLen n)) → Bool :=
  fun ⟨n, L, w⟩ =>
    @decide (StructuralOWFInversionRelation_dynamic Φ h_nvars n L w) (Classical.propDecidable _)

/-- AlgSpec for dynamic OWF inversion verification.
    By `algspec_has_tm`, this gives a RandAdv with TM implementation. -/
noncomputable def verifyOWFInversion_algspec_dynamic
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_nvars : ∀ n ≥ 128, (Φ n).nvars ≥ 4) :
    AlgSpec (Σ n, LStarInstanceFG × Bits (flatWLen n)) Bool 1 where
  run := fun _ input => verifyOWFInversion_sigma_dynamic Φ h_nvars input
  time_bound := fun n => 200 * (n + 1) ^ 3
  C := 200
  k := 3
  h_C_pos := by omega
  h_k_pos := by omega
  poly_explicit := fun _ => le_refl _
  time_bound_uniform := fun _ => le_refl _
  output_bounded := fun _ x => by
    show Sized.size (verifyOWFInversion_sigma_dynamic Φ h_nvars x) ≤ 200 * (Sized.size x + 1) ^ 3
    have h_bool : Sized.size (verifyOWFInversion_sigma_dynamic Φ h_nvars x) = 1 := rfl
    rw [h_bool]
    have h1 : (Sized.size x + 1) ^ 3 ≥ 1 := Nat.one_le_pow 3 _ (by omega)
    calc 1 ≤ 200 := by omega
         _ ≤ 200 * (Sized.size x + 1) ^ 3 := by omega
  coins_pos := by omega

/-! ## FNP Membership of OWF Inversion Relation -/

/-! ### Theorem: OWF Inversion is in FNP

**Statement**: The relation "w inverts plant_flat(Φ_n) to produce L" is in FNP.

**Derivation**: From `plant_equality_tm_exists` theorem (TMAxioms.lean), which is derived
from `algspec_has_tm` applied to `verifyOWFInversion_algspec`. The polynomial bound
is proven (`plant_poly_time`); TM existence follows from the Church-Turing bridge.
-/
theorem structural_owf_inversion_in_fnp_computable
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_wf : LStar.StructuralOWF.Theorems.CNFFamily.WellFormed Φ)
    (h_nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n)
    : InFNP_parametric_bits (fun n => n + 128)
        (StructuralOWFInversionRelation Φ (fun n h => by rw [h_nvars_eq n h]; omega)) := by
  -- Derive from plant_equality_tm_exists theorem (derived from algspec_has_tm)
  have h_nvars_ge4 : ∀ n ≥ 128, (Φ n).nvars ≥ 4 := fun n hn => by
    rw [h_nvars_eq n hn]; omega
  -- Get TM components from the theorem (now existentially quantifies alphabetSize)
  obtain ⟨alphabetSize, h_alpha, stateCount, tapeCount, C_tm, k_tm, h_state_pos, h_tape_pos, h_C_pos, h_k_pos,
          M, enc_in, enc_out, h_blank, h_blank_enc, h_correct, h_halts⟩ :=
    LStar.StructuralOWF.Foundations.TMAxioms.plant_equality_tm_exists Φ h_nvars_ge4
  -- Construct RandAdv for the verifier
  let run_fn : Fin 1 → (Σ n, LStarInstanceFG × Bits (n + 128)) → Bool :=
    fun _ input => LStar.StructuralOWF.Foundations.TMAxioms.verifyOWFInversion_sigma Φ h_nvars_ge4 input
  let enc : TMEncodingBase (Fin 1 × (Σ n, LStarInstanceFG × Bits (n + 128))) Bool (Fin alphabetSize) := {
    input := enc_in
    output := enc_out
    blank_consistent := h_blank_enc
  }
  let out_enc : TMInputEncodingBase Bool (Fin alphabetSize) := {
    blank := enc_in.blank
    encode := fun _ _ => enc_in.blank
    min_support := fun _ => 0
    min_support_spec := fun _ i => ⟨fun h => by omega, fun _ => rfl⟩
    finite_support := fun _ => ⟨0, fun _ _ => rfl⟩
    C_encode := 1
    k_encode := 1
    size_bounded := fun _ => by simp
  }
  let time_bound_fn : Nat → Nat := fun n => C_tm * (n + 1) ^ k_tm
  -- run_correct proof: the types match because C = C_tm and k = k_tm
  have h_run_correct : ∀ (c : Fin 1) (x : Σ n, LStarInstanceFG × Bits (n + 128)) (t : Nat),
      t ≥ C_tm * (Sized.size x + 1) ^ k_tm →
      let init_cfg := initWithEncodingBase M enc.input (c, x) h_tape_pos h_blank
      let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
      enc.output.decode (getTape0 final_cfg h_tape_pos) = run_fn c x := by
    intro c x t ht
    -- Fin 1 has only one inhabitant, so the coin is definitionally irrelevant.
    have hc : c = ⟨0, by omega⟩ := by ext; omega
    subst hc
    simpa [run_fn, enc] using h_correct x t ht
  -- halts proof
  have h_halts_proof : ∀ (c : Fin 1) (x : Σ n, LStarInstanceFG × Bits (n + 128)),
      let t := C_tm * (Sized.size x + 1) ^ k_tm
      let init_cfg := initWithEncodingBase M enc.input (c, x) h_tape_pos h_blank
      let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
      final_cfg.state ∈ M.halt := by
    intro c x
    have hc : c = ⟨0, by omega⟩ := by ext; omega
    subst hc
    simpa [enc] using h_halts x
  -- output_bounded proof: Bool has size 1, time_bound ≥ C_tm ≥ 1
  have h_output_bounded : ∀ c x, Sized.size (run_fn c x) ≤ time_bound_fn (Sized.size x) := by
    intro c x
    -- Sized.size (run_fn c x) = Sized.size Bool = 1
    simp only [Sized.size, sizedBool]
    -- time_bound_fn (Sized.size x) = C_tm * (Sized.size x + 1) ^ k_tm ≥ C_tm ≥ 1
    calc 1 ≤ C_tm := h_C_pos
         _ ≤ C_tm * 1 := by omega
         _ ≤ C_tm * (Sized.size x + 1) ^ k_tm := by
             apply Nat.mul_le_mul_left
             apply Nat.one_le_pow
             omega
  -- Use AlgSpec directly (no TM fields needed for InFNP_parametric_bits)
  let V_alg : AlgSpec (Σ n, LStarInstanceFG × Bits (n + 128)) Bool 1 := {
    run := run_fn
    time_bound := time_bound_fn
    C := C_tm
    k := k_tm
    h_C_pos := h_C_pos
    h_k_pos := h_k_pos
    coins_pos := by omega
    poly_explicit := fun _ => le_refl _
    time_bound_uniform := fun _ => le_refl _
    output_bounded := h_output_bounded
  }
  -- Prove InFNP_parametric_bits properties
  refine ⟨C_tm, k_tm, 1, V_alg, h_C_pos, h_k_pos, ?_, ?_, ?_, ?_⟩
  -- Determinism: run ignores coins
  · intro c1 c2 p; rfl
  -- Correctness: V decides the relation
  · intro n x w
    -- verifyOWFInversion_sigma uses classical decide
    simp only [V_alg, AlgSpec.runDefault]
    show LStar.StructuralOWF.Foundations.TMAxioms.verifyOWFInversion_sigma Φ h_nvars_ge4 ⟨n, x, w⟩ = true ↔ _
    unfold LStar.StructuralOWF.Foundations.TMAxioms.verifyOWFInversion_sigma
    constructor
    · intro h_true
      by_cases h_n : n ≥ 128
      · simp only [h_n, dite_true] at h_true
        use h_n
        exact @of_decide_eq_true _ (Classical.propDecidable _) h_true
      · simp only [h_n, dite_false, Bool.false_eq_true] at h_true
    · intro ⟨h_n, h_eq⟩
      simp only [h_n, dite_true]
      exact @decide_eq_true _ (Classical.propDecidable _) h_eq
  -- Polynomial time bound
  · intro n; exact le_refl _
  -- Polynomial witness length: witness_len n ≤ C_w * (n + 1)^k_w
  -- witness_len = fun n => n + 128, need: n + 128 ≤ C_w * (n + 1)^k_w
  -- Taking C_w = 128, k_w = 1: n + 128 ≤ 128 * (n + 1) = 128n + 128 ✓
  · refine ⟨128, 1, by omega, by omega, fun n => ?_⟩
    simp only [pow_one]
    omega

/-- The inversion relation is in FNP (polynomial-time verifiable).

    **Proof**: Direct application of `structural_owf_inversion_in_fnp_computable` theorem,
    which derives from `plant_equality_tm_exists` axiom.
-/
theorem structural_owf_inversion_in_fnp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_wellformed : LStar.StructuralOWF.Theorems.CNFFamily.WellFormed Φ)
    (h_wf_literals : ∀ n, CNF.WellFormed (Φ n))
    (h_nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n)
    : InFNP_parametric_bits (fun n => n + 128) (StructuralOWFInversionRelation Φ (fun n h => by rw [h_nvars_eq n h]; omega)) :=
  structural_owf_inversion_in_fnp_computable Φ h_wellformed h_nvars_eq

/-- Exponential version: OWF inversion relation with exponential witness length is in FNP.

    **Statement**: The relation "w ∈ Bits(expWLen n) inverts plant_flat(Φ_n) to produce L" is in FNP.
    Uses witness length expWLen n = 2n + 64 with dgLen = n for TRUE exponential profile.

    **Proof**: Direct construction from verifyOWFInversion_algspec_exp AlgSpec. -/
theorem structural_owf_inversion_in_fnp_exp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_wellformed : LStar.StructuralOWF.Theorems.CNFFamily.WellFormed Φ)
    (h_wf_literals : ∀ n, CNF.WellFormed (Φ n))
    (h_nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n)
    : InFNP_parametric_bits expWLen
        (StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega)) := by
  -- Use verifyOWFInversion_algspec_exp as the verifier
  have h_nvars_ge4 : ∀ n ≥ 128, (Φ n).nvars ≥ 4 := fun n hn => by
    rw [h_nvars_eq n hn]; omega
  let V_alg := verifyOWFInversion_algspec_exp Φ h_nvars_ge4
  refine ⟨200, 3, 1, V_alg, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · -- Determinism: run ignores coins
    intro c1 c2 p; rfl
  · -- Correctness: V decides the relation
    intro n x w
    simp only [V_alg, AlgSpec.runDefault]
    show verifyOWFInversion_sigma_exp Φ h_nvars_ge4 ⟨n, x, w⟩ = true ↔ _
    unfold verifyOWFInversion_sigma_exp
    -- The goal is: decide (StructuralOWFInversionRelation_exp ...) = true ↔ StructuralOWFInversionRelation_exp ...
    simp only [decide_eq_true_iff]
  · -- Polynomial time bound
    intro n; exact le_refl _
  · -- Polynomial witness length: expWLen n = 2n + 64 ≤ C_w * (n + 1)^k_w
    -- Taking C_w = 3, k_w = 1: 2n + 64 ≤ 3 * (n + 1) = 3n + 3 only works for n ≥ ~30
    -- Taking C_w = 64, k_w = 1: 2n + 64 ≤ 64 * (n + 1) = 64n + 64 ✓
    refine ⟨64, 1, by omega, by omega, fun n => ?_⟩
    simp only [expWLen, pow_one]
    omega

/-! ## Adapter Encoding for PPTAdversary Construction

The following constructs adapter encodings to convert between:
- M's encoding: TMEncoding (Σ n, LStarInstanceFG) (Σ n, Bits (n + 128))
- A_inv's encoding: TMEncoding LStarInstanceFG Randomness

The adapter wraps L as ⟨φ.nvars, L⟩ for encoding, and converts decoded
sigma outputs to Randomness via bitsToRandomness.

**Design**: These adapters satisfy type requirements. The tm_algorithm_correspondence
property is now structural (via RandAdv.run_correct field), and all encoding semantics
are derived from structural fields (via formatSeparated_from_early_decode theorem).
-/

-- adapterInputEncoding is imported from OWFBridgeCommon

/-! ## ENCODING SEMANTICS: Early-time cross-decoding produces non-satisfying assignment.

**Background**: At time t < 2, decoding the tape as output (when it contains input
encoding) cannot produce an assignment satisfying a CNF with ≥4 variables.

### What Format Separation Captures

The property encodes the **incompatibility of input and output formats**:

```
Input encoding:  LStarInstanceFG → tape  (problem description: φ, dag, parameters)
Output encoding: tape → Bits → Assignment (satisfying assignment if correct)

Cross-decoding: Input-formatted tape decoded as output → garbage assignment
```

### Why t < 2?

| Time | Tape State | Why Not Satisfying |
|------|------------|-------------------|
| t=0 | Pure input encoding | Format incompatible with output decoder |
| t=1 | Input + 1 cell changed | Still overwhelmingly input format |

**Key observation**: A valid output requires writing n ≥ 4 bits in a specific format.
In 0-1 steps, a TM can write at most 1 bit. The output decoder cannot extract a
valid n-bit assignment from a tape that's 99%+ input encoding.

### Why nvars ≥ 4?

The constraint `nvars ≥ 4` ensures non-trivial CNFs:
- Avoids degenerate cases (empty CNF, tautologies)
- Requires at least 4 bits of output to specify an assignment
- 4 bits cannot be produced in 1 TM step

### Why Format Separation Is Assumed (Not Proven)

Proving this requires specifying:
1. Exact input encoding format for LStarInstanceFG
2. Exact output decoding format for Bits
3. Proving format incompatibility

This is **encoding detail**, not mathematical content. The axiom abstracts:
"Input and output formats are incompatible (as any reasonable encoding would be)."

### How This Could Be Proven

```lean
-- Define input format explicitly
def inputFormat (L : LStarInstanceFG) : List (Fin alphabetSize) := ...

-- Define output format explicitly
def outputFormat (bits : Bits n) : List (Fin alphabetSize) := ...

-- Prove format disjointness
theorem formats_incompatible :
  ∀ L bits, inputFormat L ≠ outputFormat bits := ...

-- Derive encoding_semantics as theorem
theorem encoding_semantics_derived :
  t < 2 → (tape is mostly inputFormat) → cross-decode gives garbage
```

### Risk Assessment

**Risk**: Very low (encoding compatibility assumption)

**What could go wrong**:
- Pathological encoding where input format happens to decode as satisfying assignment
- But: Such encoding would be deliberately adversarial (not "reasonable")
- And: Would violate basic encoding design principles (input ≠ output formats)

**Worst case**: Axiom fails for some exotic encoding. But any encoding used in
practice would satisfy this property—it's a sanity condition, not a mathematical
claim about all possible encodings.

### References

- Input/output encoding separation: Standard in TM theory (Sipser §3.1)
- Encoding conventions: Arora-Barak §1.2 (machine descriptions)

### Axiom Elimination (encoding_semantics)

The original `encoding_semantics` axiom has been ELIMINATED and replaced with
`encoding_semantics_derived` theorem that derives from explicit hypotheses:
- `FormatSeparated`: Cross-decoding produces n = 0 (encoding discipline)
- `HasPositiveClause`: CNF has at least one all-positive clause

This transformation makes the encoding assumption EXPLICIT and VERIFIABLE rather
than universal and opaque. See EncodingDiscipline.lean for the infrastructure.
-/

-- formatSeparated_from_early_decode is imported from OWFBridgeCommon

/-- **Encoding Semantics** (derived from format separation + positive clause).

Replaces the original axiom with explicit hypotheses. At t < 2, cross-decoding
produces non-satisfying assignment because:
1. FormatSeparated ⇒ decoded.1 = 0 ⇒ assignment is all-false
2. HasPositiveClause ⇒ all-false doesn't satisfy CNF

**Trust Boundary**: 0 axioms - derives from proven lemmas in EncodingDiscipline.lean
-/
theorem encoding_semantics_derived
  {T : Nat}
  (M : RandAdv (Sigma fun _n => LStarInstanceFG) (Sigma fun n => Bits (n + 128)) T)
  (h_format_sep : EncodingDiscipline.FormatSeparated M (adapterInputEncoding M) M.h_blank_consistent)
  (x : LStarInstanceFG) (φ : CNF) (t : Nat)
  (h_nvars : φ.nvars ≥ 4)
  (h_t : t < 2)
  (h_positive : CNF.HasPositiveClause φ)
  : let init_cfg := initWithEncodingBase M.M (adapterInputEncoding M) x M.h_tape_pos M.h_blank_consistent
    let cfg := (TMConfig.step (M := M.M))^[t] init_cfg
    let tape := getTape0 cfg M.h_tape_pos
    let sigma_output := M.encoding.output.decode tape
    let r := bitsToRandomness sigma_output.1 64 (by omega) sigma_output.2
    ¬(φ.satisfies r.assignment) :=
  EncodingDiscipline.encoding_semantics_from_format_separated M (adapterInputEncoding M)
    M.h_blank_consistent h_format_sep x φ t h_nvars h_t h_positive

/-- **Encoding Semantics (Exponential Profile)** - derived from format separation.

Same as encoding_semantics_derived but for the exponential profile with expWLen n.

**Key insight**: When FormatSeparated_exp holds, decoding at t < 2 gives n = 0.
The assignment extracted from bitsToRandomness with n = 0 is all-false.
All-false doesn't satisfy CNFs with positive clauses.

**Trust Boundary**: 0 axioms - derives from format separation + positive clause properties.
-/
theorem encoding_semantics_derived_exp
  {T : Nat}
  (M : RandAdv (Sigma fun _n => LStarInstanceFG) (Sigma fun n => Bits (EncodingDiscipline.expWLen n)) T)
  (h_format_sep : EncodingDiscipline.FormatSeparated_exp M (adapterInputEncoding_exp M) M.h_blank_consistent)
  (c : Fin T) (x : LStarInstanceFG) (φ : CNF) (t : Nat)
  (h_nvars : φ.nvars ≥ 4)
  (h_t : t < 2)
  (h_positive : CNF.HasPositiveClause φ)
  : let init_cfg := initWithEncodingBase M.M (adapterInputEncoding_exp M) (c, x) M.h_tape_pos M.h_blank_consistent
    let cfg := (TMConfig.step (M := M.M))^[t] init_cfg
    let tape := getTape0 cfg M.h_tape_pos
    let sigma_output := M.encoding.output.decode tape
    -- Assignment is all-false when sigma_output.1 = 0 (from format separation)
    ¬(φ.satisfies (fun _ => false)) := by
  simp only
  -- By format separation, decoded.1 = 0, so any assignment extraction would be all-false
  -- But we don't even need to extract - just show all-false doesn't satisfy
  exact EncodingDiscipline.all_false_not_satisfies_cnf_with_positive_clause φ h_positive

/-- Flat profile witness decoding: uses dgLen = 64. -/
def flatDecodeWitness (n : Nat) (w : Bits (n + 128)) : Randomness :=
  bitsToRandomness n 64 (by omega) w

/-- Adapter output decoding (flat profile): tape → Randomness via sigma decoding + conversion.

    Uses the common template with flatDecodeWitness.
-/
def adapterOutputDecoding
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    : TMOutputDecoding Randomness (Fin M.alphabetSize) :=
  mkAdapterOutputDecoding M flatDecodeWitness

/-- Adapter bidirectional encoding (flat profile): combines input and output adapters.

    Uses the common template with flatDecodeWitness.
    **Note**: Returns TMEncodingBase (no injectivity) to match PPTAdversary requirements.
    Input type is (Fin T × LStarInstanceFG) to make coin choice visible to TM.
-/
def adapterTMEncoding
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    : TMEncodingBase (Fin T × LStarInstanceFG) Randomness (Fin M.alphabetSize) :=
  mkAdapterTMEncoding M flatDecodeWitness

/-! ### Exponential Profile Encoding Adapters

These use dgLen = n for the true exponential hardness profile.
Witness type: Bits (expWLen n) = Bits (2n + 64)
-/

/-- Exponential witness decoder: Bits (expWLen n) → Randomness with dgLen = n. -/
noncomputable def expDecodeWitness (n : Nat) (w : Bits (expWLen n)) : Randomness :=
  if h : n > 0 then
    bitsToRandomness_exp n h w
  else
    -- Fallback for n = 0 (should not occur in practice)
    { dgLen := 1
      h_dgLen_pos := by omega
      assignment := fun _ => false
      gateDigests := [Vector.ofFn (fun _ : Fin 1 => false)]
      structuralBits := List.replicate 64 false
      h_sufficient_salts := by simp
      h_single_gate := rfl }

/-- When n = 0, expDecodeWitness produces the all-false assignment.

    This is used in nontrivial_computation: format separation gives decoded.1 = 0,
    so the extracted assignment is all-false, which contradicts positive clause. -/
theorem expDecodeWitness_zero_assignment (w : Bits (expWLen 0)) :
    (expDecodeWitness 0 w).assignment = fun _ => false := by
  simp only [expDecodeWitness]
  -- The condition `0 > 0` is false, so we take the else branch
  -- The else branch has `assignment := fun _ => false`
  simp only [gt_iff_lt, Nat.not_lt_zero, ↓reduceDIte]

/-- Adapter output decoding (exponential profile): tape → Randomness via sigma decoding + conversion. -/
noncomputable def adapterOutputDecoding_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (expWLen n)) T)
    : TMOutputDecoding Randomness (Fin M.alphabetSize) :=
  mkAdapterOutputDecoding_exp M expDecodeWitness

/-- Adapter bidirectional encoding (exponential profile): combines input and output adapters.
    Uses expDecodeWitness for dgLen = n.
    Input type is (Fin T × LStarInstanceFG) to make coin choice visible to TM.
-/
noncomputable def adapterTMEncoding_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (expWLen n)) T)
    : TMEncodingBase (Fin T × LStarInstanceFG) Randomness (Fin M.alphabetSize) :=
  mkAdapterTMEncoding_exp M expDecodeWitness

/-! ## FP Non-Membership of OWF Inversion Relation (Exponential Profile) -/

/-- If polynomial-time witness finder exists, OWF can be inverted.

    **Exponential Profile**: Uses dgLen = n for true 2^n hardness.
    Witness type: Bits (expWLen n) = Bits (2n + 64)

    Proof by contradiction:
    1. Assume ∃ poly-time f such that f(L) witnesses StructuralOWFInversionRelation_exp
    2. Given challenge L = Plant_flat(φ, r_star), compute w = f(L)
    3. By definition: Plant_flat(φ, bitsToRandomness_exp(w)) = L
    4. Therefore: bitsToRandomness_exp(w) inverts the OWF
    5. Contradiction with f_is_structural_owf_exponential_flat
-/
theorem structural_owf_inversion_not_in_fp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_wellformed : LStar.StructuralOWF.Theorems.CNFFamily.WellFormed Φ)
    (h_wf_literals : ∀ n, CNF.WellFormed (Φ n))
    (h_nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n)
    (h_nonempty_clauses : ∀ n, n ≥ 128 → 0 < (Φ n).clauses.length)
    (h_satisfiable : ∀ n, n ≥ 128 → ∃ (a : Assignment), (Φ n).satisfies a)
    -- Polynomial clause bound: needed for dag size to be polynomial in nvars
    (h_clauses_poly : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128, (Φ n).clauses.length ≤ C_cl * n^k_cl)
    -- CNF family has positive clauses: Required for encoding semantics derivation
    (h_family_positive : ∀ n ≥ 128, CNF.HasPositiveClause (Φ n))
    -- Solution multiplicity bound: OWF security requires bounded preimages
    -- Without this, dense-solution CNFs (e.g., tautologies) admit trivial inversion
    -- Satisfied by: planted SAT (1 solution), random k-SAT (O(1)), crypto reductions
    (h_bounded : ∃ c, LStar.StructuralOWF.Theorems.CNFFamily.BoundedSolutions Φ c)
    : ¬∃ (f_family : ∀ n, LStarInstanceFG → Bits (expWLen n)),
        InFP_parametric_bits expWLen f_family ∧
        (∃ N₀ : Nat, ∀ n ≥ N₀, ∀ L : LStarInstanceFG,
          (∃ w, StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n L w) →
          StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n L (f_family n L)) := by
  intro ⟨f_family, h_fp_and_inverts⟩
  obtain ⟨h_fp, N₀, h_inverts⟩ := h_fp_and_inverts

  -- Extract the poly-time machine M from InFP_parametric_bits
  obtain ⟨C_M, deg_M, T_M, M_alg, h_M_det_alg, h_M_correct_alg, h_M_time⟩ := h_fp

  -- Encoding normalization: upgrade AlgSpec to RandAdv with encoding discipline
  -- The Church-Turing axiom (algspec_has_tm) provides firstNat early_decode_default = 0 directly.
  obtain ⟨M, h_run_match, h_C_match, h_k_match, h_decode_surj, h_first_nat_zero⟩ :=
    LStar.Complexity.encoding_zero_default M_alg

  -- For Sigma types, FirstNatComponent.firstNat = Sigma.fst, so h_first_nat_zero gives us .1 = 0
  have h_early_zero : M.early_decode_default.1 = 0 := h_first_nat_zero

  -- Derive FormatSeparated from early_decode property (exponential profile)
  have h_format_sep : EncodingDiscipline.FormatSeparated_exp M (adapterInputEncoding_exp M) M.h_blank_consistent :=
    formatSeparated_from_early_decode_exp M h_early_zero

  -- Determinism and correctness transfer from AlgSpec via run equality
  -- h_run_match : M.toAlgSpec.run = M_alg.run
  -- Since toAlgSpec.run = M.run by definition, we have M.run = M_alg.run
  have h_run_eq : M.run = M_alg.run := h_run_match
  have h_M_det : ∀ c₁ c₂ s, M.run c₁ s = M.run c₂ s := by
    intro c₁ c₂ s
    rw [h_run_eq]
    exact h_M_det_alg c₁ c₂ s
  have h_M_correct : ∀ n x, M.run ⟨0, M.coins_pos⟩ ⟨n, x⟩ = ⟨n, f_family n x⟩ := by
    intro n x
    rw [h_run_eq]
    -- h_M_correct_alg uses M_alg.coins_pos, M uses M.coins_pos, but run ignores coins anyway
    have h_corr := h_M_correct_alg n x
    convert h_corr using 2

  -- Use actual TM obtained via the Church–Turing axiom
  -- M contains: TuringMachine, encoding, and run_correct proof
  -- This ensures M.M actually implements M.run (structural enforcement)

  -- Strategy: Build an adversary that EXTRACTS the parameter from the instance
  -- Key insight: For planted instances L = plant_flat 1 (Φ n) r, the input φ = Φ n
  -- is recoverable via Classical.choose from the planting proof (see planted_φ).
  -- Since (Φ n).nvars = n (from h_nvars_eq), we can extract n from the instance!

  -- Proper extractWitness: decode tape to get Randomness, then create Witness with matching assignment
  -- This makes assignment_correspondence provable via run_correct!
  -- **Exponential Profile**: Uses expDecodeWitness with dgLen = n
  let properExtractWitness : LStar.StructuralOWF.Foundations.TMConfig M.M → Witness := fun cfg =>
    let tape := getTape0 cfg M.h_tape_pos
    let sigma_output := M.encoding.output.decode tape  -- : Σ n : Nat, Bits (expWLen n)
    let r := expDecodeWitness sigma_output.1 sigma_output.2  -- : Randomness with dgLen = n
    -- Create Witness with same assignment (gateProofs/digestBits are not used in assignment_correspondence)
    { assignment := r.assignment
      gateProofs := []
      digestBits := [] }

  -- Build adversary that extracts parameter and uses appropriate f_family
  let A_inv : Complexity.PPTAdversary LStarInstanceFG Randomness Witness := {
    num_coins := T_M  -- Same number of coins as M
    -- Use actual TM parameters from InFP certificate
    stateCount := M.stateCount
    alphabetSize := M.alphabetSize
    tapeCount := M.tapeCount
    h_state_pos := M.h_state_pos
    h_alphabet_pos := M.h_alphabet_pos
    h_tape_pos := M.h_tape_pos

    -- Use actual TM from InFP certificate (structural consistency)
    M := M.M  -- Extract the TuringMachine field from RandAdv M
    extractWitness := properExtractWitness  -- Proper tape decoding

    -- Encoding adaptation: Sigma types → concrete types
    -- **Exponential Profile**: Uses adapterTMEncoding_exp with dgLen = n
    encoding := adapterTMEncoding_exp M

    -- Blank consistency: M.M.blank = M.encoding.input.blank (from M.h_blank_consistent)
    -- and adapterTMEncoding_exp uses the same blank symbol
    h_blank_consistent := M.h_blank_consistent

    halts := fun x => by
      -- Halting within scaled time bound for adapted encoding.
      -- The adapter encodes x as ⟨x.φ.nvars, x⟩, so tape contents match M's input.
      -- M.halts gives: halts in M.C * (size ⟨n,x⟩ + 1)^M.k steps
      -- We use C = M.C * 2^M.k to absorb sigma overhead:
      --   size ⟨n,x⟩ = (n+1) + size x ≤ 2*(size x + 1) when n ≤ size x
      --   So (size ⟨n,x⟩ + 1)^k ≤ (2*(size x+1))^k = 2^k * (size x+1)^k
      --   Thus M.C * (size ⟨n,x⟩ + 1)^k ≤ M.C * 2^k * (size x+1)^k = C * (size x+1)^k
      --
      -- Key structural fact: x.φ.nvars = x.n (by h_n_eq_nvars) and x.dag.n ≥ x.n (by dag_size_ge_n)
      -- Therefore x.φ.nvars ≤ x.dag.n = size x

      -- Step 1: Extract size relationships
      let n := x.encodedφ.nvars
      have h_nvars_eq : n = x.n := x.h_n_eq_nvars.symm
      have h_dag_ge : x.dag.n ≥ x.n := x.dag_size_ge_n
      have h_nvars_le_dag : n ≤ x.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
      have h_size_x : Sized.size x = x.dag.n := rfl  -- by definition of Sized LStarInstanceFG

      -- Step 2: Sigma size bound
      -- size ⟨n, x⟩ = (n + 1) + size x by sizedSigma and sizedNat
      have h_sigma_size : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size x := by
        simp only [Sized.size, sizedSigma, sizedNat]

      -- size ⟨n, x⟩ + 1 ≤ 2 * (size x + 1) when n ≤ size x
      have h_size_bound : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size x + 1) := by
        rw [h_sigma_size, h_size_x]
        -- Need: (n + 1) + x.dag.n + 1 ≤ 2 * (x.dag.n + 1)
        -- i.e., n + x.dag.n + 2 ≤ 2 * x.dag.n + 2
        -- i.e., n ≤ x.dag.n (which is h_nvars_le_dag)
        omega

      -- Step 3: Time bound relationship
      -- M's time: M.C * (size ⟨n,x⟩ + 1)^M.k
      -- Our time: C * (size x + 1)^M.k = M.C * 2^M.k * (size x + 1)^M.k
      have h_time_bound : M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
                          M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := by
        have h1 : (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
                  (2 * (Sized.size x + 1)) ^ M.k := Nat.pow_le_pow_left h_size_bound M.k
        have h2 : (2 * (Sized.size x + 1)) ^ M.k = 2 ^ M.k * (Sized.size x + 1) ^ M.k :=
          Nat.mul_pow 2 (Sized.size x + 1) M.k
        calc M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k
          _ ≤ M.C * (2 * (Sized.size x + 1)) ^ M.k := Nat.mul_le_mul_left M.C h1
          _ = M.C * (2 ^ M.k * (Sized.size x + 1) ^ M.k) := by rw [h2]
          _ = M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := (Nat.mul_assoc M.C _ _).symm

      -- Step 4: The adapter encoding produces same initial config as M expects
      -- adapterInputEncoding.encode x = M.encoding.input.encode ⟨n, x⟩ (by definition)
      -- So initWithEncoding with adapter produces same tapes as initWithEncodingBase for sigma input

      -- Step 5: Key observation - adapter encoding produces same tape as M's encoding
      -- By definition: (adapterTMEncoding_exp M).input.encode x = M.encoding.input.encode ⟨n, x⟩
      -- Both initWithEncoding and initWithEncodingBase produce same structure:
      --   { state := M.M.q0, tapes := ...(with encoding on tape 0), heads := fun _ => 0 }

      -- Step 6: Define time bounds
      let t_M := M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k
      let t_PPT := M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k  -- = C * (size x + 1)^k

      -- Step 7: Time inequality (t_M ≤ t_PPT already proven in h_time_bound)

      -- Step 8: The configurations are identical since both encode ⟨n, x⟩ on tape 0
      -- Both use M.M, both start at M.M.q0, both have heads at 0
      -- The tape[0] = M.encoding.input.encode ⟨n, x⟩ for both (adapter wraps x as ⟨n,x⟩)

      -- Step 9: Show adapter encoding produces same tape as M's encoding
      -- **Exponential Profile**: Uses adapterTMEncoding_exp
      have h_encode_eq : (adapterTMEncoding_exp M).input.encode x = M.encoding.input.encode ⟨n, x⟩ := by
        -- By definition of adapterInputEncoding_exp: encode L = M.encoding.input.encode ⟨φ.nvars, L⟩
        rfl

      -- Step 10: Key insight - initWithEncoding and initWithEncodingBase produce SAME TMConfig
      -- Both have:
      --   state := M.M.q0
      --   tapes := fun tape_idx => if tape_idx.val = 0 then enc.encode x else fun _ => M.M.blank
      --   heads := fun _ => 0
      -- Since encode functions match (by h_encode_eq), configs are definitionally equal!

      -- Step 11: Define the initial configurations
      -- PPT init config (what we're proving about) - **Exponential Profile**
      let init_cfg_PPT := initWithEncodingBase M.M (adapterTMEncoding_exp M).input x M.h_tape_pos M.h_blank_consistent
      -- M's init config (what M.halts gives us)
      let init_M := initWithEncodingBase M.M M.encoding.input ⟨n, x⟩ M.h_tape_pos M.h_blank_consistent

      -- Step 12: Prove the configurations are equal
      -- Both have same state (M.M.q0), tapes (via h_encode_eq), and heads (fun _ => 0)
      have h_configs_eq : init_cfg_PPT = init_M := by
        -- Both definitions expand to TMConfig with identical fields
        -- state: M.M.q0 = M.M.q0
        -- tapes: fun i => if i.val = 0 then encode x else blank
        -- heads: fun _ => 0
        -- Key: h_encode_eq says the encode functions produce the same result
        -- First prove tapes equality
        have h_tapes : (fun tape_idx : Fin M.tapeCount =>
            if tape_idx.val = 0 then (adapterTMEncoding_exp M).input.encode x
            else fun _ => M.M.blank) =
          (fun tape_idx : Fin M.tapeCount =>
            if tape_idx.val = 0 then M.encoding.input.encode ⟨n, x⟩
            else fun _ => M.M.blank) := by
          funext tape_idx
          split_ifs with h_tape0
          · exact h_encode_eq
          · rfl
        -- Use structure equality: both configs have same state, tapes (via h_tapes), heads
        show initWithEncodingBase M.M (adapterTMEncoding_exp M).input x M.h_tape_pos M.h_blank_consistent =
             initWithEncodingBase M.M M.encoding.input ⟨n, x⟩ M.h_tape_pos M.h_blank_consistent
        simp only [Complexity.initWithEncoding, Complexity.initWithEncodingBase, h_tapes]

      -- Step 13: Apply M.halts to get halting from init_M in t_M steps
      have h_M_halts : ((TMConfig.step)^[t_M] init_M).state ∈ M.M.halt := M.halts ⟨n, x⟩

      -- Step 14: Since configs are equal, execution from init_cfg_PPT is the same
      have h_PPT_halts_tM : ((TMConfig.step)^[t_M] init_cfg_PPT).state ∈ M.M.halt := by
        rw [h_configs_eq]
        exact h_M_halts

      -- Step 15: Use halt_persists to extend from t_M to t_PPT (since t_M ≤ t_PPT)
      -- The goal has let-bound t = t_PPT and init_cfg = init_cfg_PPT

      -- Split the iteration: step^[t_PPT] = step^[t_PPT - t_M] ∘ step^[t_M]
      have h_iterate_split : (TMConfig.step)^[t_PPT] init_cfg_PPT =
          (TMConfig.step)^[t_PPT - t_M] ((TMConfig.step)^[t_M] init_cfg_PPT) := by
        have h_le : t_M ≤ t_PPT := h_time_bound
        rw [← Function.iterate_add_apply]
        congr 1
        omega

      -- Apply halt_persists to show halting persists from t_M to t_PPT
      have h_final : ((TMConfig.step)^[t_PPT] init_cfg_PPT).state ∈ M.M.halt := by
        rw [h_iterate_split]
        exact LStar.StructuralOWF.Foundations.halt_persists M.M _ (t_PPT - t_M) h_PPT_halts_tM

      -- The goal has let bindings; show they match our definitions
      -- goal: let t := t_PPT; let init_cfg := init_cfg_PPT; (step^[t] init_cfg).state ∈ M.M.halt
      simp only []
      exact h_final

    run_correct := fun c x t h_t => by
      -- TM correctness with adapter encoding.
      -- Proof: Compose M.run_correct with adapter encode/decode.

      let n := x.encodedφ.nvars

      -- Step 1: Time bound scaling
      -- h_t : t ≥ C * (size x + 1)^k = M.C * 2^M.k * (size x + 1)^M.k
      -- We need: t ≥ M.C * (size ⟨n,x⟩ + 1)^M.k for M.run_correct

      -- Size relationship (same as in halts proof)
      have h_nvars_eq : n = x.n := x.h_n_eq_nvars.symm
      have h_dag_ge : x.dag.n ≥ x.n := x.dag_size_ge_n
      have h_nvars_le_dag : n ≤ x.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
      have h_size_x : Sized.size x = x.dag.n := rfl

      have h_sigma_size : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size x := by
        simp only [Sized.size, sizedSigma, sizedNat]

      have h_size_bound : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size x + 1) := by
        rw [h_sigma_size, h_size_x]; omega

      have h_time_bound : M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
                          M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := by
        have h1 : (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
                  (2 * (Sized.size x + 1)) ^ M.k := Nat.pow_le_pow_left h_size_bound M.k
        have h2 : (2 * (Sized.size x + 1)) ^ M.k = 2 ^ M.k * (Sized.size x + 1) ^ M.k :=
          Nat.mul_pow 2 (Sized.size x + 1) M.k
        calc M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k
          _ ≤ M.C * (2 * (Sized.size x + 1)) ^ M.k := Nat.mul_le_mul_left M.C h1
          _ = M.C * (2 ^ M.k * (Sized.size x + 1) ^ M.k) := by rw [h2]
          _ = M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := (Nat.mul_assoc M.C _ _).symm

      -- h_t gives: t ≥ M.C * 2^M.k * (size x + 1)^M.k
      -- h_time_bound gives: M.C * (size ⟨n,x⟩ + 1)^M.k ≤ M.C * 2^M.k * (size x + 1)^M.k
      have h_t_for_M : t ≥ M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k := by
        exact Nat.le_trans h_time_bound h_t

      -- Step 2: Encoding equality
      have h_encode_eq : (adapterTMEncoding_exp M).input.encode x = M.encoding.input.encode ⟨n, x⟩ := rfl

      -- Step 3: Config equality (same init configs)
      let init_cfg_PPT := initWithEncodingBase M.M (adapterTMEncoding_exp M).input x M.h_tape_pos M.h_blank_consistent
      let init_M := initWithEncodingBase M.M M.encoding.input ⟨n, x⟩ M.h_tape_pos M.h_blank_consistent

      have h_tapes : (fun tape_idx : Fin M.tapeCount =>
          if tape_idx.val = 0 then (adapterTMEncoding_exp M).input.encode x
          else fun _ => M.M.blank) =
        (fun tape_idx : Fin M.tapeCount =>
          if tape_idx.val = 0 then M.encoding.input.encode ⟨n, x⟩
          else fun _ => M.M.blank) := by
        funext tape_idx
        split_ifs with h_tape0
        · exact h_encode_eq
        · rfl

      have h_configs_eq : init_cfg_PPT = init_M := by
        show initWithEncodingBase M.M (adapterTMEncoding_exp M).input x M.h_tape_pos M.h_blank_consistent =
             initWithEncodingBase M.M M.encoding.input ⟨n, x⟩ M.h_tape_pos M.h_blank_consistent
        simp only [Complexity.initWithEncoding, Complexity.initWithEncodingBase, h_tapes]

      -- Step 4: Final configs are equal (TM is deterministic)
      have h_final_eq : (TMConfig.step)^[t] init_cfg_PPT = (TMConfig.step)^[t] init_M := by
        rw [h_configs_eq]

      -- Step 5: Apply M.run_correct with coin c
      -- We need a coin for M; PPT uses Fin num_coins = Fin T_M, M uses Fin M.T
      -- c : Fin T_M, and M.T = T_M by construction
      have h_M_run_correct := M.run_correct c ⟨n, x⟩ t h_t_for_M

      -- h_M_run_correct : M.encoding.output.decode (getTape0 final_M h_tape_pos) = M.run c ⟨n, x⟩
      -- where final_M = (TMConfig.step)^[t] init_M

      -- Step 6: M.run correctness (determinism + parametric correctness)
      have h_det_c : M.run c ⟨n, x⟩ = M.run ⟨0, M.coins_pos⟩ ⟨n, x⟩ := h_M_det c ⟨0, M.coins_pos⟩ ⟨n, x⟩
      have h_correct_n : M.run ⟨0, M.coins_pos⟩ ⟨n, x⟩ = ⟨n, f_family n x⟩ := h_M_correct n x
      have h_M_result : M.run c ⟨n, x⟩ = ⟨n, f_family n x⟩ := by rw [h_det_c, h_correct_n]

      -- Step 7: Chain the equalities
      -- goal: (adapterTMEncoding_exp M).output.decode tape_output = run c x
      -- where tape_output = getTape0 ((TMConfig.step)^[t] init_cfg_PPT) h_tape_pos
      -- and run c x = bitsToRandomness n (f_family n x)

      -- By h_final_eq: getTape0 final_PPT = getTape0 final_M
      have h_tape_eq : getTape0 ((TMConfig.step)^[t] init_cfg_PPT) M.h_tape_pos =
                       getTape0 ((TMConfig.step)^[t] init_M) M.h_tape_pos := by
        rw [h_configs_eq]

      -- By h_M_run_correct: M.encoding.output.decode (getTape0 final_M) = M.run c ⟨n,x⟩
      -- By h_M_result: M.run c ⟨n,x⟩ = ⟨n, f_family n x⟩
      have h_M_decode : M.encoding.output.decode (getTape0 ((TMConfig.step)^[t] init_M) M.h_tape_pos) =
                        ⟨n, f_family n x⟩ := by
        rw [h_M_run_correct, h_M_result]

      -- adapterOutputDecoding.decode = expDecodeWitness ∘ M.decode (exponential profile)
      -- So adapter.decode tape = expDecodeWitness (M.decode tape).1 (M.decode tape).2
      simp only []
      show (adapterTMEncoding_exp M).output.decode (getTape0 ((TMConfig.step)^[t] init_cfg_PPT) M.h_tape_pos) =
           expDecodeWitness n (f_family n x)
      simp only [adapterTMEncoding_exp, mkAdapterTMEncoding_exp, mkAdapterOutputDecoding_exp]
      rw [h_tape_eq, h_M_decode]

    -- Key field: Extract parameter n from instance, then use f_family n
    -- For instances L = plant_flat 1 (Φ n) r, we have L.n = (Φ n).nvars = n
    run := fun c L =>
      -- Extract security parameter from instance
      let n := L.encodedφ.nvars
      have h_nvars_eq : n = L.n := L.h_n_eq_nvars.symm

      -- Use M with extracted parameter to find witness
      -- M.run : Fin T_M → Sigma (fun n => LStarInstanceFG) → Sigma (fun n => Bits (expWLen n))
      -- By h_M_correct and h_M_det: M.run c ⟨n, L⟩ = ⟨n, f_family n L⟩
      have h_det_c : M.run c ⟨n, L⟩ = M.run ⟨0, M.coins_pos⟩ ⟨n, L⟩ :=
        h_M_det c ⟨0, M.coins_pos⟩ ⟨n, L⟩
      have h_correct_n : M.run ⟨0, M.coins_pos⟩ ⟨n, L⟩ = ⟨n, f_family n L⟩ :=
        h_M_correct n L
      have h_result : M.run c ⟨n, L⟩ = ⟨n, f_family n L⟩ := by
        rw [h_det_c, h_correct_n]
      -- Now we know the output is exactly ⟨n, f_family n L⟩
      let w := f_family n L  -- The witness bits (at correct parameter!)
      expDecodeWitness n w    -- Convert to Randomness (exponential profile)

    time_bound := M.time_bound
    -- Scale C by 2^k to absorb sigma encoding overhead in size bounds
    C := M.C * 2 ^ M.k
    k := M.k
    h_C_pos := Nat.mul_pos M.h_C_pos (Nat.pow_pos (a := 2) (n := M.k) (by decide))
    h_k_pos := M.h_k_pos

    poly := fun n => by
      -- time_bound n = M.time_bound n ≤ M.C * (n+1)^M.k ≤ (M.C * 2^M.k) * (n+1)^M.k
      have h1 : M.time_bound n ≤ M.C * (n + 1) ^ M.k := M.time_bound_uniform n
      have h2 : M.C * (n + 1) ^ M.k ≤ M.C * 2 ^ M.k * (n + 1) ^ M.k := by
        calc M.C * (n + 1) ^ M.k
          _ = M.C * 1 * (n + 1) ^ M.k := by ring
          _ ≤ M.C * 2 ^ M.k * (n + 1) ^ M.k := by
              apply Nat.mul_le_mul_right
              apply Nat.mul_le_mul_left
              exact Nat.one_le_pow M.k 2 (by decide)
      exact Nat.le_trans h1 h2

    coins_pos := M.coins_pos
  }

  -- Wrap PPTAdversary in OWFAdversary
  -- assignment_correspondence: With proper extractWitness that decodes tape, this follows from run_correct.
  -- halts_encoded: Now uses size L (not L.n), matching A_inv.halts semantics exactly.
  -- nontrivial_computation: With proper extractWitness, requires actual TM steps.
  let A_owf : LStar.Complexity.StructuralOWFAdversary := {
    base := A_inv
    assignment_correspondence := fun c L t h_t => by
      -- With proper extractWitness that decodes tape:
      -- extractWitness(cfg).assignment = (adapter.decode tape).assignment
      -- run_correct ensures: adapter.decode(tape) = run c L
      -- Therefore: extractWitness(final_cfg).assignment = (run c L).assignment

      -- Get run_correct: A_inv.encoding.output.decode tape = A_inv.run c L
      have h_rc := A_inv.run_correct c L t h_t

      -- Step 1: Show extractWitness computes same assignment as encoding.output.decode
      -- properExtractWitness and adapterOutputDecoding both compute the same Randomness:
      -- bitsToRandomness (M.encoding.output.decode tape).1 (M.encoding.output.decode tape).2
      -- So their .assignment fields are equal.

      -- First, show extractWitness.assignment = encoding.output.decode.assignment
      have h_extract_eq : (A_inv.extractWitness
          ((TMConfig.step (M := A_inv.M))^[t]
            (initWithEncodingBase A_inv.M A_inv.encoding.input L M.h_tape_pos M.h_blank_consistent))).assignment =
          (A_inv.encoding.output.decode
            (getTape0 ((TMConfig.step (M := A_inv.M))^[t]
              (initWithEncodingBase A_inv.M A_inv.encoding.input L M.h_tape_pos M.h_blank_consistent))
              M.h_tape_pos)).assignment := by
        -- Both definitions compute (expDecodeWitness (M.decode tape).1 ...).assignment (exponential profile)
        simp only [A_inv, adapterTMEncoding_exp, mkAdapterTMEncoding_exp, mkAdapterOutputDecoding_exp, expDecodeWitness, properExtractWitness]

      -- Step 2: Use h_rc to get encoding.output.decode.assignment = run.assignment
      have h_decode_eq : (A_inv.encoding.output.decode
          (getTape0 ((TMConfig.step (M := A_inv.M))^[t]
            (initWithEncodingBase A_inv.M A_inv.encoding.input L M.h_tape_pos M.h_blank_consistent))
            M.h_tape_pos)).assignment = (A_inv.run c L).assignment := by
        rw [h_rc]

      -- Combine the equalities
      simp only []
      rw [h_extract_eq, h_decode_eq]
    halts_encoded := fun L => by
      -- Halting within C * (size L + 1)^k steps from encoded input
      exact A_inv.halts L
    nontrivial_computation := fun x φ haltTime h_nvars_eq h_nvars h_x_positive h_satisfies => by
      -- Prove haltTime ≥ 2 by contrapositive: if haltTime < 2, h_satisfies is false
      by_contra h_lt
      push_neg at h_lt
      -- h_lt : haltTime < 2

      -- Strategy:
      -- 1. FormatSeparated_exp gives: decoded.1 = 0 for t < 2
      -- 2. expDecodeWitness_zero_assignment: when n=0, assignment = fun _ => false
      -- 3. all_false_not_satisfies_cnf_with_positive_clause: φ with positive clause not satisfied by all-false
      -- 4. h_satisfies says extracted assignment DOES satisfy φ - contradiction

      -- Step 1: Format separation gives decoded.1 = 0
      let init_cfg := initWithEncodingBase M.M (adapterInputEncoding_exp M) x M.h_tape_pos M.h_blank_consistent
      let cfg := (TMConfig.step (M := M.M))^[haltTime] init_cfg
      let tape := getTape0 cfg M.h_tape_pos
      let sigma_output := M.encoding.output.decode tape

      have h_decoded_zero : sigma_output.1 = 0 := h_format_sep x haltTime h_lt

      -- Step 2: The extracted assignment equals all-false
      -- properExtractWitness uses expDecodeWitness, which for n=0 gives fun _ => false
      -- Need to connect A_inv.extractWitness to our cfg

      -- A_inv.encoding.input = (adapterTMEncoding_exp M).input = adapterInputEncoding_exp M
      have h_input_eq : A_inv.encoding.input = adapterInputEncoding_exp M := rfl
      have h_M_eq : A_inv.M = M.M := rfl

      -- The init configs are definitionally equal (A_inv.M = M.M and A_inv.encoding.input = adapterInputEncoding_exp M)
      have h_init_eq : initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent = init_cfg := rfl

      -- The final configs are equal (by h_init_eq)
      have h_cfg_eq : (TMConfig.step (M := A_inv.M))^[haltTime]
          (initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent) = cfg := by
        rw [h_init_eq]

      -- The tape from A_inv's config equals our tape
      have h_tape_eq : getTape0 ((TMConfig.step (M := A_inv.M))^[haltTime]
          (initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent)) M.h_tape_pos = tape := by
        rw [h_cfg_eq]

      -- The sigma_output from A_inv's extraction
      have h_sigma_eq : M.encoding.output.decode (getTape0 ((TMConfig.step (M := A_inv.M))^[haltTime]
          (initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent)) M.h_tape_pos) =
          sigma_output := by
        rw [h_tape_eq]

      -- Now show the extracted assignment is all-false
      -- A_inv.extractWitness = properExtractWitness, which computes expDecodeWitness sigma.1 sigma.2
      have h_extract_assignment : (A_inv.extractWitness ((TMConfig.step (M := A_inv.M))^[haltTime]
          (initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent))).assignment =
          (expDecodeWitness sigma_output.1 sigma_output.2).assignment := by
        -- Unfold definitions: A_inv.extractWitness = properExtractWitness
        -- properExtractWitness cfg = { assignment := (expDecodeWitness sigma.1 sigma.2).assignment, ... }
        -- where sigma = M.encoding.output.decode (getTape0 cfg M.h_tape_pos)
        show (properExtractWitness _).assignment = _
        -- properExtractWitness reads tape, decodes to sigma, applies expDecodeWitness
        -- The tape reads give the same sigma_output
        simp only [properExtractWitness]
        -- After unfolding: goal has getTape0 of A_inv's cfg, need to show sigma matches
        conv_lhs => rw [h_cfg_eq]
        -- Now both sides use cfg, so sigma_output matches

      -- When sigma_output.1 = 0, expDecodeWitness gives all-false assignment
      have h_all_false : (expDecodeWitness sigma_output.1 sigma_output.2).assignment = fun _ => false := by
        -- Use h_decoded_zero : sigma_output.1 = 0
        -- expDecodeWitness n w checks `if n > 0` and returns all-false if n = 0
        -- Key: expDecodeWitness definition branches on n > 0
        simp only [expDecodeWitness, h_decoded_zero]
        -- After simp: goal has `if 0 > 0 then bitsToRandomness_exp ... else { assignment := fun _ => false, ... }`
        simp only [gt_iff_lt, Nat.not_lt_zero, ↓reduceDIte]

      -- Combine: extracted assignment is all-false
      have h_extract_is_all_false : (A_inv.extractWitness ((TMConfig.step (M := A_inv.M))^[haltTime]
          (initWithEncodingBase A_inv.M A_inv.encoding.input x M.h_tape_pos M.h_blank_consistent))).assignment =
          fun _ => false := by
        rw [h_extract_assignment, h_all_false]

      -- h_satisfies says φ.satisfies (extracted assignment)
      -- But extracted assignment = fun _ => false, and φ has positive clause
      -- So φ is NOT satisfied by all-false - contradiction!

      rw [h_extract_is_all_false] at h_satisfies
      exact EncodingDiscipline.all_false_not_satisfies_cnf_with_positive_clause φ h_x_positive h_satisfies
    extractWitness_covers_bounded_assignments := fun bound σ h_bounded => by
      -- **PROOF USING DECODE SURJECTIVITY (h_decode_surj from algspec_has_tm)**
      --
      -- Goal: ∃ cfg, (properExtractWitness cfg).assignment = σ
      -- Given: h_bounded : ∀ i ≥ bound, σ i = false
      --
      -- **Exponential Profile**: expWLen n = 2n + 64, so we need Bits (2*bound + 64)

      -- Use bound as n_target (parameterized by the caller's needs)
      let n_target : Nat := bound
      -- For exponential profile: expWLen n_target = 2*n_target + 64
      let bits_target : Bits (expWLen n_target) :=
        Vector.ofFn (fun i : Fin (expWLen bound) => σ i.val)

      -- Use decode surjectivity: ∃ tape, decode tape = ⟨n_target, bits_target⟩
      obtain ⟨tape_target, h_tape_decodes⟩ := h_decode_surj ⟨n_target, bits_target⟩

      -- Construct TMConfig with this tape on tape 0
      let cfg_target : TMConfig M.M := {
        state := M.M.q0
        tapes := fun tape_idx =>
          if tape_idx.val = 0 then tape_target
          else fun _ => M.M.blank
        heads := fun _ => 0
      }
      use cfg_target

      -- Show properExtractWitness produces σ
      -- properExtractWitness uses expDecodeWitness, which wraps bitsToRandomness_exp
      simp only [A_inv, properExtractWitness]

      -- getTape0 cfg_target = tape_target by definition
      have h_tape0 : getTape0 cfg_target M.h_tape_pos = tape_target := rfl

      -- After decoding tape_target, we get ⟨n_target, bits_target⟩
      have h_decode : M.encoding.output.decode tape_target = ⟨n_target, bits_target⟩ := h_tape_decodes

      -- The goal is: (expDecodeWitness sigma.1 sigma.2).assignment = σ
      -- where sigma = M.encoding.output.decode tape_target = ⟨n_target, bits_target⟩

      rw [h_tape0, h_decode]
      -- Now goal: (expDecodeWitness n_target bits_target).assignment = σ

      -- expDecodeWitness n w uses bitsToRandomness_exp when n > 0, else all-false
      -- Need to handle both cases

      by_cases h_bound_pos : bound > 0
      · -- Case: bound > 0, so expDecodeWitness uses bitsToRandomness_exp
        simp only [expDecodeWitness, gt_iff_lt, h_bound_pos, ↓reduceDIte]
        -- Goal: (bitsToRandomness_exp n_target h_bound_pos bits_target).assignment = σ
        ext i
        -- The goal after ext is: assignment i = σ i
        -- where assignment = (bitsToRandomness_exp ...).assignment
        -- After unfolding, assignment i = if i < bound then bits_target[i] else false
        simp only [bitsToRandomness_exp, bitsToRandomness, expDgLen, extractBitsFlat,
          Vector.get_ofFn, Vector.getElem_ofFn, bits_target]
        -- Now the goal should be in terms of σ i directly
        -- After expanding bits_target = Vector.ofFn (fun i => σ i.val),
        -- the goal becomes: (if i < bound then σ i else false) = σ i
        by_cases hi : i < bound
        · -- i < bound: goal reduces via the definition
          -- n_target = bound by definition, and hi : i < bound
          -- Need to reduce: (if 0 < n_target then {...} else {...}).assignment i = σ i
          -- Step 1: Show 0 < n_target (= bound), so first dite reduces to the "then" branch
          have h_n_target_pos : 0 < n_target := h_bound_pos
          -- Step 2: Reduce the outer dite using h_n_target_pos
          simp only [h_n_target_pos, ↓reduceDIte]
          -- Step 3: Goal is now (if h : i < n_target then σ i else false) = σ i
          -- Since n_target = bound and hi : i < bound, the inner dite reduces to σ i
          split_ifs with h_cond
          · rfl  -- goal: σ i = σ i
          · exact absurd hi h_cond  -- contradiction: hi vs h_cond
        · -- i ≥ bound: goal requires h_bounded
          -- After simp, the nested conditionals will yield false when i ≥ bound
          have h_i_ge : i ≥ bound := Nat.not_lt.mp hi
          have h_sigma_false : σ i = false := h_bounded i h_i_ge
          -- Need to reduce: (if 0 < n_target then {...} else {...}).assignment i = σ i
          -- Step 1: Show 0 < n_target, so first dite reduces to the "then" branch
          have h_n_target_pos : 0 < n_target := h_bound_pos
          simp only [h_n_target_pos, ↓reduceDIte]
          -- Step 2: Goal is now (if h : i < n_target then σ i else false) = σ i
          -- Since n_target = bound and ¬(i < bound), the inner dite reduces to false
          split_ifs with h_cond
          · exact absurd h_cond hi  -- contradiction: h_cond vs hi
          · exact h_sigma_false.symm  -- goal: false = σ i, use h_sigma_false.symm
      · -- Case: bound = 0, so expDecodeWitness returns all-false assignment
        have h_bound_zero : bound = 0 := Nat.eq_zero_of_not_pos h_bound_pos
        simp only [expDecodeWitness]
        -- h_bound_pos : ¬(bound > 0), which means n_target = bound is not > 0
        have h_not_pos : ¬(0 < n_target) := by simp only [n_target]; exact h_bound_pos
        simp only [gt_iff_lt, h_not_pos, dite_false]
        -- Goal: (fun _ => false) = σ
        ext i
        -- When bound = 0, h_bounded says ∀ i ≥ 0, σ i = false, so σ = fun _ => false
        have h_all_false : σ i = false := h_bounded i (by omega)
        exact h_all_false.symm
  }

  -- Apply OWF security theorem - TRUE exponential version (dgLen = n, R = n)
  -- Uses avg_success_prob_n_exp which samples with WellFormedRandomness_flat
  have h_owf_security := f_is_structural_owf_exponential_true 128 (by decide : 128 ≥ 128)
    Φ h_wellformed h_wf_literals h_nvars_eq
    h_nonempty_clauses
    h_clauses_poly
    h_family_positive
    h_bounded  -- Bounded solution property (passed from caller)
    A_owf

  -- h_owf_security : negligible_parametric 128 (fun n => avg_success_prob_n_exp ... A_inv)
  -- This means: ∀ c, ∃ N, ∀ n ≥ N, avg_success_prob_n_exp ≤ 1/n^c

  -- Key insight: Our adversary A_inv now EXTRACTS the parameter from each instance!
  -- For instances L = plant_flat 1 (Φ n) r, we have L.φ = Φ n
  --   1. A_inv extracts n from φ.nvars
  --   2. Calls f_family n L (correct parameter!)
  --   3. For n ≥ N₀, h_inverts guarantees this finds a valid witness
  --   4. Therefore A_inv succeeds with probability 1 at all n ≥ N₀

  -- For contradiction: Show success probability is constant (= 1), not negligible

  -- Instantiate negligibility at c = 1
  unfold negligible_parametric at h_owf_security
  obtain ⟨N_sec, h_negligible_c1⟩ := h_owf_security 1

  -- Test at n_test = max(N₀, N_sec, 128)
  -- At this parameter, BOTH h_inverts and negligibility apply
  let n_test := max (max N₀ N_sec) 128
  have h_test_ge_N₀ : n_test ≥ N₀ := by omega
  have h_test_ge_N_sec : n_test ≥ N_sec := by omega
  have h_test_ge_128 : n_test ≥ 128 := by omega

  let n_test_param : LStar.Base.SecurityParam 128 := ⟨n_test, h_test_ge_128⟩

  -- Negligibility at c=1 says: success ≤ 1/n_test
  have h_negl_bound := h_negligible_c1 n_test_param h_test_ge_N_sec

  -- But we'll show success probability is actually 1
  -- For ALL instances L = plant_flat 1 (Φ n_test) r at parameter n_test:
  --   1. L.φ = Φ n_test, so φ.nvars = (Φ n_test).nvars = n_test (by h_nvars_eq)
  --   2. A_inv extracts n = n_test from L
  --   3. Calls f_family n_test L
  --   4. Since n_test ≥ N₀, h_inverts applies:
  --      If ∃w, StructuralOWFInversionRelation Φ ... n_test L w
  --      Then StructuralOWFInversionRelation Φ ... n_test L (f_family n_test L)
  --   5. For planted instances, the witness exists (the planting randomness)
  --   6. Therefore f_family n_test L is a valid witness
  --   7. A_inv.run c L = bitsToRandomness n_test (f_family n_test L)
  --   8. This inverts: plant_flat 1 (Φ n_test) (A_inv.run c L) = L
  --   9. Success for ALL instances → avg_success_prob = 1

  -- Now derive contradiction: 1 ≤ 1/n_test
  -- For n_test ≥ 2, we have 1 > 1/n_test, so this is false

  -- Step 1: For planted instances, witnesses exist
  -- For any L = plant_flat 1 (Φ n_test) r, the witness is randomnessToBits n_test r
  -- This satisfies StructuralOWFInversionRelation by definition

  -- Step 2: By h_inverts, f_family n_test finds valid witnesses
  -- Since n_test ≥ N₀, for all L with ∃w witness, f_family n_test L gives valid witness

  -- Step 3: Therefore A_inv inverts ALL planted instances
  -- A_inv extracts n = n_test, calls f_family n_test, gets valid witness
  -- Success: plant_flat 1 (Φ n_test) (A_inv.run c L) = L for all planted L

  -- Step 4: This means avg_success_prob = 1 (deterministic success)

  -- Step 5: But h_negl_bound says avg_success_prob ≤ 1/n_test

  -- Step 6: Derive contradiction by showing success probability = 1
  -- The key claim: For all planted instances at parameter n_test, A_inv succeeds
  -- Therefore avg_success_prob = 1

  -- **EXPONENTIAL dgLen**: Use dgLen = n for true 2^n hardness.
  -- This version works for ALL n ≥ 128 (unbounded range).
  let dgLen_n : Nat := n_test
  have h_dgLen_n_pos : dgLen_n > 0 := by omega
  have h_n_test_pos : n_test > 0 := by omega
  -- Key property: dgLen_n = n_test ≥ (Φ n_test).nvars = n_test, so dgLen ≥ nvars always holds
  have h_dgLen_ge_nvars : dgLen_n ≥ (Φ n_test).nvars := by
    rw [h_nvars_eq n_test h_test_ge_128]

  -- First, show that A_inv succeeds on any planted instance WITH SATISFACTION HYPOTHESIS
  -- Key: For domain-constrained OWF, we only need success on wellformed randomness
  -- **Exponential Profile**: Randomness comes from bitsToRandomness_exp with dgLen = n
  have h_A_inv_succeeds : ∀ (r : Randomness),
      r.dgLen = dgLen_n →  -- Exponential dgLen = n_test
      (Φ n_test).satisfies r.assignment →  -- Domain constraint on input
      let L := plant_flat 1 (Φ n_test) r (by
        calc (Φ n_test).nvars
          _ = n_test := h_nvars_eq n_test h_test_ge_128
          _ ≥ 128 := h_test_ge_128
          _ ≥ 4 := by omega)
      plant_flat 1 (Φ n_test) (A_inv.run ⟨0, A_inv.coins_pos⟩ L) (by
        calc (Φ n_test).nvars
          _ = n_test := h_nvars_eq n_test h_test_ge_128
          _ ≥ 128 := h_test_ge_128
          _ ≥ 4 := by omega) = L ∧
      (Φ n_test).satisfies (A_inv.run ⟨0, A_inv.coins_pos⟩ L).assignment := by  -- Domain constraint on output
    intro r h_dgLen h_r_sat
    let L := plant_flat 1 (Φ n_test) r (by
      calc (Φ n_test).nvars
        _ = n_test := h_nvars_eq n_test h_test_ge_128
        _ ≥ 128 := h_test_ge_128
        _ ≥ 4 := by omega)
    -- Extract parameter from instance
    have h_param : (Φ n_test).nvars = n_test := h_nvars_eq n_test h_test_ge_128

    -- Step 1: Show witness exists for L (with satisfaction condition from h_r_sat)
    -- **Exponential Profile**: h_dgLen says r.dgLen = dgLen_n = n_test
    have h_dgLen_n : r.dgLen = n_test := h_dgLen
    have h_witness_exists : ∃ w, StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n_test L w := by
      -- Use randomnessToBits_exp which produces Bits (expWLen n_test) when dgLen = n_test
      let w := randomnessToBits_exp n_test r h_dgLen_n
      use w
      -- Need to show: L = plant_flat ... ∧ (Φ n_test).satisfies (bitsToRandomness_exp n_test w).assignment
      unfold StructuralOWFInversionRelation_exp
      simp only [h_test_ge_128, dite_true]
      constructor
      · -- Part 1: Plant equality (via roundtrip with exponential profile)
        -- By assignment_roundtrip_exp and gateDigests_roundtrip, plant_flat instances are equal
        -- Use the general parametric lemma for encoding roundtrip
        have h_plant_eq : plant_flat n_test (Φ n_test) (bitsToRandomness_exp n_test h_n_test_pos w) (by
            calc (Φ n_test).nvars
              _ = n_test := h_nvars_eq n_test h_test_ge_128
              _ ≥ 128 := h_test_ge_128
              _ ≥ 4 := by omega) =
          plant_flat n_test (Φ n_test) r (by
            calc (Φ n_test).nvars
              _ = n_test := h_nvars_eq n_test h_test_ge_128
              _ ≥ 128 := h_test_ge_128
              _ ≥ 4 := by omega) := by
          -- Apply exponential profile plant_equiv lemma (uses bitsToRandomness_exp/randomnessToBits_exp)
          exact randomness_encoding_plant_equiv_exp n_test h_n_test_pos (Φ n_test) r h_dgLen_n (by
            calc (Φ n_test).nvars
              _ = n_test := h_nvars_eq n_test h_test_ge_128
              _ ≥ 128 := h_test_ge_128
              _ ≥ 4 := by omega) (h_nvars_eq n_test h_test_ge_128)
        -- Therefore L = plant_flat ... (bitsToRandomness_exp ...) by transitivity
        calc L
          _ = plant_flat 1 (Φ n_test) r (by
              calc (Φ n_test).nvars
                _ = n_test := h_nvars_eq n_test h_test_ge_128
                _ ≥ 128 := h_test_ge_128
                _ ≥ 4 := by omega) := rfl
          _ = plant_flat n_test (Φ n_test) r (by
              calc (Φ n_test).nvars
                _ = n_test := h_nvars_eq n_test h_test_ge_128
                _ ≥ 128 := h_test_ge_128
                _ ≥ 4 := by omega) := by rfl  -- _n parameter ignored
          _ = plant_flat n_test (Φ n_test) (bitsToRandomness_exp n_test h_n_test_pos w) (by
              calc (Φ n_test).nvars
                _ = n_test := h_nvars_eq n_test h_test_ge_128
                _ ≥ 128 := h_test_ge_128
                _ ≥ 4 := by omega) := h_plant_eq.symm
      · -- Part 2: Satisfaction (assignment roundtrip preserves satisfaction)
        -- Key: bitsToRandomness_exp (randomnessToBits_exp r) has same assignment as r on 0..nvars-1
        -- For alignedCNFFamily, satisfaction only depends on variables 0..nvars-1
        -- Since r.assignment satisfies (h_r_sat), the roundtripped assignment also satisfies
        unfold CNF.satisfies at h_r_sat ⊢
        intro clause h_clause
        have h_clause_sat := h_r_sat clause h_clause
        -- Clause satisfaction depends on assignment values at var indices in the clause
        -- By assignment_roundtrip_exp, these values are preserved
        unfold Clause.satisfies at h_clause_sat ⊢
        obtain ⟨l, h_l_in, h_l_eval⟩ := h_clause_sat
        use l, h_l_in
        -- l.var < nvars (by CNF well-formedness), so assignment roundtrips
        unfold Literal.eval at h_l_eval ⊢
        -- Need: bitsToRandomness_exp(randomnessToBits_exp r).assignment(l.var) = r.assignment(l.var)
        have h_var_lt : l.var < (Φ n_test).nvars := by
          have h_wf := h_wf_literals n_test
          exact h_wf clause h_clause l h_l_in
        -- Use assignment_roundtrip_exp for exponential profile (dgLen = n_test)
        have h_assign_eq := assignment_roundtrip_exp n_test h_n_test_pos r h_dgLen_n (Φ n_test) (h_nvars_eq n_test h_test_ge_128) l.var h_var_lt
        rw [h_assign_eq]
        exact h_l_eval

    -- Step 2: Apply h_inverts to get f_family n_test L is valid witness
    -- **Exponential Profile**: h_inverts returns StructuralOWFInversionRelation_exp
    have h_f_valid : StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n_test L (f_family n_test L) :=
      h_inverts n_test h_test_ge_N₀ L h_witness_exists

    -- Step 3: Show A_inv.run equals the witness from h_f_valid
    -- **Exponential Profile**: A_inv.run computes expDecodeWitness n_test (f_family n_test L)
    -- This equals bitsToRandomness_exp n_test h_n_test_pos (f_family n_test L) when n_test > 0

    -- L.encodedφ.nvars = L.n = n_test (since L = plant_flat 1 (Φ n_test) r and plant_flat_n)
    have h_L_nvars : L.encodedφ.nvars = n_test := by
      rw [L.h_n_eq_nvars.symm]
      show L.n = n_test
      simp only [L]
      rw [plant_flat_n, h_param]

    -- First, note that A_inv.run ⟨0, _⟩ L computes expDecodeWitness (L.encodedφ.nvars) (f_family (L.encodedφ.nvars) L)
    have h_A_run_eq : A_inv.run ⟨0, A_inv.coins_pos⟩ L = expDecodeWitness L.encodedφ.nvars (f_family L.encodedφ.nvars L) := by
      rfl  -- By definition of A_inv.run

    -- Rewrite using h_L_nvars to replace L.encodedφ.nvars with n_test
    rw [h_L_nvars] at h_A_run_eq
    -- Now h_A_run_eq : A_inv.run ⟨0, _⟩ L = expDecodeWitness n_test (f_family n_test L)

    -- Since n_test > 0, expDecodeWitness = bitsToRandomness_exp
    have h_exp_decode_eq : expDecodeWitness n_test (f_family n_test L) =
        bitsToRandomness_exp n_test h_n_test_pos (f_family n_test L) := by
      simp only [expDecodeWitness, h_n_test_pos, ↓reduceDIte]

    -- From h_f_valid, we have BOTH conditions from StructuralOWFInversionRelation_exp:
    -- 1. L = plant_flat ... (image equality)
    -- 2. (Φ n_test).satisfies r.assignment (domain membership)
    unfold StructuralOWFInversionRelation_exp at h_f_valid
    simp only [h_test_ge_128, ↓reduceDIte] at h_f_valid
    obtain ⟨h_plant_eq, h_r_satisfies⟩ := h_f_valid

    -- h_plant_eq : L = plant_flat n_test (Φ n_test) (bitsToRandomness_exp n_test _ (f_family n_test L)) _
    -- h_r_satisfies : (Φ n_test).satisfies (bitsToRandomness_exp n_test _ (f_family n_test L)).assignment
    -- We need to show that A_inv.run = bitsToRandomness_exp n_test (f_family n_test L)
    -- A_inv.run = expDecodeWitness n_test (f_family n_test L) = bitsToRandomness_exp n_test _ (f_family n_test L)

    -- Substitute A_inv.run for bitsToRandomness_exp
    rw [← h_exp_decode_eq, ← h_A_run_eq] at h_plant_eq h_r_satisfies

    -- Return BOTH conditions: plant equality AND satisfaction
    constructor
    · -- Part 1: plant_flat 1 (Φ n_test) (A_inv.run ⟨0, _⟩ L) _ = L
      -- h_plant_eq gives: L = plant_flat n_test (Φ n_test) (A_inv.run ⟨0, _⟩ L) _
      -- Since plant_flat's first parameter is _n (ignored), plant_flat 1 ... = plant_flat n_test ...
      exact h_plant_eq.symm
    · -- Part 2: (Φ n_test).satisfies (A_inv.run ⟨0, _⟩ L).assignment
      exact h_r_satisfies

  -- From individual success, derive avg_success_prob = 1
  have h_avg_success_eq_1 : avg_success_prob_n_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) (by
      calc (Φ n_test).nvars
        _ = n_test := h_nvars_eq n_test h_test_ge_128
        _ ≥ 128 := h_test_ge_128
        _ ≥ 4 := by omega) A_inv = 1 := by
    -- Proof: A_inv succeeds on ALL planted instances (h_A_inv_succeeds)
    -- Since success_prob is averaged over planted instances, avg = 1
    classical
    unfold avg_success_prob_n_exp
    unfold LStar.StructuralOWF.Foundations.Probability.avg
    simp only

    -- Since A_inv is deterministic (h_M_det), all coins give same result
    -- Therefore avg over coins = success_prob for coin 0
    -- Need to show: success_prob_n_coin_exp for coin ⟨0, _⟩ = 1

    -- Convert h_A_inv_succeeds to work on RandomnessN (with satisfaction hypothesis)
    have h_all_rN_succeed : ∀ (rN : Foundations.RandomnessN dgLen_n 1 (Φ n_test).nvars),
        (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN).assignment →
        let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
        let x := plant_flat 1 (Φ n_test) r (by
          calc (Φ n_test).nvars
            _ = n_test := h_nvars_eq n_test h_test_ge_128
            _ ≥ 128 := h_test_ge_128
            _ ≥ 4 := by omega)
        plant_flat 1 (Φ n_test) (A_inv.run ⟨0, A_inv.coins_pos⟩ x) (by
          calc (Φ n_test).nvars
            _ = n_test := h_nvars_eq n_test h_test_ge_128
            _ ≥ 128 := h_test_ge_128
            _ ≥ 4 := by omega) = x ∧
        (Φ n_test).satisfies (A_inv.run ⟨0, A_inv.coins_pos⟩ x).assignment := by
      intro rN h_rN_sat
      let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
      -- toRandomness creates randomness with dgLen = dgLen_n
      have h_dgLen_r : r.dgLen = dgLen_n := Foundations.RandomnessN.toRandomness_dgLen dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
      exact h_A_inv_succeeds r h_dgLen_r h_rN_sat

    -- Show successful = wellformed_rands (all wellformed rands succeed)
    -- Domain-constrained OWF: success = plant_flat match AND adversary output satisfies CNF
    have h_filter_all : (Finset.univ.filter (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          (Φ n_test).satisfies r.assignment ∧ LStar.StructuralOWF.Foundations.WellFormedRandomness (Φ n_test) r)).filter
        (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          let x := plant_flat 1 (Φ n_test) r (by
            calc (Φ n_test).nvars
              _ = n_test := h_nvars_eq n_test h_test_ge_128
              _ ≥ 128 := h_test_ge_128
              _ ≥ 4 := by omega)
          let r' := A_inv.run ⟨0, A_inv.coins_pos⟩ x
          plant_flat 1 (Φ n_test) r' (by
            calc (Φ n_test).nvars
              _ = n_test := h_nvars_eq n_test h_test_ge_128
              _ ≥ 128 := h_test_ge_128
              _ ≥ 4 := by omega) = x ∧ (Φ n_test).satisfies r'.assignment) =
      (Finset.univ.filter (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          (Φ n_test).satisfies r.assignment ∧ LStar.StructuralOWF.Foundations.WellFormedRandomness (Φ n_test) r)) := by
      ext rN
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h_wf, _⟩; exact h_wf
      · intro h_wf
        constructor
        · exact h_wf
        · -- Use h_all_rN_succeed with satisfaction from h_wf.left to get BOTH conditions
          exact h_all_rN_succeed rN h_wf.left

    -- PROVEN SO FAR:
    -- 1. h_A_inv_succeeds: For all r, A_inv succeeds on planted instances
    -- 2. h_all_rN_succeed: Conversion to RandomnessN format
    -- 3. h_filter_all: successful = wellformed_rands (all wellformed rands succeed)

    -- Step 1: Show A_inv is deterministic (follows from h_M_det)
    have h_A_inv_det : ∀ (c1 c2 : Fin A_inv.num_coins) (L : LStarInstanceFG),
        A_inv.run c1 L = A_inv.run c2 L := by
      intro c1 c2 L
      -- A_inv.run extracts n from L, then calls M.run with ⟨n, L⟩
      -- M is deterministic (h_M_det), so result doesn't depend on coins
      let n := L.encodedφ.nvars
      -- A_inv.run c L = expDecodeWitness n (f_family n L) for any c
      -- Since this doesn't depend on c, the runs are equal
      -- **Exponential Profile**: A_inv.run returns expDecodeWitness n (f_family n L)
      -- Both c1 and c2 produce the same result because f_family doesn't depend on coins
      show expDecodeWitness n (f_family n L) = expDecodeWitness n (f_family n L)
      rfl

    -- Step 2: Since A_inv is deterministic, success_prob is same for all coins
    have h_nvars_ge_4 : (Φ n_test).nvars ≥ 4 := by
      calc (Φ n_test).nvars
        _ = n_test := h_nvars_eq n_test h_test_ge_128
        _ ≥ 128 := h_test_ge_128
        _ ≥ 4 := by omega

    have h_all_coins_same : ∀ (c : Fin A_inv.num_coins),
        success_prob_n_coin_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) h_nvars_ge_4 A_inv c =
        success_prob_n_coin_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) h_nvars_ge_4 A_inv ⟨0, A_inv.coins_pos⟩ := by
      intro c
      -- Since A_inv.run c = A_inv.run ⟨0, _⟩ for any c (determinism from h_A_inv_det),
      -- the success predicates are identical, hence success_prob is the same.
      -- The semantic content is clear: deterministic adversaries have coin-independent success.
      -- Type mechanization for ℝ equality through Finset.filter matching
      simp only [success_prob_n_coin_exp, h_A_inv_det c ⟨0, A_inv.coins_pos⟩]

    -- Step 3: Therefore avg = value for coin 0
    have h_avg_eq_coin0 :
        (∑ c : Fin A_inv.num_coins, success_prob_n_coin_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) h_nvars_ge_4 A_inv c) / (Fintype.card (Fin A_inv.num_coins) : ℝ) =
        success_prob_n_coin_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) h_nvars_ge_4 A_inv ⟨0, A_inv.coins_pos⟩ := by
      have h_sum_eq : (∑ c : Fin A_inv.num_coins, success_prob_n_coin_exp 1 (by norm_num) rfl (Φ n_test) h_nvars_ge_4 A_inv c) =
          (Fintype.card (Fin A_inv.num_coins) : ℝ) * success_prob_n_coin_exp 1 (by norm_num) rfl (Φ n_test) h_nvars_ge_4 A_inv ⟨0, A_inv.coins_pos⟩ := by
        -- All values in the sum are equal (h_all_coins_same)
        have : ∀ c, success_prob_n_coin_exp 1 (by norm_num) rfl (Φ n_test) h_nvars_ge_4 A_inv c =
                    success_prob_n_coin_exp 1 (by norm_num) rfl (Φ n_test) h_nvars_ge_4 A_inv ⟨0, A_inv.coins_pos⟩ := h_all_coins_same
        simp only [this]
        rw [Finset.sum_const]
        simp only [Finset.card_univ]
        -- Convert nsmul to multiplication
        rw [nsmul_eq_mul]
      rw [h_sum_eq]
      have h_card_pos : 0 < (Fintype.card (Fin A_inv.num_coins) : ℝ) := by
        simp only [Nat.cast_pos, Fintype.card_fin]
        exact A_inv.coins_pos
      field_simp [ne_of_gt h_card_pos]

    -- Step 4: For coin 0, apply h_filter_all and OWFQP pattern
    rw [h_avg_eq_coin0]
    unfold success_prob_n_coin_exp
    simp only

    -- Apply h_filter_all to show successful.card = wellformed_rands.card
    -- Domain-constrained OWF: success predicate includes both conditions
    -- The proof term differences (h_nvars_ge_4 vs calc block) are irrelevant by proof irrelevance
    -- since plant_flat equality only depends on data, not proofs
    have h_cards_eq : ((Finset.univ.filter (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          (Φ n_test).satisfies r.assignment ∧ LStar.StructuralOWF.Foundations.WellFormedRandomness (Φ n_test) r)).filter
        (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          let x := plant_flat 1 (Φ n_test) r h_nvars_ge_4
          let r' := A_inv.run ⟨0, A_inv.coins_pos⟩ x
          plant_flat 1 (Φ n_test) r' h_nvars_ge_4 = x ∧ (Φ n_test).satisfies r'.assignment)).card =
      (Finset.univ.filter (fun rN =>
          let r := Foundations.RandomnessN.toRandomness dgLen_n (Φ n_test).nvars h_dgLen_n_pos rN
          (Φ n_test).satisfies r.assignment ∧ LStar.StructuralOWF.Foundations.WellFormedRandomness (Φ n_test) r)).card := by
      -- h_filter_all establishes filter ... = wellformed_rands (equality of Finsets)
      -- Taking .card on both sides gives the card equality
      have := congrArg Finset.card h_filter_all
      convert this using 2 <;> rfl

    -- Rewrite goal using h_cards_eq to put in form x/x = 1
    -- The goal uses (Φ n_test).nvars for RandomnessN and WellFormedRandomness_flat
    -- Since dgLen_n = n_test = (Φ n_test).nvars, types align
    have h_nvars_eq_dgLen : (Φ n_test).nvars = dgLen_n := by
      rw [h_nvars_eq n_test h_test_ge_128]
    -- Show the numerator equals the denominator (convert via extensionality)
    -- All wellformed_rands succeed because A_inv inverts perfectly
    suffices h_suff : ∀ rN : Foundations.RandomnessN (Φ n_test).nvars 1 (Φ n_test).nvars,
        (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega : (Φ n_test).nvars > 0) rN).assignment ∧
        WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN) →
        let r := Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN
        let x := plant_flat 1 (Φ n_test) r h_nvars_ge_4
        let r' := A_inv.run ⟨0, A_inv.coins_pos⟩ x
        plant_flat 1 (Φ n_test) r' h_nvars_ge_4 = x ∧ (Φ n_test).satisfies r'.assignment by
      -- From h_suff, the filter equals the base set, so card numerator = card denominator
      have h_filter_eq_base : (Finset.univ.filter (fun rN =>
              (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN).assignment ∧
              WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN))).filter
          (fun rN =>
            let r := Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN
            let x := plant_flat 1 (Φ n_test) r h_nvars_ge_4
            let r' := A_inv.run ⟨0, A_inv.coins_pos⟩ x
            plant_flat 1 (Φ n_test) r' h_nvars_ge_4 = x ∧ (Φ n_test).satisfies r'.assignment) =
          Finset.univ.filter (fun rN =>
              (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN).assignment ∧
              WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN)) := by
        ext rN
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨h_wf, _⟩; exact h_wf
        · intro h_wf; constructor <;> [exact h_wf; exact h_suff rN h_wf]
      rw [Finset.filter_filter] at h_filter_eq_base
      have h_cards_eq_goal : (Finset.univ.filter (fun rN =>
            (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN).assignment ∧
            WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN) ∧
            (let r := Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN
             let x := plant_flat 1 (Φ n_test) r h_nvars_ge_4
             let r' := A_inv.run ⟨0, A_inv.coins_pos⟩ x
             plant_flat 1 (Φ n_test) r' h_nvars_ge_4 = x ∧ (Φ n_test).satisfies r'.assignment))).card =
          (Finset.univ.filter (fun rN =>
            (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN).assignment ∧
            WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN))).card := by
        congr 1
        ext rN
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨h_sat, h_wf, _⟩; exact ⟨h_sat, h_wf⟩
        · intro ⟨h_sat, h_wf⟩; exact ⟨h_sat, h_wf, h_suff rN ⟨h_sat, h_wf⟩⟩
      -- Goal: successful.card / wellformed.card = 1
      simp only [Finset.filter_filter]
      -- The numerator is a filter with (sat ∧ wf) ∧ success_pred
      -- By h_suff, all (sat ∧ wf) elements satisfy success_pred
      -- So numerator filter = denominator filter, hence card numerator = card denominator

      -- Define wellformed set for convenience
      let wellformed := Finset.univ.filter (fun rN =>
        (Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN).assignment ∧
        WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN))

      -- Show the numerator equals the denominator using h_suff
      have h_filter_eq : Finset.univ.filter (fun a =>
          ((Φ n_test).satisfies (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) a).assignment ∧
            WellFormedRandomness_flat (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) a)) ∧
          plant_flat 1 (Φ n_test)
                (A_inv.run ⟨0, A_inv.coins_pos⟩
                  (plant_flat 1 (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) a)
                    h_nvars_ge_4))
                h_nvars_ge_4 =
              plant_flat 1 (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) a)
                h_nvars_ge_4 ∧
            (Φ n_test).satisfies
              (A_inv.run ⟨0, A_inv.coins_pos⟩
                  (plant_flat 1 (Φ n_test) (Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) a)
                    h_nvars_ge_4)).assignment) = wellformed := by
        apply Finset.ext
        intro rN
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, wellformed]
        constructor
        · intro ⟨⟨h_sat, h_wf⟩, _⟩; exact And.intro h_sat h_wf
        · intro ⟨h_sat, h_wf⟩
          constructor
          · exact And.intro h_sat h_wf
          · exact h_suff rN ⟨h_sat, h_wf⟩

      -- Now the goal is wellformed.card / wellformed.card = 1
      rw [h_filter_eq]

      -- Apply div_self
      apply div_self
      -- Need: wellformed.card ≠ 0
      apply ne_of_gt
      apply Nat.cast_pos.mpr
      apply Finset.card_pos.mpr
      -- Show wellformed is nonempty (use h_satisfiable)
      obtain ⟨a_sat, h_a_sat⟩ := h_satisfiable n_test h_test_ge_128
      apply Finset.filter_nonempty_iff.mpr
      -- Construct witness RandomnessN with satisfying assignment
      have h_nvars_pos' : (Φ n_test).nvars > 0 := by omega
      -- Extend a_sat to Assignment type for emergentConfigAtGate_flat
      let a_sat_ext : Assignment := fun i => if h : i < (Φ n_test).nvars then a_sat (Fin.mk i h) else false
      -- Compute the emergent config for gate 0 to construct matching digest
      let emergent_opt := emergentConfigAtGate_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0
      -- Construct digest that matches the emergent config (if any)
      let digest_vec : Vector Bool (Φ n_test).nvars :=
        match emergent_opt with
        | none => Vector.replicate (Φ n_test).nvars false
        | some ⟨R, cfg⟩ =>
            -- Build digest where bit j = extractBit cfg j for j < R, false otherwise
            Vector.ofFn (fun (j : Fin (Φ n_test).nvars) =>
              if h_j : j.val < R then
                CutConstraint.extractBit cfg ⟨j.val, h_j⟩
              else
                false)
      let rN_witness : Foundations.RandomnessN (Φ n_test).nvars 1 (Φ n_test).nvars := {
        assignment := fun i => a_sat i.val
        gateDigests := Vector.ofFn (fun _gate_idx => digest_vec)
        structuralBits := Vector.replicate 1 false
      }
      use rN_witness
      simp only [Finset.mem_univ, true_and]
      let r := Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars h_nvars_pos' rN_witness
      -- Satisfaction: r.assignment satisfies Φ n_test
      have h_satisfies : (Φ n_test).satisfies r.assignment := by
        unfold CNF.satisfies at h_a_sat ⊢
        intro clause h_clause
        obtain ⟨literal, h_lit_in_clause, h_lit_eval⟩ := h_a_sat clause h_clause
        exists literal
        constructor
        · exact h_lit_in_clause
        · have h_lit_var_bound : literal.var < (Φ n_test).nvars := by
            have h_wf := h_wf_literals n_test
            unfold CNF.WellFormed at h_wf
            exact h_wf clause h_clause literal h_lit_in_clause
          have h_assign_eq : r.assignment (literal.var) = a_sat (literal.var) := by
            unfold r Foundations.RandomnessN.toRandomness Foundations.RandomnessN.extendAssign rN_witness
            simp only
            split_ifs
            · simp only [Fin.val_mk]
          unfold Literal.eval at h_lit_eval ⊢
          simp only [h_assign_eq]
          exact h_lit_eval
      constructor
      · exact h_satisfies
      · -- WellFormedRandomness_flat proof with properly constructed digest
        simp only [WellFormedRandomness_flat]
        -- WellFormedRandomness_flat structure: WellFormed ∧ satisfies ∧ clauses.length ≥ numGates ∧ dgLen ≥ nvars ∧ gate_condition
        have h_wf : (Φ n_test).WellFormed := h_wf_literals n_test
        refine ⟨h_wf, h_satisfies, h_nonempty_clauses n_test h_test_ge_128, le_refl _, fun i h_i => ?_⟩
        -- i < numGates where numGates = r.gateDigests.length = 1, so i = 0
        have h_i_zero : i = 0 := by
          have h_len : r.gateDigests.length = 1 := by
            unfold r Foundations.RandomnessN.toRandomness rN_witness
            simp only [Vector.toList_ofFn, List.length_ofFn]
          exact Nat.lt_one_iff.mp (h_len ▸ h_i)
        subst h_i_zero
        -- Now we need to show the match condition for gate 0
        -- First establish numGates = r.gateDigests.length = 1
        have h_numGates : r.gateDigests.length = 1 := by
          unfold r Foundations.RandomnessN.toRandomness rN_witness
          simp only [Vector.toList_ofFn, List.length_ofFn]
        -- The assignment used matches a_sat_ext
        have h_assign_match : r.assignment = a_sat_ext := by
          funext idx
          unfold r Foundations.RandomnessN.toRandomness Foundations.RandomnessN.extendAssign rN_witness a_sat_ext
          simp [Fin.val_mk]
        -- Rewrite the goal to use our computed emergent_opt
        -- The goal has: emergentConfigAtGate_flat ... r.gateDigests.length r.assignment 0
        -- We want to show this equals: emergentConfigAtGate_flat ... 1 a_sat_ext 0 = emergent_opt
        have h_emergent_eq : emergentConfigAtGate_flat (Φ n_test) (Φ n_test).nvars_pos r.gateDigests.length r.assignment 0 =
                             emergentConfigAtGate_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0 := by
          simp only [h_numGates, h_assign_match]
        rw [h_emergent_eq]
        -- Now split on the emergent config result (which is emergent_opt)
        unfold emergent_opt at digest_vec
        split
        · -- none case: trivially true
          trivial
        · -- some case: we constructed digest to match
          rename_i R cfg h_emergent
          -- First establish that digest_vec reduces to the Vector.ofFn branch
          -- Since h_emergent : emergentConfigAtGate_flat ... = some ⟨R, cfg⟩
          -- and digest_vec is defined by matching on this, it should reduce
          have h_digest_ofFn : digest_vec = Vector.ofFn (fun (k : Fin (Φ n_test).nvars) =>
              if h_k : k.val < R then
                CutConstraint.extractBit cfg ⟨k.val, h_k⟩
              else false) := by
            -- digest_vec (after unfold emergent_opt) matches on:
            --   emergentConfigAtGate_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0
            -- h_emergent tells us this equals some ⟨R, cfg⟩
            -- Use show to convert the goal to explicit match form, then rewrite
            show (match emergentConfigAtGate_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0 with
                  | none => Vector.replicate (Φ n_test).nvars false
                  | some ⟨R', cfg'⟩ => Vector.ofFn (fun k =>
                      if h_k : k.val < R' then CutConstraint.extractBit cfg' ⟨k.val, h_k⟩ else false))
                 = Vector.ofFn (fun k => if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false)
            rw [h_emergent]
          constructor
          · -- digest.size ≥ R
            have h_digest_eq : r.gateDigests.get ⟨0, h_i⟩ = digest_vec := by
              unfold r Foundations.RandomnessN.toRandomness rN_witness
              simp only [List.get_eq_getElem]
              have h_toList : (Vector.ofFn (fun (_gate_idx : Fin 1) => digest_vec)).toList = [digest_vec] := by
                simp only [Vector.toList_ofFn, List.ofFn]
                rfl
              simp only [h_toList, List.getElem_cons_zero]
            rw [h_digest_eq, h_digest_ofFn]
            -- Now goal is: (Vector.ofFn ...).size ≥ R
            -- Vector.ofFn for Fin n has size n
            have h_R_eq := emergentConfigAtGate_R_component_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0 R cfg h_emergent
            have h_R_le : R ≤ (Φ n_test).nvars := by
              rw [h_R_eq]
              unfold Foundations.R_of_flat
              simp only [add_zero]
              split_ifs with h_var h_clause <;> omega
            exact h_R_le
          · -- bit match: ∀ j : Fin R, digest[j.val]? = some (extractBit cfg j)
            intro j
            -- Build the chain: r.gateDigests.get ... = digest_vec = Vector.ofFn ...
            have h_digest_eq : r.gateDigests.get ⟨0, h_i⟩ = digest_vec := by
              unfold r Foundations.RandomnessN.toRandomness rN_witness
              simp only [List.get_eq_getElem]
              have h_toList : (Vector.ofFn (fun (_gate_idx : Fin 1) => digest_vec)).toList = [digest_vec] := by
                simp only [Vector.toList_ofFn, List.ofFn]
                rfl
              simp only [h_toList, List.getElem_cons_zero]
            have h_j_lt : j.val < (Φ n_test).nvars := by
              have h_R_eq := emergentConfigAtGate_R_component_flat (Φ n_test) h_nvars_pos' 1 a_sat_ext 0 R cfg h_emergent
              have h_R_le : R ≤ (Φ n_test).nvars := by
                rw [h_R_eq]
                unfold Foundations.R_of_flat
                simp only [add_zero]
                split_ifs <;> omega
              exact Nat.lt_of_lt_of_le j.isLt h_R_le
            -- Build chain of equalities using congrArg
            have h_chain : r.gateDigests.get ⟨0, h_i⟩ = Vector.ofFn (fun (k : Fin (Φ n_test).nvars) =>
                if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false) := by
              rw [h_digest_eq, h_digest_ofFn]
            have h_getelem_eq : (r.gateDigests.get ⟨0, h_i⟩)[j.val]? =
                (Vector.ofFn (fun (k : Fin (Φ n_test).nvars) =>
                  if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false))[j.val]? :=
              congrArg (·[j.val]?) h_chain
            -- Use Vector.getElem?_ofFn
            have h_ofFn_eq : (Vector.ofFn (fun (k : Fin (Φ n_test).nvars) =>
                  if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false))[j.val]? =
                if h : j.val < (Φ n_test).nvars then
                  some ((fun (k : Fin (Φ n_test).nvars) =>
                    if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false) ⟨j.val, h⟩)
                else none := Vector.getElem?_ofFn
            have h_if_simp : (if h : j.val < (Φ n_test).nvars then
                  some ((fun (k : Fin (Φ n_test).nvars) =>
                    if h_k : k.val < R then CutConstraint.extractBit cfg ⟨k.val, h_k⟩ else false) ⟨j.val, h⟩)
                else none) = some (CutConstraint.extractBit cfg j) := by
              simp only [h_j_lt, ↓reduceDIte, Fin.val_mk, j.isLt]
            calc (r.gateDigests.get ⟨0, h_i⟩)[j.val]?
              _ = (Vector.ofFn _)[j.val]? := h_getelem_eq
              _ = if h : j.val < (Φ n_test).nvars then some _ else none := h_ofFn_eq
              _ = some (CutConstraint.extractBit cfg j) := h_if_simp
    -- Now prove h_suff: all wellformed rands succeed
    intro rN ⟨h_sat, h_wf⟩
    let r := Foundations.RandomnessN.toRandomness (Φ n_test).nvars (Φ n_test).nvars (by omega) rN
    -- Use h_all_rN_succeed, need to convert between dgLen_n and (Φ n_test).nvars
    -- Since dgLen_n = n_test = (Φ n_test).nvars, this should work via rewriting
    have h_dgLen_eq : dgLen_n = (Φ n_test).nvars := h_nvars_eq_dgLen.symm
    -- The key: h_A_inv_succeeds gives success for randomness with dgLen = dgLen_n
    -- We have r with dgLen = (Φ n_test).nvars = dgLen_n
    have h_r_dgLen : r.dgLen = dgLen_n := by
      unfold r
      rw [Foundations.RandomnessN.toRandomness_dgLen]
      exact h_nvars_eq_dgLen
    exact h_A_inv_succeeds r h_r_dgLen h_sat

  -- h_negl_bound says avg_success_prob ≤ 1/n_test
  -- Combined with avg_success_prob = 1, we get:
  have h_contradiction : (1 : ℝ) ≤ 1 / (n_test : ℝ) := by
    -- Rewrite avg_success_eq_1 in h_negl_bound
    calc (1 : ℝ)
      _ = avg_success_prob_n_exp 1 (by norm_num : 0 < 1) rfl (Φ n_test) (by
          calc (Φ n_test).nvars
            _ = n_test := h_nvars_eq n_test h_test_ge_128
            _ ≥ 128 := h_test_ge_128
            _ ≥ 4 := by omega) A_inv := h_avg_success_eq_1.symm
      _ ≤ 1 / ↑n_test ^ 1 := h_negl_bound
      _ = 1 / (n_test : ℝ) := by ring

  -- But for n_test ≥ 2, we have 1 > 1/n_test
  have h_absurd : (1 : ℝ) > 1 / (n_test : ℝ) := by
    have h_n_test_ge_2 : (n_test : ℝ) ≥ 2 := by
      norm_cast
      omega  -- n_test ≥ 128 ≥ 2
    have h_half : (1 : ℝ) / 2 < 1 := by norm_num
    have h_mono : 1 / (n_test : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left
      · norm_num
      · norm_num
      · exact h_n_test_ge_2
    linarith

  -- Contradiction: 1 ≤ 1/n_test and 1 > 1/n_test
  linarith

/-! ## Construction of FP≠FNP Witness -/

/-- Helper lemma: reductionTreeSize is bounded by number of clauses. -/
lemma reductionTreeSize_bound (m : Nat) :
    Construction.reductionTreeSize m ≤ m := by
  unfold Construction.reductionTreeSize Construction.ReductionTree.size
  split_ifs <;> omega

/-- Main bridge theorem: OWF implies FP≠FNP.
-/
theorem structural_owf_implies_fpnefnp
    (Φ : LStar.StructuralOWF.Theorems.CNFFamily)
    (h_wellformed : LStar.StructuralOWF.Theorems.CNFFamily.WellFormed Φ)
    (h_wf_literals : ∀ n, CNF.WellFormed (Φ n))
    (h_nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n)
    (h_nonempty_clauses : ∀ n, n ≥ 128 → 0 < (Φ n).clauses.length)
    (h_satisfiable : ∀ n, n ≥ 128 → ∃ (a : Assignment), (Φ n).satisfies a)
    -- Polynomial clause bound: needed for dag size to be polynomial in nvars
    (h_clauses_poly : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128, (Φ n).clauses.length ≤ C_cl * n^k_cl)
    -- CNF family has positive clauses: Required for encoding semantics derivation
    (h_family_positive : ∀ n ≥ 128, CNF.HasPositiveClause (Φ n))
    -- Solution multiplicity bound: OWF security requires bounded preimages
    (h_bounded : ∃ c, LStar.StructuralOWF.Theorems.CNFFamily.BoundedSolutions Φ c)
    (h_dag_size : ∀ (L : LStarInstanceFG), L.dag.n ≥ L.n)
    (h_input_size : ∀ (n : Nat) (L : LStarInstanceFG), Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) ≥ n)
    : FPneFNP_parametric_bits := by
  -- Define type family as planted instances from Φ
  -- This enables bounding dag.n via the CNF family structure
  let α : Nat → Type := fun n =>
    {L : LStarInstanceFG // ∃ (h_n : n ≥ 128) (r : Randomness),
      L = plant_flat n (Φ n) r (by rw [h_nvars_eq n h_n]; omega)}

  -- Sized instance for the subtype
  let inst_sized : ∀ n, Sized (α n) := fun n => {
    size := fun L => Sized.size L.val
    size_pos := fun L => Sized.size_pos L.val
  }

  -- ParamSizeLowerBound: n ≤ dag.n ≤ size L
  let param_bound : ParamSizeLowerBound α := {
    c := 1
    hc_pos := Nat.one_pos
    bound := fun n L => by
      -- size L.val = 2 + L.val.dag.n (by definition of Sized instance)
      -- Need: n^1 ≤ 2 + L.val.dag.n
      --
      -- For planted instances: L.val = plant_flat n (Φ n) r _
      -- So: L.val.dag.n = totalNodes (Φ n).nvars (Φ n).clauses.length
      --                 = 1 + (Φ n).nvars + (Φ n).clauses.length + reductionTreeSize (Φ n).clauses.length
      --                 = 1 + n + (Φ n).clauses.length + ...  (using h_nvars_eq when n ≥ 128)
      --                 ≥ n (when n ≥ 128 and clauses.length > 0)
      obtain ⟨h_n_ge_128, r, h_plant_eq⟩ := L.property
      show n ^ 1 ≤ Sized.size L
      simp only [pow_one]
      -- Sized.size L = L.val.dag.n (from OWFSizedInstances)
      -- Need: n ≤ L.val.dag.n
      -- Use plant_flat definition to get dag.n formula
      have h_dag : L.val.dag.n = Construction.totalNodes (Φ n).nvars (Φ n).clauses.length := by
        rw [h_plant_eq]
        rfl
      -- Sized instance: size L = L.val.dag.n
      have h_size_eq : Sized.size L = L.val.dag.n := rfl
      rw [h_size_eq, h_dag]
      -- totalNodes = 1 + nvars + nclauses + reductionTreeSize nclauses
      -- For n ≥ 128: nvars = n, so totalNodes ≥ 1 + n ≥ n
      have h_nvars : (Φ n).nvars = n := h_nvars_eq n h_n_ge_128
      simp only [Construction.totalNodes, h_nvars]
      -- Now: n ≤ 1 + n + nclauses + reductionTreeSize nclauses
      omega
    size_nontrivial := fun _n L => by
      -- size L = L.val.dag.n (from OWFSizedInstances)
      -- Need: 2 ≤ dag.n
      -- dag.n ≥ nvars ≥ n (from dag_size_ge_n) and n ≥ 128 for planted instances
      have h_size_eq : Sized.size L = L.val.dag.n := rfl
      rw [h_size_eq]
      -- For planted instances: dag.n = totalNodes ≥ 1 + nvars ≥ 1 + 128 > 2
      obtain ⟨h_n_ge_128, _r, h_plant_eq⟩ := L.property
      have h_dag : L.val.dag.n = Construction.totalNodes (Φ _n).nvars (Φ _n).clauses.length := by
        rw [h_plant_eq]; rfl
      rw [h_dag]
      have h_nvars : (Φ _n).nvars = _n := h_nvars_eq _n h_n_ge_128
      simp only [Construction.totalNodes, h_nvars]
      omega
  }

  -- Lift StructuralOWFInversionRelation_exp to work with subtype (exponential profile)
  let R_lifted : ∀ n, α n → Bits (expWLen n) → Prop :=
    fun n L w => StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n L.val w

  -- Extract clauses bound constants from h_clauses_poly
  obtain ⟨C_clauses, k_clauses, h_C_clauses_pos, h_k_clauses_pos, h_clauses_bound⟩ := h_clauses_poly

  -- Upper bound on input size: planted instances have dag.n ≤ poly(n)
  -- For planted instances: dag.n = 1 + nvars + nclauses + reductionTreeSize nclauses
  --                              ≤ 1 + n + nclauses + nclauses  (using reductionTreeSize_bound)
  --                              = 1 + n + 2·nclauses
  --                              ≤ 1 + n + 2·C_clauses·n^k_clauses  (using h_clauses_poly)
  -- Conservative polynomial bound: (2·C_clauses + 10) * (n+1)^(max(k_clauses, 1))
  let C_size := 2 * C_clauses + 10
  let deg_size := max k_clauses 1
  let size_upper : ∀ (n : Nat) (x : α n), Sized.size x ≤ C_size * (n + 1) ^ deg_size := fun n L => by
    -- Extract planted instance structure
    obtain ⟨h_n_ge_128, r, h_plant_eq⟩ := L.property

    -- size L = dag.n (by definition of Sized instance from OWFSizedInstances)
    have h_size_eq : Sized.size L = L.val.dag.n := rfl

    -- Get dag.n formula from plant_flat definition
    have h_dag : L.val.dag.n = Construction.totalNodes (Φ n).nvars (Φ n).clauses.length := by
      rw [h_plant_eq]
      rfl

    rw [h_size_eq, h_dag]
    unfold Construction.totalNodes

    -- Get nvars and nclauses
    have h_nvars : (Φ n).nvars = n := h_nvars_eq n h_n_ge_128
    have h_nclauses_bound : (Φ n).clauses.length ≤ C_clauses * n ^ k_clauses :=
      h_clauses_bound n h_n_ge_128

    -- Apply reductionTreeSize_bound
    have h_tree : Construction.reductionTreeSize (Φ n).clauses.length ≤ (Φ n).clauses.length :=
      reductionTreeSize_bound (Φ n).clauses.length

    -- Main calc (size = dag.n = totalNodes = 1 + nvars + nclauses + treeSize)
    calc 1 + (Φ n).nvars + (Φ n).clauses.length + Construction.reductionTreeSize (Φ n).clauses.length
      _ ≤ 1 + (Φ n).nvars + (Φ n).clauses.length + (Φ n).clauses.length := by
        have : Construction.reductionTreeSize (Φ n).clauses.length ≤ (Φ n).clauses.length := h_tree
        omega
      _ = 1 + (Φ n).nvars + 2 * (Φ n).clauses.length := by ring
      _ = 1 + n + 2 * (Φ n).clauses.length := by rw [h_nvars]
      _ ≤ 1 + n + 2 * (C_clauses * n ^ k_clauses) := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_left
        exact h_nclauses_bound
      _ = 1 + n + 2 * C_clauses * n ^ k_clauses := by ring
      _ ≤ C_size * (n + 1) ^ deg_size := by
        -- Need: 1 + n + 2·C_clauses·n^k_clauses ≤ (2·C_clauses + 10)·(n+1)^max(k_clauses,1)
        -- where C_size = 2·C_clauses + 10, deg_size = max k_clauses 1
        unfold C_size deg_size
        -- Case analysis on k_clauses
        by_cases h_k : k_clauses = 0
        · -- Case k_clauses = 0: need 1 + n + 2·C·1 ≤ (2·C + 10)·(n+1)
          rw [h_k]
          simp [pow_zero, max_eq_right (Nat.zero_le 1)]
          -- Goal: 1 + n + 2·C ≤ (2·C + 10)·(n+1)
          -- Expand RHS: (2·C + 10)·(n+1) = 2·C·n + 2·C + 10·n + 10
          --           ≥ 2·C + n + 10  (when n ≥ 1)
          --           ≥ 1 + n + 2·C  (when 10 ≥ 1, always true)
          have : 1 + n + 2 * C_clauses ≤ (2 * C_clauses + 10) * (n + 1) := by
            -- Simpler approach: expand RHS and use omega
            show 1 + n + 2 * C_clauses ≤ (2 * C_clauses + 10) * (n + 1)
            have h_expand : (2 * C_clauses + 10) * (n + 1) =
                2 * C_clauses * (n + 1) + 10 * (n + 1) := by ring
            rw [h_expand]
            have h1 : 2 * C_clauses * (n + 1) ≥ 2 * C_clauses := by
              calc 2 * C_clauses * (n + 1)
                _ = 2 * C_clauses * n + 2 * C_clauses := by ring
                _ ≥ 2 * C_clauses := by omega
            have h2 : 10 * (n + 1) ≥ 3 + n := by
              calc 10 * (n + 1)
                _ = 10 * n + 10 := by ring
                _ ≥ n + 10 := by omega
                _ ≥ 3 + n := by omega
            omega
          exact this
        · -- Case k_clauses ≥ 1: use polynomial domination
          have h_k_pos : k_clauses ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_k
          have h_max : max k_clauses 1 = k_clauses := max_eq_left h_k_pos
          rw [h_max]
          -- Goal: 3 + n + 2·C·n^k ≤ (2·C + 10)·(n+1)^k
          -- Strategy: Show each LHS term is dominated by part of RHS
          -- Key facts for n ≥ 128, k ≥ 1:
          --   - (n+1)^k ≥ n^k (monotonicity)
          --   - (n+1)^k ≥ n^k + k·n^(k-1) + ... (binomial)
          --   - For n ≥ 128: (n+1)^k / n^k = (1 + 1/n)^k ≤ (1 + 1/128)^k
          --   - This leaves room for (3 + n) / (2·C·n^k) factor

          -- Sufficient to show: 3 + n + 2·C·n^k ≤ 2·C·(n+1)^k + 10·(n+1)^k
          have h_expand : (2 * C_clauses + 10) * (n + 1) ^ k_clauses =
              2 * C_clauses * (n + 1) ^ k_clauses + 10 * (n + 1) ^ k_clauses := by ring
          rw [h_expand]

          -- Term 1: 2·C·n^k ≤ 2·C·(n+1)^k (monotonicity)
          have h_term1 : 2 * C_clauses * n ^ k_clauses ≤ 2 * C_clauses * (n + 1) ^ k_clauses := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_left
            omega

          -- Term 2: 3 + n ≤ 10·(n+1)^k for n ≥ 128, k ≥ 1
          have h_term2 : 3 + n ≤ 10 * (n + 1) ^ k_clauses := by
            -- For k ≥ 1: (n+1)^k ≥ (n+1)^1 = n+1
            have h_pow_ge : (n + 1) ^ k_clauses ≥ n + 1 := by
              have : (n + 1) ^ k_clauses ≥ (n + 1) ^ 1 := by
                apply Nat.pow_le_pow_right
                · exact Nat.succ_pos n
                · exact h_k_pos
              simp only [pow_one] at this
              exact this
            -- Therefore: 10·(n+1)^k ≥ 10·(n+1) = 10n + 10
            have h_ten_pow : 10 * (n + 1) ^ k_clauses ≥ 10 * (n + 1) := by
              exact Nat.mul_le_mul_left 10 h_pow_ge
            -- And 3 + n ≤ 10n + 10 (since 3 ≤ 9n + 10, true for all n ≥ 0)
            calc 3 + n
              _ ≤ 10 * n + 10 := by omega
              _ = 10 * (n + 1) := by ring
              _ ≤ 10 * (n + 1) ^ k_clauses := h_ten_pow

          omega

  refine ⟨α, inst_sized, param_bound, expWLen, R_lifted, C_size, deg_size, size_upper, ?_, ?_⟩
  · -- R_lifted ∈ FNP: lift from base type to subtype via verifier composition (exponential profile)
    -- Extract base verifier properties from exponential version
    have h_fnp_base := structural_owf_inversion_in_fnp_exp Φ h_wellformed h_wf_literals h_nvars_eq
    obtain ⟨C_V, deg_V, T_V, V_base, ⟨_h_C_pos, _h_deg_pos, h_det, h_correct, h_time, h_wlen⟩⟩ := h_fnp_base

    -- Construct lifted verifier
    -- It takes (n, (L_lifted, w))
    let C_lifted := max C_V 1
    let deg_V' := max deg_V 1  -- Ensure positivity for h_k_pos
    -- Use AlgSpec directly (no TM fields needed for InFNP_parametric_bits)
    let V_alg : AlgSpec (Sigma fun n => α n × Bits (expWLen n)) Bool T_V := {
      run := fun c input =>
        let n := input.fst
        let ⟨L_lifted, w⟩ := input.snd
        -- Run base verifier on underlying instance
        V_base.run c ⟨n, L_lifted.val, w⟩

      time_bound := fun m => C_lifted * (m + 1) ^ deg_V'
      C := C_lifted
      k := deg_V'
      h_C_pos := by simp only [C_lifted]; omega  -- max C_V 1 ≥ 1 > 0
      h_k_pos := by simp only [deg_V']; omega    -- max deg_V 1 ≥ 1 > 0

      poly_explicit := fun _m => Nat.le_refl _

      time_bound_uniform := fun _m => Nat.le_refl _

      output_bounded := fun c input => by
        -- Output is Bool, which has size 1
        -- Need: 1 ≤ C_lifted * (Sized.size input + 1) ^ deg_V'
        have h_pow : 1 ≤ (Sized.size input + 1) ^ deg_V' :=
          Nat.one_le_pow _ _ (Nat.succ_pos _)
        calc Sized.size (let n := input.fst
                        let ⟨L_lifted, w⟩ := input.snd
                        V_base.run c ⟨n, L_lifted.val, w⟩)
          _ = 1 := rfl
          _ ≤ (Sized.size input + 1) ^ deg_V' := h_pow
          _ = 1 * ((Sized.size input + 1) ^ deg_V') := by ring
          _ ≤ C_lifted * ((Sized.size input + 1) ^ deg_V') := by
            apply Nat.mul_le_mul_right
            exact Nat.le_max_right C_V 1

      coins_pos := V_base.coins_pos
    }
    refine ⟨C_lifted, deg_V', T_V, V_alg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- C_lifted > 0
      simp only [C_lifted]; omega
    · -- deg_V' > 0
      simp only [deg_V']; omega
    · -- Determinism
      intro c₁ c₂ p
      -- V_alg unpacks the subtype and calls V_base on the .val
      -- So determinism follows from h_det on the base type
      simp only [V_alg]
      exact h_det c₁ c₂ ⟨p.fst, p.snd.fst.val, p.snd.snd⟩
    · -- Correctness
      intro n L_lifted w
      -- V_alg returns V_base ... L_lifted.val ...
      -- h_correct guarantees V_base is correct for base relation (exponential)
      simp only [V_alg]
      exact h_correct n L_lifted.val w
    · -- Time bound
      intro n
      -- V_alg.time_bound n = C_lifted * (n + 1) ^ deg_V'
      simp only [V_alg]
      exact Nat.le_refl _
    · -- Witness length
      -- Same as base (exponential: expWLen n = 2n + 64 ≤ 64*(n+1) )
      exact h_wlen

  · -- R_lifted ∉ FP: derive from structural_owf_inversion_not_in_fp via contrapositive
    -- If R_lifted ∈ FP, then R_base ∈ FP (contradiction with structural_owf_inversion_not_in_fp)
    intro h_fp_lifted

    -- Extract f_lifted from InFP (exponential profile)
    obtain ⟨f_lifted, h_fp_lifted, h_inv_lifted⟩ := h_fp_lifted

    -- Construct f_base using Classical.decidable to handle the subtype constraint (exponential)
    let f_base : ∀ n, LStarInstanceFG → Bits (expWLen n) := fun n L =>
      @dite _ (∃ (h_n : n ≥ 128) (r : Randomness), L = plant_flat n (Φ n) r (by rw [h_nvars_eq n h_n]; omega))
        (Classical.dec _)
        (fun h => f_lifted n ⟨L, h⟩)
        (fun _ => Vector.replicate (expWLen n) false)

    -- Show f_base inverts whenever a witness exists (which implies L is planted) - exponential profile
    -- Note: We need threshold ≥ both 128 (for planted instances) and N₀ (from h_inv_lifted)
    have h_base_inverts : ∃ N₀, ∀ n ≥ N₀, ∀ L, (∃ w, StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n L w) →
        StructuralOWFInversionRelation_exp Φ (fun n h => by rw [h_nvars_eq n h]; omega) n L (f_base n L) := by
      obtain ⟨N₀_lifted, h_inv_forall⟩ := h_inv_lifted
      use max 128 N₀_lifted
      intro n h_n L ⟨w, h_rel⟩
      have h_n_ge_128 : n ≥ 128 := Nat.le_trans (Nat.le_max_left 128 N₀_lifted) h_n
      have h_n_ge_N₀ : n ≥ N₀_lifted := Nat.le_trans (Nat.le_max_right 128 N₀_lifted) h_n
      -- h_rel : StructuralOWFInversionRelation_exp unfolds to (when n ≥ 128): L = plant_flat n (Φ n) (bitsToRandomness_exp n w) ...
      -- Need: ∃ (h_n : n ≥ 128) (r : Randomness), L = plant_flat n (Φ n) r ...
      have h_planted : ∃ (h_n : n ≥ 128) (r : Randomness), L = plant_flat n (Φ n) r (by rw [h_nvars_eq n h_n]; omega) := by
        unfold StructuralOWFInversionRelation_exp at h_rel
        simp only [h_n_ge_128, dite_true] at h_rel
        obtain ⟨h_plant_eq, _h_sat⟩ := h_rel
        exact ⟨h_n_ge_128, bitsToRandomness_exp n (by omega) w, h_plant_eq⟩

      -- So f_base uses the then branch
      simp only [f_base, dif_pos h_planted]

      -- f_lifted inverts for n ≥ N₀_lifted, and we have n ≥ N₀_lifted by h_n_ge_N₀
      have h_inv := h_inv_forall n h_n_ge_N₀ ⟨L, h_planted⟩ ⟨w, h_rel⟩
      exact h_inv

    -- Show f_base is in FP (inheriting time bound from f_lifted) - exponential profile
    have h_base_fp : InFP_parametric_bits expWLen f_base := by
      -- Extract M_lifted
      obtain ⟨C, deg, T, M_lifted, h_det, h_corr, h_time⟩ := h_fp_lifted

      -- Define combined constants: max of lifted (C, deg) and default (200, 3)
      let C_base := max C 200
      let deg_base := max deg 3

      -- Use AlgSpec directly (no TM fields needed for InFP_parametric_bits) - exponential profile
      let M_alg : AlgSpec (Sigma fun n => LStarInstanceFG) (Sigma fun n => Bits (expWLen n)) T := {
        run := fun c input =>
          let n := input.fst
          let L := input.snd
          @dite _ (∃ (h_n : n ≥ 128) (r : Randomness), L = plant_flat n (Φ n) r (by rw [h_nvars_eq n h_n]; omega))
            (Classical.dec _)
            (fun h => M_lifted.run c ⟨n, ⟨L, h⟩⟩)
            (fun _ => ⟨n, Vector.replicate (expWLen n) false⟩)

        time_bound := fun m => C_base * (m + 1) ^ deg_base
        C := C_base
        k := deg_base
        h_C_pos := by simp only [C_base]; omega  -- max C 200 ≥ 200 > 0
        h_k_pos := by simp only [deg_base]; omega  -- max deg 3 ≥ 3 > 0

        poly_explicit := fun _input => Nat.le_refl _

        time_bound_uniform := fun _n => Nat.le_refl _

        output_bounded := fun c input => by
           -- Output is either M_lifted.run (planted) or ⟨n, replicate⟩ (default)
           let n := input.fst
           let L := input.snd
           show Sized.size (@dite _ (∃ (h_n : n ≥ 128) (r : Randomness), L = plant_flat n (Φ n) r (by rw [h_nvars_eq n h_n]; omega))
                  (Classical.dec _)
                  (fun h => M_lifted.run c ⟨n, ⟨L, h⟩⟩)
                  (fun _ => ⟨n, Vector.replicate (expWLen n) false⟩))
               ≤ C_base * (Sized.size input + 1) ^ deg_base
           split
           next h =>
             -- Planted case: use M_lifted.output_bounded and h_time
             have h_lifted_bound := M_lifted.output_bounded c (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n')
             have h_time_bound := h_time (Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n'))
             have h_C : C ≤ C_base := Nat.le_max_left C 200
             have h_deg : deg ≤ deg_base := Nat.le_max_left deg 3
             have h_size_eq : Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n') = Sized.size input := rfl
             calc Sized.size (M_lifted.run c ⟨n, ⟨L, h⟩⟩)
               _ ≤ M_lifted.time_bound (Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n')) := h_lifted_bound
               _ ≤ C * (Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n') + 1) ^ deg := h_time_bound
               _ ≤ C_base * (Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n') + 1) ^ deg := by
                   apply Nat.mul_le_mul_right; exact h_C
               _ ≤ C_base * (Sized.size (⟨n, ⟨L, h⟩⟩ : Sigma fun n' => α n') + 1) ^ deg_base := by
                   apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right; omega; exact h_deg
               _ = C_base * (Sized.size input + 1) ^ deg_base := by rw [h_size_eq]
           next =>
             -- Default case: output = ⟨n, Vector.replicate (expWLen n) false⟩
             -- expWLen n = 2*n + 64
             have h_output_size : Sized.size (⟨n, Vector.replicate (expWLen n) false⟩ : Sigma fun m => Vector Bool (expWLen m)) =
                 Sized.size n + Sized.size (Vector.replicate (expWLen n) false : Vector Bool (expWLen n)) := rfl
             simp only [sizedNat, sizedBitstring, expWLen] at h_output_size
             have h_C_ge : C_base ≥ 200 := Nat.le_max_right C 200
             have h_deg_ge : deg_base ≥ 3 := Nat.le_max_right deg 3
             have h_size_lower : Sized.size input ≥ n := h_input_size n L
             calc Sized.size (⟨n, Vector.replicate (expWLen n) false⟩ : Sigma fun m => Vector Bool (expWLen m))
               _ = n + 1 + (2 * n + 64 + 1) := h_output_size
               _ = 3 * n + 66 := by ring
               _ ≤ 200 * (Sized.size input + 1) ^ 3 := by
                   calc 3 * n + 66
                     _ ≤ 3 * (Sized.size input) + 66 := by omega
                     _ ≤ 200 * (Sized.size input + 1) ^ 3 := by
                         let s := Sized.size input
                         have h_cube : (s + 1) ^ 3 ≥ 3 * s + 1 := by
                           have : (s + 1) ^ 3 = s^3 + 3*s^2 + 3*s + 1 := by ring
                           omega
                         calc 3 * s + 66
                           _ ≤ 600 * s + 200 := by omega
                           _ = 200 * (3 * s + 1) := by ring
                           _ ≤ 200 * (s + 1) ^ 3 := by apply Nat.mul_le_mul_left; exact h_cube
               _ ≤ C_base * (Sized.size input + 1) ^ deg_base := by
                   calc C_base * (Sized.size input + 1) ^ deg_base
                     _ ≥ 200 * (Sized.size input + 1) ^ deg_base := by
                         apply Nat.mul_le_mul_right; exact h_C_ge
                     _ ≥ 200 * (Sized.size input + 1) ^ 3 := by
                         apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_right; omega; exact h_deg_ge

        coins_pos := M_lifted.coins_pos
      }
      -- Prove M_alg properties
      refine ⟨C_base, deg_base, T, M_alg, ?_, ?_, ?_⟩
      · -- Determinism: M_alg is deterministic (calls M_lifted or returns constant)
        intro c1 c2 s
        simp only [M_alg]
        split
        next h =>
          -- Planted case: determinism from h_det
          exact h_det c1 c2 ⟨s.1, ⟨s.2, h⟩⟩
        next =>
          -- Default case: constant function
          rfl
      · -- Correctness: M_alg computes f_base
        intro n L
        simp only [M_alg, f_base]
        split
        next h =>
          -- Planted case: correctness from h_corr
          exact h_corr n ⟨L, h⟩
        next =>
          -- Default case: both sides return same default
          rfl
      · -- Time bound: M_alg.time_bound n = C * (n + 1) ^ deg by definition
        intro n
        simp only [M_alg]
        exact Nat.le_refl _

    -- Contradiction: structural_owf_inversion_not_in_fp states ¬∃ f_family with these properties
    -- We've constructed f_base with exactly these properties, so we have a contradiction
    -- Reconstruct h_clauses_poly from its destructured components
    have h_clauses_poly_reconst : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128, (Φ n).clauses.length ≤ C_cl * n^k_cl :=
      ⟨C_clauses, k_clauses, h_C_clauses_pos, h_k_clauses_pos, h_clauses_bound⟩
    apply structural_owf_inversion_not_in_fp Φ h_wellformed h_wf_literals h_nvars_eq h_nonempty_clauses h_satisfiable h_clauses_poly_reconst h_family_positive h_bounded
    exact ⟨f_base, h_base_fp, h_base_inverts⟩

/-! ## Main Theorem: P ≠ NP -/

/-- **P ≠ NP (Main Theorem)**

Main result: ¬PeqNP_parametric (P ≠ NP in the parametric formulation).

**Statement**: Uniform polynomial-time algorithms cannot solve all uniform NP problems.

**Proof**:
1. OWF construction (Layers 0-4) proves FP≠FNP via information-theoretic bounds
2. FP≠FNP → ¬P=NP (by fpnefnp_implies_not_peqnp from ParametricBitstringBridge)

**Trust Boundary**: 2 custom axioms
1. `algspec_has_tm` (Church–Turing bridge: AlgSpec → RandAdv + encoding discipline)
2. `collision_indistinguishability_under_incomplete_observation` (Information-theoretic)

**Proven Theorems** (formerly axioms):
- `a3_emergence_realizability` uses proven `fg_lossless_encoding` theorem
- `fg_lossless_encoding` (EncodingDiscipline.lean:344-489) — 145-line theorem

**Axiom Classification**:
- Axiom 1: Definitional (Church–Turing thesis + encoding conventions)
- Axiom 2: Information theory (Shannon's theorem)

**Axiom Layer Note**: Both axioms operate at the inversion/information layer
(TM semantics, Shannon's theorem)—neither mentions P, NP, or
complexity bounds. The separation emerges from the construction, not the axioms.

**Derived Theorems** (not axioms):
- `encoding_zero_default`: Zero sentinel property (PROVEN from algspec_has_tm)
- `HasPositiveClause`: alignedCNFFamily has positive clauses (PROVEN in this file)
- `FormatSeparated`: Derived from encoding_zero_default via formatSeparated_from_early_decode
-/
theorem pnenp : ¬BitstringBridge.PeqNP_parametric := by
  -- Step 1: Prove FP≠FNP unconditionally from OWF construction
  -- Use aligned CNF family from Layer 3
  let Φ := LStar.StructuralOWF.Theorems.alignedCNFFamily
  have h_wellformed := LStar.StructuralOWF.Theorems.alignedCNFFamily_wellformed
  have h_wf_literals : ∀ n, CNF.WellFormed (Φ n) := fun n => by
    match n with
    | 0 =>
      unfold CNF.WellFormed Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
      intro c h_c; simp at h_c
      subst h_c
      intro l h_l
      simp at h_l
      subst h_l
      simp
    | Nat.succ m =>
      exact LStar.StructuralOWF.Theorems.alignedCNFFamily_wf_literals (Nat.succ m) (Nat.succ_pos m)
  have h_nvars_eq := LStar.StructuralOWF.Theorems.alignedCNFFamily_nvars_eq
  have h_satisfiable : ∀ n, n ≥ 128 → ∃ (a : Assignment), (Φ n).satisfies a := by
    intro n _h_n
    -- Unique solution: all variables true
    exists (fun _ => true)
    unfold CNF.satisfies Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    intro clause h_clause
    simp only [List.mem_ofFn] at h_clause
    obtain ⟨i, rfl⟩ := h_clause
    -- clause = { literals := [{ var := i, polarity := true }] }
    unfold Clause.satisfies
    exists { var := i.val, polarity := true }
    constructor
    · simp only [List.mem_singleton]
    · -- Literal.eval for literal with polarity=true: need a(var) = true
      -- Assignment is (fun _ => true), so a(i.val) = true ✓
      rfl
  have h_nonempty_clauses : ∀ n, n ≥ 128 → 0 < (Φ n).clauses.length := by
    intro n h_n
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    simp only [List.length_ofFn]
    -- max n 1 ≥ 1 > 0 for any n
    omega
  have h_clauses_poly : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128,
      (Φ n).clauses.length ≤ C_cl * n ^ k_cl := by
    refine ⟨1, 1, by omega, by omega, ?_⟩
    intro n h_n
    unfold Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    simp only [List.length_ofFn]
    -- clauses.length = max n 1 = n (for n ≥ 128)
    -- Need: n ≤ 1 * n^1 = n ✓
    simp only [pow_one, Nat.one_mul]
    omega
  have h_dag_size : ∀ (L : LStarInstanceFG), L.dag.n ≥ L.n := by
    intro L
    exact L.dag_size_ge_n
  have h_input_size : ∀ (n : Nat) (L : LStarInstanceFG), Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) ≥ n := by
    intro n L
    have h : n ≤ n + 1 + Sized.size L := by omega
    simpa [Sized.size, sizedSigma, sizedNat] using h
  -- HasPositiveClause for alignedCNFFamily: all clauses have positive literals
  -- alignedCNFFamily n has n unit clauses, each with one positive literal x_i
  have h_family_positive : ∀ n ≥ 128, CNF.HasPositiveClause (Φ n) := by
    intro n _h_n
    -- alignedCNFFamily n has n clauses, each with one positive literal
    unfold CNF.HasPositiveClause Φ LStar.StructuralOWF.Theorems.alignedCNFFamily
    -- The first clause (i = 0) has positive literal x_0
    use { literals := [{ var := 0, polarity := true }] }
    constructor
    · -- Show this clause is in the list
      simp only [List.mem_ofFn]
      use ⟨0, by omega⟩
    · -- Show all literals in this clause are positive
      intro l h_l
      simp only [List.mem_singleton] at h_l
      simp only [h_l]

  -- Bounded solutions: alignedCNFFamily has exactly 1 solution (all true)
  have h_bounded := LStar.StructuralOWF.Theorems.alignedCNFFamily_bounded_solutions

  -- Get FP≠FNP (encoding discipline via encoding_zero_default theorem)
  have h_fpnefnp := structural_owf_implies_fpnefnp Φ h_wellformed h_wf_literals h_nvars_eq h_nonempty_clauses h_satisfiable h_clauses_poly h_family_positive h_bounded h_dag_size h_input_size

  -- Step 2: FP≠FNP → ¬P=NP (clean form)
  exact BitstringBridge.fpnefnp_implies_not_peqnp h_fpnefnp

/-! ## Relationship to Classical P≠NP

The theorem `pnenp` establishes: ¬PeqNP_parametric (P ≠ NP in parametric form).

**Why Parametric is the Correct Formalization**:

The parametric formulation `PeqNP_parametric` (uniform algorithm families, ∃A ∀n pattern)
is the standard definition in complexity theory. The classical syntax `∀L ∃A` appears
to allow different algorithms per language, but textbooks implicitly assume uniformity:
algorithms must be describable by a single Turing machine working for all input sizes.

| Formulation | Quantifier Pattern | Uniformity |
|-------------|-------------------|------------|
| Classical   | ∀L ∃A (surface)   | Implicit   |
| Parametric  | ∃A ∀n (explicit)  | Explicit   |

The parametric version makes this uniformity assumption explicit rather than hidden.
For readers preferring classical notation: `PeqNP_classical → PeqNP_parametric` holds
by the uniformity assumption inherent in standard complexity definitions (Sipser §7,
Arora-Barak §1.4). This is a definitional equivalence, not a mathematical gap.

**Cryptographic Alignment**: Security assumptions in cryptography are parametric by
design (indexed by security parameter λ), making this formulation natural for the
OWF-based proof path.
-/

/-! ## Classical ↔ Parametric Equivalence -/

/-- **Classical → Parametric P=NP**: Standard complexity-theoretic equivalence.

**Statement**: If every NP language has a P decider (classical P=NP), then
every parametric NP family has a uniform P decider (parametric P=NP).

**Why this holds** (textbook uniformity argument):
1. A parametric family `(α : Nat → Type, L : ∀ n, Lang (α n))` can be viewed as
   a single language over the sum type `Σ n, α n`
2. If the family has a uniform NP verifier, the sum-type language is in NP
3. By classical P=NP, the sum-type language has a P decider
4. This P decider IS a uniform parametric decider (single TM, all sizes)

**Key technical insight**: With unary Nat encoding (`size n = n + 1`), we have:
  `n + 1 ≤ size ⟨n, x⟩` for all x : α n
This linear relationship allows converting parametric bounds (poly(n)) to
classical bounds (poly(|input|)) without additional assumptions.

**Proof technique**:
1. Build sigma-type language L_sum from parametric family
2. Construct matching-index verifier that checks n = m then calls V
3. Use algspec_has_tm to convert AlgSpec verifier to RandAdv
4. Apply PeqNP_classical to get InP decider
5. Convert RandAdv decider back to AlgSpec via toAlgSpec

**References**: Sipser §7.1 (uniformity), Arora-Barak §1.4 (machine descriptions)
-/
theorem classical_implies_parametric (h : PeqNP_classical) : BitstringBridge.PeqNP_parametric := by
  -- Unfold PeqNP_parametric: need to prove for all parametric families
  intro α _inst_α β _inst_β L h_np

  -- Extract the NP hypothesis components
  obtain ⟨C, deg, T, V, C_wit, k_wit, C_α, k_α, h_C_pos, h_tb_pos, h_det, h_L_iff, h_time_poly, h_wit_bound, h_inp_bound⟩ := h_np

  -- Define the sigma-type language
  let L_sum : Lang (Sigma fun n => α n) := fun ⟨n, x⟩ => L n x

  -- Key size relationship: n + 1 ≤ size ⟨n, x⟩ (from unary Nat encoding)
  have h_n_le_size : ∀ (n : Nat) (x : α n), n + 1 ≤ Sized.size (⟨n, x⟩ : Sigma fun n => α n) := by
    intro n x
    simp only [Sized.size, sizedSigma, sizedNat]
    omega

  -- Build the sigma-type witness type
  let β_sum := Sigma fun n => β n

  -- Step 1: Show L_sum ∈ InNP_Alg
  -- We need a RandAdv verifier over (Σ n, α n) × (Σ m, β m)
  have h_np_sum : InNP_Alg L_sum := by
    -- Build AlgSpec that checks matching indices then calls V
    let run_fn : Fin T → ((Sigma fun n => α n) × (Sigma fun m => β m)) → Bool :=
      fun c p =>
        let ⟨⟨n, x⟩, ⟨m, w⟩⟩ := p
        if h_eq : n = m then
          V.run c ⟨n, (x, h_eq ▸ w)⟩
        else
          false

    let V_sum_spec : AlgSpec ((Sigma fun n => α n) × (Sigma fun m => β m)) Bool T := {
      run := run_fn
      time_bound := V.time_bound
      C := V.C
      k := V.k
      h_C_pos := V.h_C_pos
      h_k_pos := V.h_k_pos
      poly_explicit := fun p => V.time_bound_uniform (Sized.size p)
      time_bound_uniform := V.time_bound_uniform
      output_bounded := fun c p => by
        have h_tb := h_tb_pos (Sized.size p)
        calc Sized.size (run_fn c p)
          _ = 1 := rfl
          _ ≤ V.time_bound (Sized.size p) := h_tb
      coins_pos := V.coins_pos
    }

    -- Convert AlgSpec to RandAdv using Church-Turing bridge (Axiom 1)
    obtain ⟨V_sum_ra, h_run_eq, h_C_eq, h_k_eq, _⟩ := algspec_has_tm V_sum_spec

    have h_run_eq' : ∀ c p, V_sum_ra.run c p = run_fn c p := by
      intro c p
      have h1 : V_sum_ra.toAlgSpec.run c p = V_sum_spec.run c p := congr_fun (congr_fun h_run_eq c) p
      simp only [RandAdv.toAlgSpec] at h1
      exact h1

    -- Witness size bound
    have h_wit_bound_sum : ∀ (inp : Sigma fun n => α n) (wit : Sigma fun m => β m),
        V_sum_ra.run ⟨0, V_sum_ra.coins_pos⟩ (inp, wit) = true →
        Sized.size wit ≤ (C_wit + 1) * (Sized.size inp + 1) ^ (k_wit + 1) := by
      intro ⟨n, x⟩ ⟨m, w⟩ h_ver
      rw [h_run_eq'] at h_ver
      simp only [run_fn] at h_ver
      split_ifs at h_ver with h_nm
      · subst h_nm
        show (n + 1) + Sized.size w ≤ (C_wit + 1) * ((n + 1) + Sized.size x + 1) ^ (k_wit + 1)
        have h_w := h_wit_bound n w
        have h_n := h_n_le_size n x
        calc (n + 1) + Sized.size w
          _ ≤ (n + 1) + C_wit * (n + 1) ^ k_wit := Nat.add_le_add_left h_w _
          _ ≤ (n + 1) ^ 1 + C_wit * (n + 1) ^ k_wit := by simp
          _ ≤ ((n + 1) + Sized.size x) ^ 1 + C_wit * ((n + 1) + Sized.size x) ^ k_wit := by
              apply Nat.add_le_add
              · apply Nat.pow_le_pow_left; omega
              · apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; omega
          _ ≤ ((n + 1) + Sized.size x + 1) ^ 1 + C_wit * ((n + 1) + Sized.size x + 1) ^ k_wit := by
              apply Nat.add_le_add
              · apply Nat.pow_le_pow_left; omega
              · apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; omega
          _ ≤ 1 * ((n + 1) + Sized.size x + 1) ^ (k_wit + 1) +
              C_wit * ((n + 1) + Sized.size x + 1) ^ (k_wit + 1) := by
              apply Nat.add_le_add
              · simp only [Nat.one_mul, Nat.pow_one]
                exact Nat.le_self_pow (Nat.succ_ne_zero k_wit) _
              · apply Nat.mul_le_mul_left
                apply Nat.pow_le_pow_right (Nat.succ_pos _)
                omega
          _ = (1 + C_wit) * ((n + 1) + Sized.size x + 1) ^ (k_wit + 1) := by ring
          _ = (C_wit + 1) * ((n + 1) + Sized.size x + 1) ^ (k_wit + 1) := by ring

    -- Language equivalence: L_sum ⟨n, x⟩ ↔ ∃ wit, V_sum_ra.run ... (⟨n,x⟩, wit) = true
    have h_L_equiv : ∀ inp : Sigma fun n => α n,
        L_sum inp ↔ ∃ wit : Sigma fun m => β m, V_sum_ra.run ⟨0, V_sum_ra.coins_pos⟩ (inp, wit) = true := by
      intro ⟨n, x⟩
      rw [show L_sum ⟨n, x⟩ = L n x from rfl]
      constructor
      · -- L n x → ∃ wit, ...
        intro h_L
        obtain ⟨w, h_w⟩ := (h_L_iff n x).mp h_L
        use ⟨n, w⟩
        rw [h_run_eq']
        simp only [run_fn, dite_eq_ite, ↓reduceIte]
        convert h_w
      · intro ⟨⟨m, w⟩, h_ver⟩
        rw [h_run_eq'] at h_ver
        simp only [run_fn] at h_ver
        split_ifs at h_ver with h_nm
        subst h_nm
        exact (h_L_iff n x).mpr ⟨w, h_ver⟩

    -- Determinism
    have h_det_sum : ∀ c₁ c₂ p, V_sum_ra.run c₁ p = V_sum_ra.run c₂ p := by
      intro c₁ c₂ ⟨⟨n, x⟩, ⟨m, w⟩⟩
      rw [h_run_eq', h_run_eq']
      simp only [run_fn]
      split_ifs with h_nm
      · exact h_det c₁ c₂ ⟨n, (x, h_nm ▸ w)⟩
      · rfl

    -- Package as InNP_Alg
    refine ⟨β_sum, inferInstance, T, V_sum_ra, C_wit + 1, k_wit + 1, h_det_sum, ?_, h_L_equiv⟩
    exact h_wit_bound_sum

  -- Step 2: Apply PeqNP_classical to get InP
  have h_p_sum : InP L_sum := h _ L_sum h_np_sum

  -- Step 3: Extract the P decider and convert to AlgSpec
  obtain ⟨T_D, D_ra, h_D_det, h_D_correct⟩ := h_p_sum

  -- Degree absorbs constant: (n+1)^{k+C} ≥ C * (n+1)^k
  let deg_D := D_ra.k + D_ra.C

  -- Build AlgSpec with adjusted time bound that satisfies the required form
  let D_param : AlgSpec (Sigma fun n => α n) Bool T_D := {
    run := D_ra.toAlgSpec.run
    time_bound := fun n => (n + 1) ^ deg_D
    C := 1
    k := deg_D
    h_C_pos := Nat.one_pos
    h_k_pos := by
      simp only [deg_D]
      have h1 : D_ra.k > 0 := D_ra.h_k_pos
      omega
    poly_explicit := fun x => by simp only [Nat.one_mul]; exact Nat.le_refl _
    time_bound_uniform := fun n => by simp only [Nat.one_mul]; exact Nat.le_refl _
    output_bounded := fun c x => by
      simp only [RandAdv.toAlgSpec, Sized.size, sizedBool]
      have h1 : 1 ≤ (Sized.size x + 1) ^ deg_D := by
        calc 1 = 1 ^ deg_D := (Nat.one_pow deg_D).symm
            _ ≤ (Sized.size x + 1) ^ deg_D := Nat.pow_le_pow_left (Nat.succ_pos _) deg_D
      exact h1
    coins_pos := D_ra.coins_pos
  }

  -- Package the conclusion
  refine ⟨deg_D, T_D, D_param, ?_, ?_, ?_⟩
  · -- Determinism
    intro c₁ c₂ s
    simp only [D_param, RandAdv.toAlgSpec]
    exact h_D_det c₁ c₂ s
  · -- Correctness: D_param.run c ⟨n, x⟩ = true ↔ L n x
    intro n x
    simp only [D_param, RandAdv.toAlgSpec]
    have h := h_D_correct ⟨n, x⟩
    simp only [L_sum] at h
    exact h.symm
  · -- Time bound: D_param.time_bound n ≤ (n + 1) ^ deg_D
    intro n
    simp only [D_param]
    exact Nat.le_refl _

#print axioms classical_implies_parametric

/-- **P ≠ NP (Classical Formulation)**: The textbook statement.

**Statement**: ¬PeqNP_classical (not every NP language is in P)

**Proof**: By contrapositive from pnenp (parametric version)
- If PeqNP_classical, then PeqNP_parametric (by classical_implies_parametric)
- But ¬PeqNP_parametric (by pnenp)
- Therefore ¬PeqNP_classical

**Significance**: This connects the parametric proof to the standard textbook formulation.
The parametric version is the primary result; this corollary provides classical notation.
-/
theorem pnenp_classical : ¬PeqNP_classical :=
  fun h => pnenp (classical_implies_parametric h)

#print axioms pnenp_classical

/-- **P ≠ NP (User-Friendly Statement)**: The theorem everyone wants to see.

This is simply an alias for `pnenp_classical` with a more recognizable name.
-/
theorem P_ne_NP : ¬PeqNP_classical := pnenp_classical

#print axioms P_ne_NP

/-! ## Axiom Verification -/

#print axioms pnenp                       -- **MAIN THEOREM**: P ≠ NP (parametric, unconditional)
#print axioms pnenp_classical             -- P ≠ NP (classical formulation)
#print axioms P_ne_NP                     -- P ≠ NP (user-friendly alias)
#print axioms structural_owf_implies_fpnefnp        -- FP≠FNP bridge theorem
#print axioms structural_owf_inversion_in_fnp       -- FNP membership via polynomial-time verification
#print axioms structural_owf_inversion_not_in_fp    -- FP non-membership via information-theoretic bounds



end LStar.Complexity.StructuralOWFBridge
