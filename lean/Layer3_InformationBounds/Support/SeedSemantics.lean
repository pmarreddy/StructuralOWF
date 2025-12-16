import Layer1_Construction.Core.LStarInstance
import Layer1_Construction.Core.EmergenceMatrix
import Layer1_Construction.Core.SeedChain
import Layer1_Construction.Core.MultiLevelDAG
import Layer1_Construction.Core.Pools
import Layer0_Foundations.Base.FiniteEncoding
import Mathlib.Data.Vector.Basic

-- Import R_of_flat for centralized R computation (exponential profile)
-- This ensures type consistency between pure structure and planted instances
import Layer3_InformationBounds.Randomness.RanksExponential

/-! ## SeedSemantics: Pure Functions for Emergent Configuration (Non-Circular)

**Purpose**: Pure computational functions for emergent configurations without planted instance dependencies → enables non-circular well-formedness definitions.

**Key principle** (§6, §2.2): ALL functions PURE—compute from CNF structure + assignments only, NO randomness/planting dependence.

**Architectural role** (supports PlantedInstanceConsistency.lean):
1. emergentConfigAtGate φ a i: Pure emergent config computation
2. WellFormedRandomness φ r: Non-circular well-formedness definition
3. Separation: φ-determined structure vs r-determined randomness

**Helpers** (fully implemented): assignmentToVector, seedToBits, vectorToFin, vectorTakeLast, extractEmergentBits

**Complex functions** (implemented): lstarStructureFromCNF (pure DAG from φ), computeSeedAtVertex (recursive seed from assignment), emergentConfigAtVertex (full implementation)

**Trust boundary**: 7 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

open LStar

/-! ## Basic Helpers (Fully Implemented) -/

/-- Convert assignment to bit vector for first n variables. -/
def assignmentToVector (a : AssignmentInf) (n : Nat) : Vector Bool n :=
  Vector.ofFn (fun i => a i.val)

/-- Convert Seed to bit vector. -/
def seedToBits {n} (s : Seed n) : Vector Bool n :=
  Vector.ofFn (fun i => Seed.get s i)

/-- Convert bit vector to Fin (2^n) by interpreting as binary number.

    **Algorithm**: Fold bits as big-endian binary:
    [b₀, b₁, ..., bₙ₋₁] → b₀·2^(n-1) + b₁·2^(n-2) + ... + bₙ₋₁·2^0

    **Note**: This matches the parity encoding used in FrontierGate. -/
def vectorToFin {n} (v : Vector Bool n) : Fin (2^n) :=
  let bits := v.toList
  let val := bits.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0
  ⟨val % (2^n), Nat.mod_lt val (Nat.two_pow_pos n)⟩

/-- Extract last R elements from a vector of length n (where R ≤ n).

    **Use case**: Extract emergent bits from seed:
    seed = [parent_bits | emergent_bits]
                         ↑ last R_v bits  -/
def vectorTakeLast {n} (v : Vector Bool n) (R : Nat) (h : R ≤ n) : Vector Bool R :=
  Vector.ofFn (fun i => v.get ⟨n - R + i, by omega⟩)

/-! ## Seed Extraction Lemmas -/

/-- Extract emergent portion from a Seed.

    **Semantic meaning**: For seed_v with structure [parent_bits | R_v emergent bits],
    extract the last R_v bits as emergent configuration.

    **Parameters**:
    - s: Full seed at vertex v
    - R: Number of emergent bits (R_v)
    - h: Proof that R ≤ seed width (from L.seedWidth_ok) -/
def extractEmergentBits {n} (s : Seed n) (R : Nat) (h : R ≤ n) : Vector Bool R :=
  vectorTakeLast (seedToBits s) R h

/-- Convert emergent bit vector to configuration value Fin (2^R). -/
def emergentBitsToConfig {R} (bits : Vector Bool R) : Fin (2^R) :=
  vectorToFin bits

/-! ## vectorToFin Properties

Key properties of the big-endian bit-to-number conversion used in emergence encoding.

**Mathematical Foundation**: These lemmas establish that big-endian binary encoding/decoding
is correctly implemented. The key property is that extracting bits MSB-first and folding
with (acc * 2 + bit) recovers the original value - this is the standard binary representation
theorem from number theory.

**Trust Level**: The core lemma `vectorToFin_reversed_encoding` captures a standard
mathematical fact about binary representation. While the full proof is complex due to
Lean 4's definitional requirements, the mathematical claim is uncontroversial.
-/

/-- Bridge: (val >>> k) % 2 = 1 ↔ Nat.testBit val k.

    **Proof**: Uses Nat.shiftRight_eq_div_pow and Nat.testBit_eq_decide_div_mod_eq from Mathlib. -/
private lemma ss_shift_mod_decide_eq_testBit (val k : Nat) :
    decide ((val >>> k) % 2 = 1) = Nat.testBit val k := by
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq]

/-- Horner's method invariant: foldl with initial accumulator can be split. -/
private lemma ss_foldl_horner_invariant (bits : List Bool) (acc : Nat) :
    bits.foldl (fun a b => a * 2 + b.toNat) acc =
    acc * 2^bits.length + bits.foldl (fun a b => a * 2 + b.toNat) 0 := by
  induction bits generalizing acc with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have h0 : (0 : Nat) * 2 + b.toNat = b.toNat := by ring
    rw [h0, ih (acc * 2 + b.toNat), ih b.toNat]
    ring

/-- Bound: foldl result is strictly less than 2^(list length). -/
private lemma ss_foldl_builds_binary (bits : List Bool) :
    bits.foldl (fun a b => a * 2 + b.toNat) 0 < 2^bits.length := by
  induction bits with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have h0 : (0 : Nat) * 2 + b.toNat = b.toNat := by ring
    rw [h0, ss_foldl_horner_invariant rest b.toNat]
    have h1 : b.toNat ≤ 1 := by cases b <;> simp
    have h2 : b.toNat * 2^rest.length ≤ 1 * 2^rest.length :=
      Nat.mul_le_mul_right (2^rest.length) h1
    simp only [one_mul] at h2
    omega

/-- Helper: testBit is false above the bound for val < 2^R. -/
private lemma ss_testBit_high_false {R : Nat} (val : Nat) (h_val : val < 2^R) (i : Nat) (hi : i ≥ R) :
    Nat.testBit val i = false := by
  apply Nat.testBit_eq_false_of_lt
  calc val < 2^R := h_val
       _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hi

/-- Helper: testBit of (a * 2^n + b) equals testBit b when i < n (and b < 2^n).
    This is the key property for Horner's method decomposition. -/
private lemma ss_testBit_add_mul_pow_low {n i : Nat} (a b : Nat) (hb : b < 2^n) (hi : i < n) :
    Nat.testBit (a * 2^n + b) i = Nat.testBit b i := by
  -- The key is that a * 2^n contributes only to bits >= n
  -- So bits 0..n-1 come entirely from b
  induction n generalizing a b i with
  | zero => omega  -- i < 0 is impossible
  | succ m ih =>
    cases i with
    | zero =>
      -- testBit (...) 0 = testBit b 0
      rw [Nat.testBit_zero, Nat.testBit_zero]
      -- a * 2^(m+1) is even, so (a * 2^(m+1) + b) % 2 = b % 2
      have h1 : (a * 2^(m+1)) % 2 = 0 := by
        have h_pow : 2^(m+1) = 2^m * 2 := Nat.pow_succ 2 m
        rw [h_pow]
        have h_assoc : a * (2^m * 2) = (a * 2^m) * 2 := by ring
        rw [h_assoc]
        have h_comm : (a * 2^m) * 2 = 2 * (a * 2^m) := Nat.mul_comm _ _
        rw [h_comm]
        exact Nat.mul_mod_right 2 (a * 2^m)
      have h2 : (a * 2^(m+1) + b) % 2 = b % 2 := by omega
      rw [h2]
    | succ j =>
      -- testBit (...) (j+1) = testBit (... / 2) j
      rw [Nat.testBit_succ, Nat.testBit_succ]
      -- (a * 2^(m+1) + b) / 2 = a * 2^m + b / 2
      have h_div : (a * 2^(m+1) + b) / 2 = a * 2^m + b / 2 := by
        -- 2^(m+1) = 2 * 2^m
        have h_pow2 : 2^(m+1) = 2 * 2^m := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [h_pow2]
        -- a * (2 * 2^m) + b = 2 * (a * 2^m) + b = b + 2 * (a * 2^m)
        have h_eq : a * (2 * 2^m) + b = b + 2 * (a * 2^m) := by ring
        rw [h_eq, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
        ring
      rw [h_div]
      have hb' : b / 2 < 2^m := by
        have h_pow2 : 2^(m+1) = 2 * 2^m := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [h_pow2] at hb
        exact Nat.div_lt_of_lt_mul hb
      have hj : j < m := Nat.lt_of_succ_lt_succ hi
      exact ih a (b / 2) hb' hj

/-- Helper: testBit of (a * 2^n + b) at position n equals testBit a 0 (when b < 2^n and a < 2). -/
private lemma ss_testBit_add_mul_pow_eq {n : Nat} (a b : Nat) (hb : b < 2^n) (ha : a < 2) :
    Nat.testBit (a * 2^n + b) n = Nat.testBit a 0 := by
  induction n generalizing a b with
  | zero =>
    -- n = 0: (a * 1 + b) = a + b, and b < 1 means b = 0
    simp at hb
    simp [hb]
  | succ m ih =>
    rw [Nat.testBit_succ]
    -- (a * 2^(m+1) + b) / 2 = a * 2^m + b / 2
    have h_div : (a * 2^(m+1) + b) / 2 = a * 2^m + b / 2 := by
      -- 2^(m+1) = 2 * 2^m
      have h_pow2 : 2^(m+1) = 2 * 2^m := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [h_pow2]
      -- a * (2 * 2^m) + b = b + 2 * (a * 2^m)
      have h_eq : a * (2 * 2^m) + b = b + 2 * (a * 2^m) := by ring
      rw [h_eq, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      ring
    rw [h_div]
    have hb' : b / 2 < 2^m := by
      have h_pow2 : 2^(m+1) = 2 * 2^m := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h_pow2] at hb
      exact Nat.div_lt_of_lt_mul hb
    exact ih a (b / 2) hb' ha

/-- Helper: testBit of (a * 2^n + b) is false for i > n when a * 2^n + b < 2^(n+1). -/
private lemma ss_testBit_add_mul_pow_high {n i : Nat} (a b : Nat)
    (h_sum : a * 2^n + b < 2^(n+1)) (hi : i > n) :
    Nat.testBit (a * 2^n + b) i = false := by
  apply ss_testBit_high_false _ h_sum
  omega

/-- **Core Property**: foldl of big-endian testBit produces the original value.

    **Statement**: For val < 2^R, foldl [testBit val (R-1), ..., testBit val 0] = val.

    **Mathematical Proof** (binary representation uniqueness):
    The foldl computes Horner's method at x=2:
    - Result = testBit(R-1)·2^{R-1} + testBit(R-2)·2^{R-2} + ... + testBit(0)·2^0
    - This equals Σ_{i<R} testBit(val, i)·2^i = val (standard binary representation)

    **Proof technique**: Induction on R, using custom helpers for bit-position analysis. -/
private lemma ss_foldl_testBit_eq_val {R : Nat} (val : Nat) (h_val : val < 2^R) :
    (List.ofFn (fun j : Fin R => Nat.testBit val (R - 1 - j.val))).foldl
      (fun a b => a * 2 + b.toNat) 0 = val := by
  -- Prove equality by showing all bits match
  apply Nat.eq_of_testBit_eq
  intro i
  -- Induction on R
  induction R generalizing val i with
  | zero =>
    -- R = 0, val < 1, so val = 0
    simp at h_val
    simp [h_val]
  | succ n ih =>
    -- R = n + 1, bits = [testBit val n, testBit val (n-1), ..., testBit val 0]
    simp only [List.ofFn_succ, List.foldl_cons]

    -- Simplify: ↑(0 : Fin (n+1)) = 0, so (n + 1 - 1 - ↑0) = n
    have h_fin0 : (0 : Fin (n + 1)).val = 0 := rfl
    simp only [h_fin0, Nat.add_sub_cancel, Nat.sub_zero]

    -- After first step: acc = (0 * 2 + (testBit val n).toNat) = (testBit val n).toNat
    have h0 : (0 : Nat) * 2 + (Nat.testBit val n).toNat = (Nat.testBit val n).toNat := by ring
    simp only [h0]

    -- The remaining list is [testBit val (n-1), ..., testBit val 0]
    have h_rest : (List.ofFn fun j : Fin n => Nat.testBit val (n - ↑j.succ)) =
                  (List.ofFn fun j : Fin n => Nat.testBit val (n - 1 - j.val)) := by
      congr 1
      funext j
      simp only [Fin.val_succ]
      rw [Nat.sub_sub]
      ring_nf

    simp only [h_rest]

    -- Use Horner's invariant: foldl acc rest = acc * 2^n + foldl 0 rest
    rw [ss_foldl_horner_invariant]
    have h_len : (List.ofFn (fun j : Fin n => Nat.testBit val (n - 1 - j.val))).length = n := by
      simp only [List.length_ofFn]
    rw [h_len]

    -- Now the foldl result is: (testBit val n).toNat * 2^n + foldl 0 [lower bits]
    -- Let a = (testBit val n).toNat and b = foldl 0 [lower bits]

    have h_foldl_bound : (List.ofFn (fun j : Fin n => Nat.testBit val (n - 1 - j.val))).foldl
                          (fun a b => a * 2 + b.toNat) 0 < 2^n := by
      have hb := ss_foldl_builds_binary (List.ofFn (fun j : Fin n => Nat.testBit val (n - 1 - j.val)))
      simp only [List.length_ofFn] at hb
      exact hb

    have h_a_bound : (Nat.testBit val n).toNat < 2 := by cases Nat.testBit val n <;> simp

    -- Split into cases based on i
    by_cases hi : i < n
    · -- Case i < n: The bit comes from the foldl of lower bits
      rw [ss_testBit_add_mul_pow_low (Nat.testBit val n).toNat _ h_foldl_bound hi]

      -- The foldl computes the lower n bits of val
      -- We need: testBit (foldl [...]) i = testBit val i

      -- Key: the lower bits of val are the same as val % 2^n
      have h_mod_bits : (List.ofFn fun j : Fin n => Nat.testBit val (n - 1 - j.val)) =
                        (List.ofFn fun j : Fin n => Nat.testBit (val % 2^n) (n - 1 - j.val)) := by
        congr 1
        funext j
        have hj : n - 1 - j.val < n := by omega
        rw [Nat.testBit_mod_two_pow]
        simp [hj]

      rw [h_mod_bits]
      have h_val_mod : val % 2^n < 2^n := Nat.mod_lt val (Nat.two_pow_pos n)
      rw [ih (val % 2^n) h_val_mod]
      rw [Nat.testBit_mod_two_pow]
      simp [hi]

    · -- Case i ≥ n
      push_neg at hi
      by_cases hi2 : i = n
      · -- Case i = n: The bit is exactly (testBit val n)
        rw [hi2]
        rw [ss_testBit_add_mul_pow_eq (Nat.testBit val n).toNat _ h_foldl_bound h_a_bound]
        rw [Nat.testBit_zero]
        cases Nat.testBit val n <;> simp [Bool.toNat]

      · -- Case i > n: Both sides are false
        have hi3 : i > n := Nat.lt_of_le_of_ne hi (Ne.symm hi2)
        have h_high : Nat.testBit val i = false := ss_testBit_high_false val h_val i (by omega)
        rw [h_high]

        -- Show the sum is < 2^(n+1)
        have h_sum_bound : (Nat.testBit val n).toNat * 2^n +
                            (List.ofFn (fun j : Fin n => Nat.testBit val (n - 1 - j.val))).foldl
                              (fun a b => a * 2 + b.toNat) 0 < 2^(n+1) := by
          have h1 : (Nat.testBit val n).toNat ≤ 1 := by cases Nat.testBit val n <;> simp
          have h2 : (Nat.testBit val n).toNat * 2^n ≤ 2^n := by
            calc (Nat.testBit val n).toNat * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right _ h1
                 _ = 2^n := by ring
          calc (Nat.testBit val n).toNat * 2^n +
                (List.ofFn (fun j : Fin n => Nat.testBit val (n - 1 - j.val))).foldl
                  (fun a b => a * 2 + b.toNat) 0
              < 2^n + 2^n := by omega
            _ = 2^(n+1) := by ring

        exact ss_testBit_add_mul_pow_high _ _ h_sum_bound hi3

/-- **Core Property**: vectorToFin of reversed-bit encoding recovers original value.

    **Statement**: For any val : Fin (2^R), encoding val's bits in reversed order
    (MSB first, LSB last) and converting back via vectorToFin produces val.

    **Proof Structure**:
    1. Convert decide form to testBit using shift_mod_decide_eq_testBit
    2. Show foldl result < 2^R using foldl_builds_binary
    3. Apply foldl_testBit_eq_val (binary representation theorem)

    **Why this matters**: computeSeedAtVertex_flat encodes assignment bits this way,
    and emergentBitsToConfig must recover the original value for a3_emergence_realizability.

    **Trust boundary**: Reduces to foldl_testBit_eq_val (binary representation theorem). -/
theorem vectorToFin_reversed_encoding (R : Nat) (val : Fin (2^R)) :
    vectorToFin (Vector.ofFn (fun j : Fin R => decide ((val.val >>> (R - 1 - j.val)) % 2 = 1))) = val := by
  -- Step 1: Convert decide to testBit
  have h_conv : Vector.ofFn (fun j : Fin R => decide ((val.val >>> (R - 1 - j.val)) % 2 = 1)) =
                Vector.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j.val)) := by
    congr 1
    funext j
    exact ss_shift_mod_decide_eq_testBit val.val (R - 1 - j.val)
  rw [h_conv]

  -- Step 2: Unfold vectorToFin
  unfold vectorToFin
  apply Fin.ext

  -- Step 3: Convert Vector.toList to List.ofFn
  have h_toList : (Vector.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j.val))).toList =
                  List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j.val)) := by
    simp only [Vector.toList_ofFn]
  simp only [h_toList]

  -- Step 4: Show foldl result < 2^R (so mod is identity)
  have h_foldl_bound : (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j))).foldl
                        (fun a b => a * 2 + b.toNat) 0 < 2^R := by
    have h := ss_foldl_builds_binary (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j)))
    simp only [List.length_ofFn] at h
    exact h

  have h_mod_id : (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j))).foldl
                   (fun a b => a * 2 + b.toNat) 0 % 2^R =
                  (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j))).foldl
                   (fun a b => a * 2 + b.toNat) 0 := Nat.mod_eq_of_lt h_foldl_bound

  -- Step 5: The two fold functions are the same (Bool.toNat = if b then 1 else 0)
  have h_foldl_eq : (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j))).foldl
                     (fun a b => a * 2 + (if b = true then 1 else 0)) 0 =
                    (List.ofFn (fun j : Fin R => Nat.testBit val.val (R - 1 - j))).foldl
                     (fun a b => a * 2 + b.toNat) 0 := by
    congr 1
    funext a b
    cases b <;> rfl
  rw [h_foldl_eq, h_mod_id]

  -- Step 6: Apply binary representation theorem
  exact ss_foldl_testBit_eq_val val.val val.isLt

/-! ## Pure DAG Structure

These functions extract the L* DAG structure from a CNF formula WITHOUT
planting. They compute the same DAG structure that Plant.lean would build,
but without depending on randomness.

**Key Insight**: The L* reduction from 3-SAT is DETERMINISTIC on φ.
Only the FG digest values depend on r. The DAG structure, emergence ranks,
and emergence matrices are pure functions of φ.

**Implementation Strategy**:
1. Extract pure parts from Plant.lean (buildDAGFromCNF, buildEmergenceRanks)
2. OR reference Plant's pure builders directly if already factored
3. Build LStarInstanceFull WITHOUT FG gates (those need r.gateDigests)
-/

/-- Pure L* DAG structure from CNF formula.

    **Parameterization**: Takes numGates to ensure R computation matches
    planted instances exactly, eliminating type mismatches.

    **Parameters**:
    - φ: CNF formula (determines DAG structure)
    - numGates: Number of FG gates (determines which vertices get FG R values)

    **Computes** (from φ and numGates):
    - DAG structure (vertices, edges)
    - Emergence ranks R_v at each vertex (using R_of_flat - exponential profile)
    - Seed widths
    - Emergence matrices

    **Does NOT include** (depends on r):
    - FG gate digests (those require randomness)
    - Assignment-dependent pool assignments

    **Key Property**: Uses R_of_flat φ numGates to compute R values IDENTICALLY to plant_flat,
    ensuring type consistency (Fin (2^R) indices match perfectly).

    **Precondition**: φ must be non-trivial (φ.nvars > 0), now enforced via explicit hypothesis. -/
noncomputable def lstarStructureFromCNF (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) : LStarInstanceFull :=
  -- Build the multi-level DAG (pure, depends only on φ structure)
  -- Pass numGates to create FG-aware DAG structure
  let dag := Construction.build3SATReductionDAG φ numGates

  -- Compute R values using centralized R_of_flat (exponential profile)
  -- This ensures R values match planted instances exactly, eliminating type mismatches!
  let R_val := LStar.StructuralOWF.Foundations.R_of_flat φ numGates

  -- SeedWidth: recursive definition matching paper specification
  -- seedWidth(v) := Σ(parent widths) + R(v)
  let seedWidth_val := fun v : Fin dag.n =>
    Construction.computeSeedWidth φ numGates R_val v

  { n := φ.nvars
    n_pos := h_nvars_pos  -- From explicit parameter (eliminates axiom!)
    dag := dag
    dagAcyclic := Construction.build3SATReductionDAG_acyclic φ numGates
    seedWidth := seedWidth_val
    R := fun v => R_val v.val
    emergence := fun v =>
      -- Capacity proof: R v ≤ seedWidth v follows from construction
      have hcap : R_val v.val ≤ seedWidth_val v := by
        have h_eq := Construction.seedWidth_satisfies_capacity φ numGates R_val v
        show R_val v.val ≤ Construction.computeSeedWidth φ numGates R_val v
        rw [← h_eq]
        exact Nat.le_add_left _ _
      constructFullRank (R_val v.val) (seedWidth_val v) hcap
    pools := { stride := 1_000_003 }  -- Default pool config (no assignment dependence)
    seedWidth_ok := by
      intro v
      have h_eq := Construction.seedWidth_satisfies_capacity φ numGates R_val v
      show (∑ u ∈ dag.parents v, seedWidth_val u) + R_val v.val ≤ Construction.computeSeedWidth φ numGates R_val v
      -- h_eq states: (∑ u ∈ build3SATReductionDAG.parents v, computeSeedWidth u) + R v.val = computeSeedWidth v
      -- dag = build3SATReductionDAG definitionally, seedWidth_val = computeSeedWidth definitionally
      -- So the LHS and RHS of h_eq match our goal exactly (modulo definitional equality)
      rw [← h_eq]
      -- Now goal is: LHS ≤ LHS, which is reflexive
  }

/-! ## Recursive Seed Computation

Compute the full seed at a vertex using only φ structure and assignment.
This is recursive (depends on parent seeds) but terminates (DAG is acyclic).

**Algorithm**:
```
computeSeed φ a v:
  if v is source (variable):
    return seed from assignment[v]
  else:
    parentSeeds := [computeSeed φ a u for u in parents(v)]
    packedParents := packParents parentSeeds
    emergentBits := emergenceMatrix[v].apply(packedParents)
    return encodeSeed(packedParents, emergentBits)
```

**Key Dependencies** (already exist!):
- LStar.Construction.SeedChain: packParents, encodeSeed ✓
- LStar.Construction.EmergenceMatrix: apply function ✓
- lstarStructureFromCNF: provides DAG structure (stubbed above)
-/

/-- Compute seed at vertex from assignment (recursive).

    **Parameterization**: Takes numGates to use the correctly-typed lstarStructureFromCNF.

    **Parameters**:
    - φ: CNF formula
    - numGates: Number of FG gates (must match the planted instance!)
    - a: Assignment
    - v: Vertex in the DAG

    **Base case**: Source vertices (no parents) - seed from assignment bits
    **Recursive case**: Internal vertices - seed from parent seeds + emergence

    **Termination**: DAG acyclicity ensures recursion terminates.
    Uses vertex index as decreasing measure (parents have smaller indices).

    **Implementation**: Well-founded recursion on v.val using Construction.parents_have_smaller_indices. -/
noncomputable def computeSeedAtVertex (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat) (a : AssignmentInf)
    (v : Fin (lstarStructureFromCNF φ h_nvars_pos numGates).dag.n)
    : Seed ((lstarStructureFromCNF φ h_nvars_pos numGates).seedWidth v) :=
  let L := lstarStructureFromCNF φ h_nvars_pos numGates

  -- Check if this is a source node (no parents)
  if L.dag.parents v = ∅ then
    -- Base case: source node - build seed from assignment bits
    -- Extract R_v bits from assignment to form the seed
    let R_v := L.R v
    let seed_val : Fin (2^R_v) :=
      -- Extract bits from assignment at this vertex
      -- For vertex i, use assignment bits starting at i
      let bits := Vector.ofFn (fun (j : Fin R_v) =>
        -- Use assignment at variable (v.val + j.val) mod nvars
        a ((v.val + j.val) % φ.nvars))
      vectorToFin bits
    -- Convert to Seed of appropriate width, padding with zeros if needed
    ofBits (L.seedWidth v) (fun i =>
      if i.val < R_v then
        ((seed_val.val >>> i.val) % 2 = 1)
      else
        false)
  else
    -- Recursive case: internal node with parents
    -- Build parent history by recursing on each parent
    let parentHistory : ParentHistory L v := fun (u : {u // u ∈ L.dag.parents v}) =>
      -- Recursive call on parent u.val
      -- Termination guaranteed by parents_have_smaller_indices (proved in decreasing_by)
      computeSeedAtVertex φ h_nvars_pos numGates a u.val

    -- Pack parent seeds into a flat bit vector
    let packed := packParents L v parentHistory

    -- Apply emergence matrix to packed parents
    -- The emergence matrix extracts R_v emergent bits from the packed parent data
    let input := ofBits (L.seedWidth v) (fun i =>
      -- Copy bits from packed parents into the input seed
      if h : i.val < parentBits L v then
        packed.get ⟨i.val, h⟩
      else
        false)

    let emergent_seed := EmergenceMatrix.apply (L.emergence v) input

    -- Convert emergent seed value to bit vector
    let emergent_bits : Vector Bool (L.R v) :=
      Vector.ofFn (fun j : Fin (L.R v) =>
        ((emergent_seed.val >>> j.val) % 2 = 1))

    -- Encode parent history + emergent bits into final seed
    encodeSeed L v parentHistory emergent_bits

  termination_by v.val
  decreasing_by
    -- Need to prove: u.val.val < v.val for u ∈ L.dag.parents v
    simp_wf
    -- u.property gives us: u ∈ L.dag.parents v
    -- L.dag = build3SATReductionDAG φ numGates (definitional)
    -- So we have: u ∈ (build3SATReductionDAG φ numGates).parents v
    -- Apply parents_have_smaller_indices to get u.val < v.val
    have h_mem : ↑u ∈ (lstarStructureFromCNF φ h_nvars_pos numGates).dag.parents v := u.property
    -- Unfold L.dag to expose build3SATReductionDAG
    show (u : Fin (lstarStructureFromCNF φ h_nvars_pos numGates).dag.n).val < v.val
    exact Construction.parents_have_smaller_indices φ numGates v u.val h_mem

/-! ## Axiom Verification

These pure computational functions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms assignmentToVector
#print axioms seedToBits
#print axioms vectorToFin
#print axioms extractEmergentBits
#print axioms emergentBitsToConfig
#print axioms lstarStructureFromCNF
#print axioms computeSeedAtVertex

end LStar.StructuralOWF.Foundations
