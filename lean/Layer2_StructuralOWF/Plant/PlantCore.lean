import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer2_StructuralOWF.FrontierGate.VectorHelpers
import Layer3_InformationBounds.Randomness.RanksCore  -- EmergenceProfile and R_of definitions
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig  -- Layer 3 dependency
import Layer1_Construction.Core.EmergenceMatrix
import Layer1_Construction.Core.InstanceOps
import Layer1_Construction.Core.MultiLevelDAG
import Layer1_Construction.Properties.A2_Injectivity
import Layer1_Construction.Properties.A3_Emergence
import Layer1_Construction.Core.OAPEncoding
import Layer0_Foundations.Base.EncodedCNF
import Layer1_Construction.Core.SeedChain

/-! ## PlantCore: Shared Infrastructure for Plant Constructions

**Purpose**: Core utilities and DAG construction shared by plant profiles.

**Main exports**:
- `build3SATReductionDAG`: Constructs the multi-level DAG for 3-SAT to L* reduction
- `mk_emergence_matrix`: Constructs full-rank emergence matrices
- Digest helpers: `resizeDigestGeneral`, `assignmentToDigestN`, `xorDigestN`, etc.

**Used by**:
- **PlantExponential.lean**: Exponential profile (R_v = n, bound 2^n) - PRIMARY PATH for P≠NP proof

**DAG Structure** (depth O(log m) where m = #clauses):
- **Level 0**: Source (1 node) - provides base randomness
- **Level 1**: Variables (n nodes) - one per 3-SAT variable, depends on source
- **Level 2**: Clauses (m nodes) - one per clause, depends on its 3 variables
- **Levels 3+**: Reduction tree (⌈log₂ m⌉ levels) - binary tree combining clauses

**Total depth**: 3 + ⌈log₂ m⌉ = O(log m)

**Trust Boundary**: All definitions and theorems fully proven (no axioms, no sorries).

**Paper**: §3 "Plant Construction" for DAG architecture.

See Layer2_StructuralOWF/Layer2_README.md for Plant function details and FG mechanism.
-/

namespace LStar.StructuralOWF

open LStar
open LStar.Construction.ReductionTree
open LStar.StructuralOWF.Foundations

/-! ## Helper lemmas for stride bound -/

/-- **Helper**: Binary encoding step preserves bounds. -/
private lemma binary_foldl_bound_aux (bits : List Bool) (acc : Nat) (k : Nat)
    (h_acc : acc < 2^k) :
    bits.foldl (fun a b => 2 * a + if b then 1 else 0) acc < 2^(k + bits.length) := by
  induction bits generalizing acc k with
  | nil =>
    simp only [List.length_nil, add_zero, List.foldl_nil]
    exact h_acc
  | cons head tail ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h_new_acc : 2 * acc + (if head then 1 else 0) < 2^(k + 1) := by
      have h_double : 2 * acc < 2 * 2^k := Nat.mul_lt_mul_of_pos_left h_acc (by norm_num : 0 < 2)
      have : 2^(k+1) = 2 * 2^k := by ring
      rw [this]
      by_cases h : head = true
      · simp only [h, ite_true]
        omega
      · simp only [h, ite_false, add_zero]
        exact h_double
    have := ih (2 * acc + (if head then 1 else 0)) (k + 1) h_new_acc
    simp only [add_assoc, add_comm 1] at this
    exact this

/-- **Helper**: Binary encoding via foldl on n bits is bounded by 2^n. -/
private lemma binary_foldl_bound (bits : List Bool) (n : Nat) (h_len : bits.length ≤ n) :
    bits.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0 < 2^n := by
  let k := n - bits.length
  have h_acc : (0 : Nat) < 2^k := by
    apply Nat.zero_lt_of_lt
    apply Nat.one_le_two_pow
  have h_aux := binary_foldl_bound_aux bits 0 k h_acc
  have h_eq : k + bits.length = n := by
    unfold k
    exact Nat.sub_add_cancel h_len
  rw [h_eq] at h_aux
  exact h_aux

-- Import Randomness and Witness from RandomnessTypes
open LStar.StructuralOWF (Randomness Witness)

/-!
## 3-SAT to DAG Reduction (Multi-Level Architecture)

The L* instance is built from a 3-SAT formula φ via a witness-preserving reduction.
The DAG uses a **multi-level structure** matching the paper's O(log n) depth specification.

**DAG Structure** (depth O(log m) where m = #clauses):
- **Level 0**: Source (1 node) - provides base randomness
- **Level 1**: Variables (n nodes) - one per 3-SAT variable, depends on source
- **Level 2**: Clauses (m nodes) - one per clause, depends on its 3 variables
- **Levels 3+**: Reduction tree (⌈log₂ m⌉ levels) - binary tree combining clauses

**Total depth**: 3 + ⌈log₂ m⌉ = O(log m)

**SeedWidth** (non-uniform, level-dependent):
- Level 0: R₀
- Level 1: R₀ + R₁
- Level 2: 3·(R₀ + R₁) + R₂
- Level k: 2·seedWidth(k-1) + R_k

**Growth**: Exponential in depth, but depth is O(log m), so max seedWidth =
O(2^(log m) · R) = O(m · R) which is polynomial.

**Capacity Constraint**: Satisfied by construction via the formula
seedWidth(v) := (Σ u ∈ parents(v): seedWidth(u)) + R(v)

**Witness Preservation**:
- Satisfying assignment a → determines variable node seeds
- Clause nodes verify: decode 3 parent seeds → extract assignments → check clause
- All clauses satisfied → reduction tree propagates success
- φ is SAT ⟺ L* instance has valid witness
-/

/-- Build the multi-level DAG for 3-SAT to L* reduction.

    Delegates to Construction.build3SATReductionDAG. The DAG has logarithmic depth
    in the number of clauses and preserves the satisfiability property:
    a formula is satisfiable if and only if the corresponding L* instance has a witness.

    **FG Bottleneck**: The `numGates` parameter specifies how many FG gates to use.
    Non-FG clauses depend on FG gates, creating the 2^R information-theoretic bottleneck.
    Default: 1 (single-gate architecture for backward compatibility). -/
def build3SATReductionDAG (φ : CNF) (numGates : Nat := 1) : DAG :=
  Construction.build3SATReductionDAG φ numGates

/-- The multi-level 3-SAT reduction DAG is acyclic.

    Acyclicity follows from the level-based topological ordering:
    Source, then Variables, then Clauses, then Reduction tree. -/
theorem build3SATReductionDAG_acyclic (φ : CNF) (numGates : Nat := 1) :
    DAG.isAcyclic (build3SATReductionDAG φ numGates) := by
  unfold build3SATReductionDAG
  exact Construction.build3SATReductionDAG_acyclic φ numGates


/-- Encode an assignment into a dgLen-bit digest vector.

    This creates a seed-locked commitment to the assignment by encoding
    the first dgLen bits of the assignment into a Vector Bool dgLen.
    Used in FG gate digest to achieve plant injectivity WITHOUT leaking
    the witness in public fields like stride.

    For n ≤ dgLen: encodes all n assignment bits (rest padded with false)
    For n > dgLen: encodes first dgLen bits (sufficient for injectivity on those bits) -/
def assignmentToDigestN (dgLen : Nat) (n : Nat) (assignment : AssignmentInf) : Vector Bool dgLen :=
  Vector.ofFn (fun i : Fin dgLen => if h : i.val < n then assignment i.val else false)

/-- Legacy 64-bit version of assignmentToDigest for backward compatibility -/
def assignmentToDigest (n : Nat) (assignment : AssignmentInf) : Vector Bool 64 :=
  assignmentToDigestN 64 n assignment

/-- XOR two dgLen-bit vectors componentwise. -/
def xorDigestN {dgLen : Nat} (v1 v2 : Vector Bool dgLen) : Vector Bool dgLen :=
  Vector.ofFn (fun i => xor (v1.get i) (v2.get i))

/-- Legacy 64-bit version of xorDigest for backward compatibility -/
def xorDigest (v1 v2 : Vector Bool 64) : Vector Bool 64 :=
  xorDigestN v1 v2

/-- Injectivity of assignmentToDigestN: equal digests imply equal assignments on first min(n,dgLen) bits -/
theorem assignmentToDigestN_injective (dgLen n : Nat) (a1 a2 : AssignmentInf)
    (h_eq : assignmentToDigestN dgLen n a1 = assignmentToDigestN dgLen n a2) :
    ∀ i < min n dgLen, a1 i = a2 i := by
  intro i hi
  have hi_dgLen : i < dgLen := Nat.lt_of_lt_of_le hi (Nat.min_le_right n dgLen)
  have hi_n : i < n := Nat.lt_of_lt_of_le hi (Nat.min_le_left n dgLen)
  have h_elem := congrArg (fun v => v.get ⟨i, hi_dgLen⟩) h_eq
  simp only [assignmentToDigestN] at h_elem
  rw [Vector.get_ofFn, Vector.get_ofFn] at h_elem
  simp only [hi_n, ↓reduceDIte] at h_elem
  exact h_elem

/-- Injectivity of assignmentToDigest: equal digests imply equal assignments on first min(n,64) bits -/
theorem assignmentToDigest_injective (n : Nat) (a1 a2 : AssignmentInf)
    (h_eq : assignmentToDigest n a1 = assignmentToDigest n a2) :
    ∀ i < min n 64, a1 i = a2 i := by
  unfold assignmentToDigest at h_eq
  exact assignmentToDigestN_injective 64 n a1 a2 h_eq

/-- Convert a source_len-bit digest to a target_len-bit digest.

    If target_len ≤ source_len, truncate to the first target_len bits.
    If target_len > source_len, pad with zeros on the right.
    This handles the mismatch between digest size and parameterized R values. -/
def resizeDigestGeneral (target_len source_len : Nat) (source : Vector Bool source_len) : Vector Bool target_len :=
  if h : target_len ≤ source_len then
    -- Truncate: take first target_len bits, then cast using min = target_len
    have h_min : min target_len source_len = target_len := Nat.min_eq_left h
    (source.take target_len).cast h_min
  else
    -- Pad: use full source_len bits and append zeros
    have h_sub : source_len + (target_len - source_len) = target_len := Nat.add_sub_cancel' (Nat.le_of_lt (Nat.lt_of_not_le h))
    (source.append (Vector.replicate (target_len - source_len) false)).cast h_sub

/-- Legacy: Convert a fixed 64-bit digest to a parameterized length.

    If target_len ≤ 64, truncate to the first target_len bits.
    If target_len > 64, pad with zeros on the right.
    This handles the mismatch between fixed digest size and parameterized R values. -/
def resizeDigest (target_len : Nat) (source : Vector Bool 64) : Vector Bool target_len :=
  resizeDigestGeneral target_len 64 source

/-- Cast a digest when source and target lengths are equal. -/
def castDigest {source_len target_len : Nat} (h_eq : source_len = target_len) (source : Vector Bool source_len) : Vector Bool target_len :=
  source.cast h_eq

/-- The first bit of resizeDigestGeneral matches the first bit of the source.

    In both truncate and pad cases, bit 0 of the output equals bit 0 of the source. -/
theorem resizeDigestGeneral_preserves_bit_0
    (target_len source_len : Nat)
    (source : Vector Bool source_len)
    (h_target_pos : 0 < target_len)
    (h_source_pos : 0 < source_len) :
    (resizeDigestGeneral target_len source_len source).get ⟨0, h_target_pos⟩ = source.get ⟨0, h_source_pos⟩ := by
  unfold resizeDigestGeneral
  split_ifs with h_le
  · -- Case 1: target_len ≤ source_len (truncate)
    exact Vector.get_zero_take_cast source target_len h_target_pos h_source_pos (Nat.min_eq_left h_le)
  · -- Case 2: target_len > source_len (pad with zeros)
    exact Vector.get_zero_append_cast source (Vector.replicate (target_len - source_len) false) h_source_pos

/-- The first bit of resizeDigest matches the first bit of the source.

    In both truncate and pad cases, bit 0 of the output equals bit 0 of the source. -/
theorem resizeDigest_preserves_bit_0
    (target_len : Nat)
    (source : Vector Bool 64)
    (h_target_pos : 0 < target_len)
    (h_source_bound : 0 < 64 := by decide) :
    (resizeDigest target_len source).get ⟨0, h_target_pos⟩ = source.get ⟨0, h_source_bound⟩ := by
  unfold resizeDigest
  exact resizeDigestGeneral_preserves_bit_0 target_len 64 source h_target_pos h_source_bound

/-- When target_len ≥ source_len, resizeDigestGeneral is injective.

    When padding, the full source is preserved and padded with zeros.
    Equal padded results must have equal sources. -/
theorem resizeDigestGeneral_injective
    (target_len source_len : Nat)
    (h_len : source_len ≤ target_len)
    (v1 v2 : Vector Bool source_len)
    (h_eq : resizeDigestGeneral target_len source_len v1 = resizeDigestGeneral target_len source_len v2) :
    v1 = v2 := by
  apply Vector.ext
  intro (i : Nat) (hi : i < source_len)
  have h_elem := congrArg (fun v => v.get ⟨i, by omega⟩) h_eq
  unfold resizeDigestGeneral at h_elem
  by_cases h_case : target_len ≤ source_len
  case pos =>
    have h_eq_len : target_len = source_len := Nat.le_antisymm h_case h_len
    subst h_eq_len
    -- After subst, source_len is replaced by target_len
    simp only [dif_pos (le_refl target_len)] at h_elem
    have h1 : ((v1.take target_len).cast (Nat.min_eq_left (le_refl target_len))).get ⟨i, by omega⟩ = v1.get ⟨i, hi⟩ := by simp
    have h2 : ((v2.take target_len).cast (Nat.min_eq_left (le_refl target_len))).get ⟨i, by omega⟩ = v2.get ⟨i, hi⟩ := by simp
    rw [h1, h2] at h_elem
    exact h_elem
  case neg =>
    simp only [dif_neg h_case] at h_elem
    have h_sub : source_len + (target_len - source_len) = target_len := Nat.add_sub_cancel' (Nat.le_of_lt (Nat.lt_of_not_le h_case))
    have h1 : ((v1.append (Vector.replicate (target_len - source_len) false)).cast h_sub).get ⟨i, by omega⟩ = v1.get ⟨i, hi⟩ := by
      rw [Vector.get_cast]; simp [Vector.get, Vector.append, hi]
    have h2 : ((v2.append (Vector.replicate (target_len - source_len) false)).cast h_sub).get ⟨i, by omega⟩ = v2.get ⟨i, hi⟩ := by
      rw [Vector.get_cast]; simp [Vector.get, Vector.append, hi]
    rw [h1, h2] at h_elem
    exact h_elem

/-- When target_len ≥ 64, resizeDigest is injective.

    When padding (target_len > 64), the full 64-bit source is preserved and padded with zeros.
    Equal padded results must have equal sources. -/
theorem resizeDigest_injective
    (target_len : Nat)
    (h_len : 64 ≤ target_len)
    (v1 v2 : Vector Bool 64)
    (h_eq : resizeDigest target_len v1 = resizeDigest target_len v2) :
    v1 = v2 := by
  unfold resizeDigest at h_eq
  exact resizeDigestGeneral_injective target_len 64 h_len v1 v2 h_eq

/-- Every Randomness has at least one FG gate digest.

    This follows from the single-gate constraint: r.gateDigests.length = 1. -/
theorem structural_owf_nonempty_gates {nvars : Nat} (r : Randomness nvars) : 0 < r.gateDigests.length := by
  rw [r.h_single_gate]
  decide

def mk_emergence_matrix (R seedWidth : Nat) (h : R ≤ seedWidth) : EmergenceMatrix R seedWidth :=
  LStar.constructFullRank R seedWidth h

end LStar.StructuralOWF
