import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer2_StructuralOWF.Plant.PlantCore
import Layer0_Foundations.Base.CNF
import Layer5_Applications.PvsNP.PrimaryPath.ParametricBitstringBridge

/-! ## EncodingHelpers: Randomness ↔ Bits Round-Trip Lemmas

**Theorems**: `assignment_roundtrip`, `gateDigests_roundtrip`, `structuralBits_roundtrip_take64`.

**Why it matters**: These lemmas certify that the bitstring witness used by `plant_flat`
exactly preserves the assignment, the single FG gate digest, and the first 64 salt bits.
This is the precise data `plant_flat` reads when constructing the planted instance, so
round-tripping them guarantees honest inversion targets in the OWF bridge.

**Proof technique**: Encode randomness as a concatenated vector (assignment ++ digest ++
structural bits), then analyze indices by simple arithmetic. The single-gate constraint
discharges the digest case, while the salt lower bound ensures the 64-bit structural slice
is available.

**Paper reference**: Read-or-x.md §4.1 (randomness layout) and §4.3 (single-gate wiring).

**Dependencies**: Builds on `Layer2_OWF.FrontierGate.RandomnessTypes` for the randomness
structure and feeds `randomness_encoding_plant_equiv` in `OWFBridge.lean` to prove
encoding/decoding preserves planted instances.
-/

namespace LStar.Complexity.StructuralOWFBridge

open LStar LStar.StructuralOWF LStar.StructuralOWF.Foundations
open BitstringBridge
open Classical

/-- Encode randomness to a bit vector. Format: [assignment (n)][gate digest (dgLen)][structural (64)].
    Total size: n + dgLen + 64. -/
def randomnessToBits (n : Nat) (r : Randomness) : Bits (n + r.dgLen + 64) :=
  let gateDigest := r.gateDigests.head (by
    intro h_empty; have := r.h_single_gate; simp [h_empty] at this)
  let structBits := r.structuralBits.take 64
  have h_struct_len : structBits.length = 64 := by
    have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
    simp [structBits, List.length_take, h_min]
  Vector.ofFn fun idx : Fin (n + r.dgLen + 64) =>
    if h_assign : idx.val < n then
      r.assignment idx.val
    else if h_gate : idx.val < n + r.dgLen then
      let pos : Nat := idx.val - n
      have h_pos_lt : pos < r.dgLen := by omega
      gateDigest.get ⟨pos, h_pos_lt⟩
    else
      let pos : Nat := idx.val - (n + r.dgLen)
      have h_pos_lt64 : pos < 64 := by omega
      have h_pos_struct : pos < structBits.length := by
        simp [h_struct_len, h_pos_lt64]
      structBits.get ⟨pos, h_pos_struct⟩

/-- Decode bits to randomness. The dgLen parameter specifies the digest length. -/
def bitsToRandomness (n dgLen : Nat) (h_dgLen_pos : dgLen > 0) (w : Bits (n + dgLen + 64)) : Randomness where
  dgLen := dgLen
  h_dgLen_pos := h_dgLen_pos
  assignment i := if h : i < n then w.get ⟨i, by omega⟩ else false
  gateDigests := [Vector.ofFn fun i : Fin dgLen => w.get ⟨n + i.val, by omega⟩]
  structuralBits := List.ofFn fun (i : Fin 64) => w.get ⟨n + dgLen + i.val, by omega⟩
  h_sufficient_salts := by simp
  h_single_gate := by rfl

/-- Specialized version for flat profile where dgLen = 64.
    Returns Bits (n + 128) directly, avoiding type coercion overhead. -/
def randomnessToBits_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64) : Bits (n + 128) :=
  let gateDigest := r.gateDigests.head (by
    intro h_empty; have := r.h_single_gate; simp [h_empty] at this)
  let structBits := r.structuralBits.take 64
  have h_struct_len : structBits.length = 64 := by
    have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
    simp [structBits, List.length_take, h_min]
  Vector.ofFn fun idx : Fin (n + 128) =>
    if h_assign : idx.val < n then
      r.assignment idx.val
    else if h_gate : idx.val < n + 64 then
      let pos : Nat := idx.val - n
      have h_pos_lt : pos < 64 := by omega
      have h_pos_dgLen : pos < r.dgLen := by rw [h_dgLen]; exact h_pos_lt
      gateDigest.get ⟨pos, h_pos_dgLen⟩
    else
      let pos : Nat := idx.val - (n + 64)
      have h_pos_lt64 : pos < 64 := by omega
      have h_pos_struct : pos < structBits.length := by
        simp [h_struct_len, h_pos_lt64]
      structBits.get ⟨pos, h_pos_struct⟩

/-- Assignment roundtrip for flat profile (dgLen = 64). -/
theorem assignment_roundtrip_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64)
    (φ : CNF) (h_nvars_eq : φ.nvars = n) :
    ∀ i < φ.nvars,
      (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).assignment i = r.assignment i := by
  intro i h_i
  have h_i_lt_n : i < n := by rw [← h_nvars_eq]; exact h_i
  simp only [bitsToRandomness, randomnessToBits_flat, Vector.get_ofFn]
  simp [h_i_lt_n]

/-! ### Round-trip Properties (Fully Parametric) -/

theorem assignment_roundtrip (n : Nat) (r : Randomness) :
    ∀ i < n,
      (bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)).assignment i = r.assignment i := by
  intro i h_i
  simp only [bitsToRandomness, randomnessToBits, Vector.get_ofFn]
  simp [h_i]

private lemma extract_singleton {α : Type*} (l : List α) (h : l.length = 1) :
    ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons head tail =>
    cases tail with
    | nil => exact ⟨head, rfl⟩
    | cons _ _ => simp at h

theorem gateDigests_roundtrip (n : Nat) (r : Randomness) :
    (bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)).gateDigests = r.gateDigests := by
  obtain ⟨g, hg⟩ := extract_singleton r.gateDigests r.h_single_gate
  -- LHS is [Vector.ofFn fun i => ...] and RHS is [g] (by hg)
  -- Prove via list extensionality
  rw [hg]
  -- Goal: [reconstructed_vector] = [g]
  apply List.ext_get
  · -- Length equality: both have length 1
    simp only [bitsToRandomness, List.length_singleton]
  · intro i hi_left hi_right
    simp only [List.length_singleton] at hi_left hi_right
    have h_i_zero : i = 0 := Nat.lt_one_iff.mp hi_left
    subst h_i_zero
    -- Show the 0th element of each list are equal
    simp only [List.get_eq_getElem, List.getElem_singleton]
    -- Goal: reconstructed_vector = g
    apply Vector.ext
    intro j h_j
    -- h_j : j < r.dgLen (since bitsToRandomness sets dgLen := r.dgLen)
    simp only [bitsToRandomness] at h_j
    simp only [bitsToRandomness, randomnessToBits, Vector.get_ofFn]
    -- Goal: [Vector.ofFn fun i => ...][0][j] = g[j]
    -- Simplify [x][0] to x
    simp only [List.getElem_singleton]
    -- Now simplify Vector.ofFn indexing to expose the if-then-else
    simp only [Vector.getElem_ofFn]
    -- Goal now has the if-then-else at top level
    -- Since j < r.dgLen, we have ¬(n + j < n) and (n + j < n + r.dgLen)
    have h1 : ¬(n + j < n) := by omega
    have h2 : n + j < n + r.dgLen := by omega
    -- Simplify the nested if-then-else using our hypotheses
    simp only [h1, dif_neg, not_false_eq_true]
    simp only [h2, dif_pos]
    -- Goal: gateDigest.get ⟨j, _⟩ = g.get ⟨j, h_j⟩
    -- Use hg to simplify r.gateDigests.head to g
    simp only [hg, List.head_cons]
    -- Now: g.get ⟨n + j - n, _⟩ = g.get ⟨j, h_j⟩
    -- Simplify n + j - n = j
    simp only [Nat.add_sub_cancel_left]
    -- g.get ⟨j, _⟩ = g[j] is definitional
    rfl

theorem structuralBits_roundtrip_take64 (n : Nat) (r : Randomness) :
    (bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)).structuralBits.take 64 =
    r.structuralBits.take 64 := by
  simp only [bitsToRandomness, randomnessToBits]
  apply List.ext_get
  · have h_len : (r.structuralBits.take 64).length = 64 := by
      have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
      simp [List.length_take, h_min]
    simp [h_len]
  · intro i hi_left hi_right
    have h_len : (r.structuralBits.take 64).length = 64 := by
      have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
      simp [List.length_take, h_min]
    have h_i : i < 64 := by simp [h_len] at hi_right; exact hi_right
    simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn, Vector.get_ofFn]
    have h1 : ¬(n + r.dgLen + i < n) := by omega
    have h2 : ¬(n + r.dgLen + i < n + r.dgLen) := by omega
    simp [h1, h2]

/-! ### Flat Profile Round-trip Properties (dgLen = 64) -/

/-- Gate digests length preservation for flat profile. -/
theorem gateDigests_length_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64) :
    (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).gateDigests.length =
    r.gateDigests.length := by
  simp only [bitsToRandomness, List.length_singleton, r.h_single_gate]

/-- Helper: r.gateDigests is non-empty (from h_single_gate). -/
theorem randomness_gateDigests_nonempty (r : Randomness) : r.gateDigests ≠ [] := by
  intro h; have := r.h_single_gate; simp [h] at this

/-- Gate digest bit equality for flat profile.
    Shows that decoded digest bits equal original digest bits (accounting for dgLen). -/
theorem gateDigest_bits_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64)
    (j : Nat) (hj : j < 64) :
    ((bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).gateDigests.head
      (by simp only [bitsToRandomness]; exact List.cons_ne_nil _ _)).get ⟨j, hj⟩ =
    (r.gateDigests.head (randomness_gateDigests_nonempty r)).get
      ⟨j, h_dgLen ▸ hj⟩ := by
  simp only [bitsToRandomness, randomnessToBits_flat, Vector.get_ofFn, List.head_cons]
  -- Now we have: if n + j < n then ... else if n + j < n + 64 then (gateDigest.get ...) else ...
  -- Since j < 64, we have ¬(n + j < n) and n + j < n + 64
  split_ifs with h1 h2
  · -- Case: n + j < n (impossible)
    omega
  · -- Case: n + j < n + 64 (true since j < 64)
    simp only [Nat.add_sub_cancel_left]
  · -- Case: ¬(n + j < n + 64) (impossible since j < 64)
    omega

/-- Helper: transport commutes with Vector element access. -/
private theorem vector_get_transport {α : Type*} {n m : Nat} (v : Vector α n) (h : n = m)
    (i : Nat) (hi_m : i < m) :
    (h ▸ v).get ⟨i, hi_m⟩ = v.get ⟨i, h ▸ hi_m⟩ := by
  subst h
  rfl

/-- Helper: transport on a singleton list produces singleton of transported element. -/
private theorem list_singleton_transport {α : Nat → Type*} {n m : Nat} (x : α n) (h : n = m) :
    (h ▸ [x] : List (α m)) = [h ▸ x] := by
  subst h
  rfl

/-- resizeDigestGeneral commutes with transport on source vector.
    When source_len = fixed_len, we can transport the source and get the same result. -/
theorem resizeDigestGeneral_transport (target_len fixed_len source_len : Nat)
    (h_eq : source_len = fixed_len) (source : Vector Bool source_len) :
    resizeDigestGeneral target_len source_len source =
    resizeDigestGeneral target_len fixed_len (h_eq ▸ source) := by
  subst h_eq
  rfl

/-- resizeDigestGeneral produces equal results for HEq sources.
    This is the key lemma for proving FG config equality with transported gateDigests. -/
theorem resizeDigestGeneral_heq_source (target_len : Nat) {s1 s2 : Nat} (hs : s1 = s2)
    (v1 : Vector Bool s1) (v2 : Vector Bool s2) (hv : v1 = hs ▸ v2) :
    resizeDigestGeneral target_len s1 v1 = resizeDigestGeneral target_len s2 v2 := by
  subst hs
  simp only [Eq.rec_eq_cast, cast_eq] at hv
  subst hv
  rfl

/-- resizeDigestGeneral on transported gateDigests.get equals resizeDigestGeneral on original.
    Key lemma: when r'.gateDigests = h_dgLen ▸ r.gateDigests, the resizeDigestGeneral outputs match.

    **Note**: We don't need list_get_transport as a separate lemma. Instead, we prove the equality
    directly by substituting and using rfl. -/
theorem resizeDigestGeneral_of_transported_list_get (target_len : Nat) {s1 s2 : Nat}
    (hs : s1 = s2) (l1 : List (Vector Bool s2)) (l2 : List (Vector Bool s1))
    (hl : l1 = hs ▸ l2) (i : Nat) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    resizeDigestGeneral target_len s2 (l1.get ⟨i, hi1⟩) =
    resizeDigestGeneral target_len s1 (l2.get ⟨i, hi2⟩) := by
  subst hs
  subst hl
  rfl

/-- Gate digests list equality for flat profile (dgLen = 64).

    **Proof strategy**: Both sides are singleton lists. Use element-wise equality
    via `gateDigest_bits_flat` and helper lemmas for transport on vectors.
-/
theorem gateDigests_roundtrip_flat_eq (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64) :
    (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).gateDigests =
    (h_dgLen ▸ r.gateDigests) := by
  -- Both sides have type List (Vector Bool 64)
  -- Extract the singleton structure of r.gateDigests
  have h_single : r.gateDigests.length = 1 := r.h_single_gate
  obtain ⟨gd, hgd⟩ := List.length_eq_one_iff.mp h_single

  -- Rewrite RHS using singleton transport lemma
  have h_rhs : (h_dgLen ▸ r.gateDigests : List (Vector Bool 64)) = [h_dgLen ▸ gd] := by
    rw [hgd]; exact list_singleton_transport gd h_dgLen
  rw [h_rhs]

  -- LHS is definitionally [decoded_vector]
  show [Vector.ofFn fun i : Fin 64 =>
      (randomnessToBits_flat n r h_dgLen).get ⟨n + i.val, by omega⟩] = [h_dgLen ▸ gd]

  -- Use List.singleton_eq_singleton and Vector extensionality
  rw [List.cons_eq_cons]
  constructor
  · -- Main part: decoded_vector = h_dgLen ▸ gd
    apply Vector.ext
    intro i hi
    -- Goal: decoded_vector[i] = (h_dgLen ▸ gd)[i]

    -- Use gateDigest_bits_flat which tells us:
    -- (bitsToRandomness ...).gateDigests.head[i] = r.gateDigests.head[i] (with transport on index)
    have h_bits := gateDigest_bits_flat n r h_dgLen i hi

    -- Unfold bitsToRandomness definition in h_bits to get the raw form
    simp only [bitsToRandomness, List.head_cons, Vector.get_ofFn] at h_bits

    -- r.gateDigests.head = gd via hgd
    simp only [hgd, List.head_cons] at h_bits
    -- Now h_bits: Vector.get (randomnessToBits_flat ...) ⟨n + i, ...⟩ = gd.get ⟨i, h_dgLen ▸ hi⟩

    -- RHS: (h_dgLen ▸ gd)[i] = gd[h_dgLen ▸ i] by vector_get_transport
    have h_transport := vector_get_transport gd h_dgLen i hi

    -- Simplify LHS: (Vector.ofFn f)[i] = f ⟨i, hi⟩ = Vector.get ... ⟨n + i, ...⟩
    simp only [Vector.getElem_ofFn]
    -- Now goal: Vector.get (randomnessToBits_flat ...) ⟨n + i, ...⟩ = (h_dgLen ▸ gd)[i]

    -- Combine: LHS = gd.get ⟨i, h_dgLen ▸ hi⟩ = (h_dgLen ▸ gd).get ⟨i, hi⟩ = RHS
    rw [h_bits, ← h_transport]
    -- .get and [] are definitionally equal
    rfl
  · rfl  -- [] = []

/-- Structural bits roundtrip (take 64) for flat profile (dgLen = 64). -/
theorem structuralBits_roundtrip_take64_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64) :
    (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).structuralBits.take 64 =
    r.structuralBits.take 64 := by
  simp only [bitsToRandomness, randomnessToBits_flat]
  apply List.ext_get
  · have h_len : (r.structuralBits.take 64).length = 64 := by
      have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
      simp [List.length_take, h_min]
    simp [h_len]
  · intro i hi_left hi_right
    have h_len : (r.structuralBits.take 64).length = 64 := by
      have h_min : Nat.min 64 r.structuralBits.length = 64 := min_eq_left r.h_sufficient_salts
      simp [List.length_take, h_min]
    have h_i : i < 64 := by simp [h_len] at hi_right; exact hi_right
    simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn, Vector.get_ofFn]
    have h1 : ¬(n + 64 + i < n) := by omega
    have h2 : ¬(n + 64 + i < n + 64) := by omega
    simp [h1, h2]

/-- The dgLen of the roundtrip decoded Randomness is 64 for flat profile. -/
theorem dgLen_roundtrip_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64) :
    (bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).dgLen = 64 := rfl

/-- Helper: bitsToRandomness always has non-empty gateDigests. -/
theorem bitsToRandomness_gateDigests_nonempty (n dgLen : Nat) (h : dgLen > 0) (w : Bits (n + dgLen + 64)) :
    (bitsToRandomness n dgLen h w).gateDigests ≠ [] := by
  simp only [bitsToRandomness, ne_eq]
  exact List.cons_ne_nil _ _

/-- Gate digests head bit equality for flat profile.
    The first (and only) gate digest is recovered bit-for-bit.
    Uses the existing gateDigest_bits_flat lemma with a simpler interface. -/
theorem gateDigest_head_eq_flat (n : Nat) (r : Randomness) (h_dgLen : r.dgLen = 64)
    (j : Nat) (hj : j < 64) :
    ((bitsToRandomness n 64 (by omega) (randomnessToBits_flat n r h_dgLen)).gateDigests.head
      (bitsToRandomness_gateDigests_nonempty n 64 (by omega) _)).get ⟨j, hj⟩ =
    (r.gateDigests.head (randomness_gateDigests_nonempty r)).get
      ⟨j, h_dgLen ▸ hj⟩ :=
  gateDigest_bits_flat n r h_dgLen j hj

/-- The dgLen of the roundtrip decoded Randomness equals r.dgLen when using general encoding. -/
theorem dgLen_roundtrip_general (n : Nat) (r : Randomness) :
    (bitsToRandomness n r.dgLen r.h_dgLen_pos (randomnessToBits n r)).dgLen = r.dgLen := rfl

#print axioms assignment_roundtrip
#print axioms gateDigests_roundtrip
#print axioms structuralBits_roundtrip_take64
#print axioms gateDigests_length_flat
#print axioms gateDigest_bits_flat
#print axioms structuralBits_roundtrip_take64_flat

end LStar.Complexity.StructuralOWFBridge
