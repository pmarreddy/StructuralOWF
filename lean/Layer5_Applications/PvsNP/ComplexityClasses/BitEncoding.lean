import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer5_Applications.PvsNP.ComplexityClasses.ListHelpers
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log

/-! ## BitEncoding: Canonical Bit-Level Encodings (0 axioms)

**Purpose**: Provide canonical bit-level encodings for types with round-trip properties.

**Design**:
- encode : α → List Bool - Map value to bit sequence
- decode : List Bool → Option α - Parse bit sequence back to value
- len_bound : ∀ a, (encode a).length ≤ C * (size a + 1)^k - Polynomial length bound
- decode_encode : ∀ a, decode (encode a) = some a - Round-trip correctness
- blank_consistent : Encoding respects blank/default values

**Pair Encoding**: Compositional concatenation-based product encoding:
- encode_pair (a, b) := encode a ++ encode b
- decode_pair splits list and decodes components
- Polynomial bounds are additive

**Usage**: Enables concrete TM encoding instantiation for ComplexityClasses.lean.

**Trust Boundary**: 0 axioms (pure interface definition and compositional construction)
-/

namespace LStar.Complexity

open Sized

/-- Helper: If filterMap produces at least one element, head? of append equals head?. -/
private lemma filterMap_head?_append_ne_nil {β : Type} (l1 l2 : List β)
    (h : l1 ≠ []) : (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => contradiction
  | cons hd tl => rfl

/-- Helper: filterMap of range is empty iff f returns none on all indices. -/
private lemma filterMap_range_eq_nil {β : Type} (f : Nat → Option β) (n : Nat) :
    (List.range n).filterMap f = [] ↔ ∀ i, i < n → f i = none := by
  constructor
  · intro h_empty i hi
    by_contra h_some
    push_neg at h_some
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists.mp h_some
    have hmem : z ∈ (List.range n).filterMap f := List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, hz.symm⟩
    rw [h_empty] at hmem
    simp at hmem
  · intro h_all_none
    induction n with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      rw [ih (fun i hi => h_all_none i (Nat.lt_trans hi (Nat.lt_succ_self m)))]
      rw [h_all_none m (Nat.lt_succ_self m)]
      simp

/-- Helper: filterMap of range is non-empty if f succeeds on some index. -/
private lemma filterMap_range_ne_nil {β : Type} (f : Nat → Option β) (n : Nat) (k : Nat)
    (h_k : k < n) (y : β) (h_success : f k = some y) :
    (List.range n).filterMap f ≠ [] := by
  intro h_empty
  rw [filterMap_range_eq_nil] at h_empty
  have := h_empty k h_k
  rw [h_success] at this
  exact Option.noConfusion this

/-- Helper: If f succeeds at index k and fails for all earlier indices, filterMap head? = some y.
    Key lemma for proving pair encoding correctness. -/
private lemma filterMap_head?_first_success {β : Type} (f : Nat → Option β)
    (k : Nat) (y : β) (n : Nat)
    (h_k_bound : k ≤ n)
    (h_success : f k = some y)
    (h_earlier_fail : ∀ j, j < k → f j = none) :
    ((List.range (n + 1)).filterMap f).head? = some y := by
  -- Induction on n, handling cases based on k
  induction n with
  | zero =>
    -- n = 0 means k = 0 by h_k_bound
    have h_k_zero : k = 0 := Nat.le_zero.mp h_k_bound
    subst h_k_zero
    simp only [List.range_succ, List.range_zero, List.nil_append, List.filterMap_cons,
               List.filterMap_nil, h_success, List.head?_cons]
  | succ m ih =>
    -- range(m + 2) = range(m + 1) ++ [m + 1]
    rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    cases Nat.lt_or_eq_of_le h_k_bound with
    | inl h_k_lt =>
      -- k < m + 1, so k ≤ m. Use IH: filterMap of range(m+1) has head some y
      have h_k_le_m : k ≤ m := Nat.lt_succ_iff.mp h_k_lt
      have h_prefix_nonempty : (List.range (m + 1)).filterMap f ≠ [] :=
        filterMap_range_ne_nil f (m + 1) k (Nat.lt_succ_of_le h_k_le_m) y h_success
      rw [filterMap_head?_append_ne_nil _ _ h_prefix_nonempty]
      exact ih h_k_le_m
    | inr h_k_eq =>
      -- k = m + 1, so f fails on 0..m, succeeds at m+1
      subst h_k_eq
      have h_prefix_empty : (List.range (m + 1)).filterMap f = [] := by
        rw [filterMap_range_eq_nil]
        intro i hi
        exact h_earlier_fail i hi
      rw [h_prefix_empty, List.nil_append, h_success]
      simp

/-- Canonical bit-level encoding with round-trip property.

**Interface**:
- encode maps values to finite bit sequences
- decode inverts encoding (Option for error handling)
- Polynomial overhead in encoding length
- Round-trip correctness: decode ∘ encode = some

**Blank handling**: The blank value has a designated bit-pattern (blank_bits) that:
- Correctly encodes/decodes the blank value
- Is prefix-free with respect to all non-blank encodings
This allows TM tape compatibility while preserving prefix-freedom.
-/
structure BitEncoding (α : Type) [Sized α] where
  /-- Encode value to bit sequence. -/
  encode : α → List Bool
  /-- Encoding length polynomial bound constant. -/
  C_len : Nat
  /-- Encoding length polynomial bound exponent. -/
  k_len : Nat
  /-- Encoding length is polynomially bounded by input size. -/
  len_bound : ∀ a, (encode a).length ≤ C_len * (size a + 1) ^ k_len
  /-- Decode bit sequence to value (Option for parse errors). -/
  decode : List Bool → Option α
  /-- Round-trip correctness: encoding is invertible. -/
  decode_encode : ∀ a, decode (encode a) = some a
  /-- Decode exactness: successful decodes only accept properly encoded values.
      This ensures concatenation-based pair encoding is unambiguous. -/
  decode_exact : ∀ bits x, decode bits = some x → bits = encode x
  /-- Encoding non-emptiness: every value has a non-empty encoding.
      This ensures decode [] = none (critical for pair encoding uniqueness). -/
  encode_nonempty : ∀ a, 0 < (encode a).length

  /-- No-confusion property: if a bitstring decodes successfully, its non-empty proper prefixes don't.
      This ensures pair encoding uniqueness: split points are unambiguous. -/
  no_prefix_confusion : ∀ bits x k,
    decode bits = some x → 0 < k → k < bits.length → decode (bits.take k) = none
  /-- Blank value (for TM tape compatibility). -/
  blank : α
  /-- The designated bit-pattern for the blank value. -/
  blank_bits : List Bool
  /-- Blank encodes to its designated bit-pattern. -/
  blank_encoding : encode blank = blank_bits
  /-- Blank decodes correctly. -/
  blank_decode : decode blank_bits = some blank

/-- Empty bitstring does not decode (derived from encode_nonempty and decode_exact).
    Key lemma for fixing pair encoding edge cases. -/
theorem BitEncoding.decode_nil_none {α : Type} [Sized α] (enc : BitEncoding α) :
    enc.decode [] = none := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp h
  have h_exact := enc.decode_exact [] x hx.symm
  have h_len : (enc.encode x).length = 0 := by simp [← h_exact]
  have h_pos := enc.encode_nonempty x
  omega

/-- Extended encoding doesn't decode: decode (encode a ++ extra) = none for non-empty extra.
    This follows from no_prefix_confusion: if it decoded to a', then encode a' = encode a ++ extra,
    making encode a a proper prefix of encode a', which contradicts no_prefix_confusion on a'. -/
theorem BitEncoding.decode_extend_none {α : Type} [Sized α] (enc : BitEncoding α)
    (a : α) (extra : List Bool) (h_extra : extra.length > 0) :
    enc.decode (enc.encode a ++ extra) = none := by
  by_contra h
  push_neg at h
  obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists.mp h
  -- From decode succeeding, get the structure
  have h_eq := enc.decode_exact (enc.encode a ++ extra) a' ha'.symm
  -- h_eq: encode a ++ extra = encode a'
  -- So encode a is a proper prefix of encode a' (since extra is non-empty)
  have h_len_a : (enc.encode a).length < (enc.encode a').length := by
    rw [← h_eq]
    simp only [List.length_append]
    omega
  -- Apply no_prefix_confusion to a': (encode a').take (len encode a) should not decode
  -- But (encode a').take (len encode a) = encode a (from h_eq)
  have h_take : (enc.encode a').take (enc.encode a).length = enc.encode a := by
    rw [← h_eq]
    rw [List.take_append_of_le_length]
    · simp
    · simp
  have h_pos : 0 < (enc.encode a).length := enc.encode_nonempty a
  have h_none := enc.no_prefix_confusion (enc.encode a') a' (enc.encode a).length
                   (enc.decode_encode a') h_pos h_len_a
  -- h_none: decode ((encode a').take (len encode a)) = none
  rw [h_take] at h_none
  -- But decode (encode a) = some a by decode_encode
  have h_some := enc.decode_encode a
  rw [h_some] at h_none
  exact Option.noConfusion h_none

/-- Pair encoding by concatenation.

**Construction**: encode_pair (a, b) = encode_α a ++ encode_β b

**Polynomial bound**: len(pair) ≤ len(a) + len(b) ≤ C_α·(|a|+1)^k_α + C_β·(|b|+1)^k_β
  Set C_pair = C_α + C_β, k_pair = max(k_α, k_β) to get polynomial bound.

**Round-trip**: decode_pair splits at length boundary and decodes components.
-/
def BitEncoding.pair {α β : Type} [Sized α] [Sized β]
    (enc_α : BitEncoding α) (enc_β : BitEncoding β) :
    BitEncoding (α × β) where
  encode := fun ⟨a, b⟩ => enc_α.encode a ++ enc_β.encode b

  -- Polynomial bounds: additive composition
  C_len := enc_α.C_len + enc_β.C_len
  k_len := max enc_α.k_len enc_β.k_len

  len_bound := fun ⟨a, b⟩ => by
    simp only [List.length_append]
    have h_a := enc_α.len_bound a
    have h_b := enc_β.len_bound b
    -- Goal: len(a) + len(b) ≤ (C_α + C_β) * (size(a,b) + 1)^max(k_α,k_β)
    -- Pair size: size (a,b) = size a + size b (standard definition)
    have h_size : size (a, b) = size a + size b := rfl
    -- Upper bound each component by max exponent
    have h_a_max : enc_α.C_len * (size a + 1) ^ enc_α.k_len ≤
                   enc_α.C_len * (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
      apply Nat.mul_le_mul_left
      -- Need: (size a + 1)^k_α ≤ (size a + size b + 1)^max(k_α, k_β)
      -- Step 1: Increase base (size a + 1) ≤ (size a + size b + 1)
      -- Step 2: Then handle exponent k_α ≤ max(k_α, k_β)
      calc (size a + 1) ^ enc_α.k_len
        _ ≤ (size a + size b + 1) ^ enc_α.k_len := by
          apply Nat.pow_le_pow_left; omega
        _ ≤ (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
          apply Nat.pow_le_pow_right; omega; omega
    have h_b_max : enc_β.C_len * (size b + 1) ^ enc_β.k_len ≤
                   enc_β.C_len * (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
      apply Nat.mul_le_mul_left
      -- Similar reasoning for b component
      calc (size b + 1) ^ enc_β.k_len
        _ ≤ (size a + size b + 1) ^ enc_β.k_len := by
          apply Nat.pow_le_pow_left; omega
        _ ≤ (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
          apply Nat.pow_le_pow_right; omega; omega
    calc (enc_α.encode a).length + (enc_β.encode b).length
      _ ≤ enc_α.C_len * (size a + 1) ^ enc_α.k_len + enc_β.C_len * (size b + 1) ^ enc_β.k_len := by
        exact Nat.add_le_add h_a h_b
      _ ≤ enc_α.C_len * (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) +
          enc_β.C_len * (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
        exact Nat.add_le_add h_a_max h_b_max
      _ = (enc_α.C_len + enc_β.C_len) * (size a + size b + 1) ^ (max enc_α.k_len enc_β.k_len) := by
        ring
      _ = (enc_α.C_len + enc_β.C_len) * (size (a, b) + 1) ^ (max enc_α.k_len enc_β.k_len) := by
        rw [h_size]

  decode := fun bits => do
    -- Decode by trying all split points (exhaustive search)
    -- Production implementations would use length prefixes
    let splits := List.range (bits.length + 1)
    let results := splits.filterMap fun split_pos => do
      let bits_a := bits.take split_pos
      let bits_b := bits.drop split_pos
      let a ← enc_α.decode bits_a
      let b ← enc_β.decode bits_b
      return (a, b)
    results.head?

  decode_encode := fun ⟨a, b⟩ => by
    -- Use filterMap_head?_first_success helper
    -- Goal: decode (encode (a, b)) = some (a, b)
    -- encode (a, b) = enc_α.encode a ++ enc_β.encode b
    -- The correct split position is k = (enc_α.encode a).length
    let bits := enc_α.encode a ++ enc_β.encode b
    let k := (enc_α.encode a).length
    let n := bits.length

    -- Define the split function
    let f : Nat → Option (α × β) := fun split_pos => do
      let bits_a := bits.take split_pos
      let bits_b := bits.drop split_pos
      let a' ← enc_α.decode bits_a
      let b' ← enc_β.decode bits_b
      return (a', b')

    -- Show k ≤ n
    have h_k_bound : k ≤ n := by
      simp only [k, n, bits, List.length_append]
      omega

    -- Show f k = some (a, b)
    have h_success : f k = some (a, b) := by
      simp only [f, k, bits]
      have h_take : (enc_α.encode a ++ enc_β.encode b).take (enc_α.encode a).length = enc_α.encode a := by
        simp [List.take_append]
      have h_drop : (enc_α.encode a ++ enc_β.encode b).drop (enc_α.encode a).length = enc_β.encode b := by
        simp [List.drop_append]
      simp only [h_take, h_drop, enc_α.decode_encode, enc_β.decode_encode]
      rfl

    -- Show all j < k fail: by no_prefix_confusion, proper prefixes don't decode
    have h_earlier_fail : ∀ j, j < k → f j = none := by
      intro j h_j_lt
      simp only [f, bits]
      -- bits.take j is a proper prefix of enc_α.encode a ++ enc_β.encode b
      -- We need: enc_α.decode (bits.take j) = none
      -- j < k = len(enc_α.encode a)
      have h_j_lt_len_a : j < (enc_α.encode a).length := h_j_lt
      -- So bits.take j = (enc_α.encode a).take j, a proper prefix
      have h_take_eq : (enc_α.encode a ++ enc_β.encode b).take j = (enc_α.encode a).take j := by
        rw [List.take_append]
        have h_min : min j (enc_α.encode a).length = j := Nat.min_eq_left (Nat.le_of_lt h_j_lt_len_a)
        simp [h_min]
        have h_zero : j - (enc_α.encode a).length = 0 := by omega
        simp [h_zero]
      rw [h_take_eq]
      -- (enc_α.encode a).take j is a proper prefix (j < len)
      -- By no_prefix_confusion, proper prefixes don't decode if j > 0
      by_cases h_j_pos : j > 0
      · -- j > 0, proper non-empty prefix
        have h_prefix_none : enc_α.decode ((enc_α.encode a).take j) = none := by
          exact enc_α.no_prefix_confusion (enc_α.encode a) a j
            (enc_α.decode_encode a) h_j_pos h_j_lt_len_a
        simp [h_prefix_none]
      · -- j = 0, empty prefix
        push_neg at h_j_pos
        have h_j_zero : j = 0 := Nat.le_zero.mp h_j_pos
        rw [h_j_zero]
        simp only [List.take_zero]
        -- Need to show that either decode [] = none OR decode of the drop fails
        -- Case split on whether enc_α.decode [] succeeds
        cases h_dec_a : enc_α.decode ([] : List Bool) with
        | none => simp [h_dec_a]
        | some a' =>
          -- If decode [] = some a', then by decode_exact, [] = encode a'
          have h_eq := enc_α.decode_exact [] a' h_dec_a
          -- Now check if enc_β.decode (bits.drop 0) succeeds
          -- bits.drop 0 = bits = enc_α.encode a ++ enc_β.encode b
          simp only [List.drop_zero]
          -- If enc_β.decode (enc_α.encode a ++ enc_β.encode b) = some b'
          -- then by decode_exact: enc_α.encode a ++ enc_β.encode b = enc_β.encode b'
          cases h_dec_b : enc_β.decode (enc_α.encode a ++ enc_β.encode b) with
          | none => simp [h_dec_a, h_dec_b]
          | some b' =>
            -- From decode_exact: enc_α.encode a ++ enc_β.encode b = enc_β.encode b'
            have h_eq_b := enc_β.decode_exact _ _ h_dec_b
            -- From h_eq: [] = enc_α.encode a'
            -- Also enc_α.decode (enc_α.encode a) = some a by decode_encode
            -- From decode_exact: enc_α.encode a = enc_α.encode a (trivial)
            -- But h_eq says encode a' = [], so enc_α.encode a' is empty
            -- This means a' is encodable to empty string
            -- And enc_β.encode b' = enc_α.encode a ++ enc_β.encode b
            -- The first component enc_α.encode a is non-empty (j < len(encode a) with j=0 < len)
            -- means len(encode a) > 0
            -- So enc_β.encode b' has length > len(enc_β.encode b) (since enc_α.encode a is non-empty)
            -- Contradiction with len_bound... actually not directly
            -- Simpler: enc_β.encode b' = enc_α.encode a ++ enc_β.encode b
            -- If enc_α.encode a is non-empty, then enc_β.encode b' starts with enc_α.encode a
            -- But b' should encode to something that decodes back to b'
            -- Actually, we have enc_β.decode (enc_β.encode b') = some b' (by decode_encode)
            -- And enc_β.encode b' = enc_α.encode a ++ enc_β.encode b
            -- So enc_β.decode (enc_α.encode a ++ enc_β.encode b) = some b'
            -- Which is exactly h_dec_b! So this is consistent.
            -- The issue is: f 0 would return some (a', b'), not none
            -- But we need to show (a', b') ≠ (a, b) or that this case doesn't happen
            -- Actually, f 0 returning some (a', b') is fine as long as (a', b') = (a, b)
            -- But that requires a' = a and b' = b
            -- From h_eq: encode a' = [], so a' is "empty-encodable"
            -- And from h_eq_b: encode b' = encode a ++ encode b
            -- Contradiction: decode_nil_none says decode [] = none, but h_dec_a says decode [] = some a'
            have h_nil_none := enc_α.decode_nil_none
            rw [h_nil_none] at h_dec_a
            exact Option.noConfusion h_dec_a

    -- Apply helper: filterMap head? = some (a, b)
    have h_result := filterMap_head?_first_success f k (a, b) n h_k_bound h_success h_earlier_fail
    -- The goal is decode (encode (a, b)) = some (a, b)
    -- Simplify to match h_result
    simp only [decode, encode, bits, n] at h_result ⊢
    exact h_result

  decode_exact := fun bits (a, b) h => by
    -- Goal: bits = encode (a, b) = enc_α.encode a ++ enc_β.encode b
    -- From decode succeeding, we know bits splits into components that decode correctly
    simp only [decode] at h
    -- h is the head? of filterMap, so extract the successful split
    have h_nonempty : (List.range (bits.length + 1)).filterMap
        (fun split_pos => do
          let bits_a := bits.take split_pos
          let bits_b := bits.drop split_pos
          let a' ← enc_α.decode bits_a
          let b' ← enc_β.decode bits_b
          return (a', b')) ≠ [] := by
      intro h_empty
      rw [h_empty] at h
      simp at h
    cases h_result : (List.range (bits.length + 1)).filterMap
        (fun split_pos => do
          let bits_a := bits.take split_pos
          let bits_b := bits.drop split_pos
          let a' ← enc_α.decode bits_a
          let b' ← enc_β.decode bits_b
          return (a', b')) with
    | nil => contradiction
    | cons hd tl =>
      rw [h_result] at h
      simp only [List.head?_cons] at h
      injection h with h_eq
      -- h_eq : (a, b) = hd, so hd = (a, b)
      -- From h_result, hd came from some successful split
      have h_hd_in : hd ∈ (List.range (bits.length + 1)).filterMap
          (fun split_pos => do
            let bits_a := bits.take split_pos
            let bits_b := bits.drop split_pos
            let a' ← enc_α.decode bits_a
            let b' ← enc_β.decode bits_b
            return (a', b')) := by
        rw [h_result]; simp
      rw [List.mem_filterMap] at h_hd_in
      obtain ⟨split_k, _, h_split⟩ := h_hd_in
      -- Extract a and b from the split
      -- h_split: the do-block succeeded, so both decodes succeeded
      cases h_dec_a : enc_α.decode (bits.take split_k) with
      | none =>
        -- If decode_a fails, the filterMap wouldn't produce this result
        simp [h_dec_a] at h_split
        -- h_split is now none = some hd, which is a contradiction
      | some a' =>
        cases h_dec_b : enc_β.decode (bits.drop split_k) with
        | none =>
          -- If decode_b fails, the filterMap wouldn't produce this result
          simp [h_dec_a, h_dec_b] at h_split
          -- h_split is now none = some hd, which is a contradiction
        | some b' =>
          -- Both succeeded, so hd = (a', b')
          simp [h_dec_a, h_dec_b] at h_split
          -- h_split should now be: some (a', b') = some hd, so (a', b') = hd
          have h_pair_eq : (a', b') = hd := by
            cases h_split; rfl
          -- Now hd = (a', b'), and from h_eq: (a, b) = hd = (a', b')
          rw [← h_pair_eq] at h_eq
          injection h_eq with h_a_eq h_b_eq
          -- Use decode_exact to get the encodings
          have h_bits_a : bits.take split_k = enc_α.encode a' :=
            enc_α.decode_exact _ _ h_dec_a
          have h_bits_b : bits.drop split_k = enc_β.encode b' :=
            enc_β.decode_exact _ _ h_dec_b
          -- Reconstruct bits: substitute a' = a and b' = b
          have h_bits_a_final : bits.take split_k = enc_α.encode a := by
            rw [← h_a_eq]; exact h_bits_a
          have h_bits_b_final : bits.drop split_k = enc_β.encode b := by
            rw [← h_b_eq]; exact h_bits_b
          -- Reconstruct the full encoding
          rw [← List.take_append_drop split_k bits]
          rw [h_bits_a_final, h_bits_b_final]

  encode_nonempty := fun ⟨a, b⟩ => by
    -- Pair encoding is non-empty since first component encoding is non-empty
    simp only [List.length_append]
    have h := enc_α.encode_nonempty a
    omega

  no_prefix_confusion := fun bits ⟨a, b⟩ k h_dec h_k_pos h_k_bound => by
    -- Pair encoding no_prefix_confusion: proper prefixes of encode (a,b) don't decode
    -- Get bits = enc_α.encode a ++ enc_β.encode b from decode succeeding
    have h_bits_eq : bits = enc_α.encode a ++ enc_β.encode b := by
      simp only [decode] at h_dec
      have h_nonempty : (List.range (bits.length + 1)).filterMap
          (fun split_pos => do
            let bits_a := bits.take split_pos
            let bits_b := bits.drop split_pos
            let a' ← enc_α.decode bits_a
            let b' ← enc_β.decode bits_b
            return (a', b')) ≠ [] := by
        intro h_empty; rw [h_empty] at h_dec; simp at h_dec
      cases h_result : (List.range (bits.length + 1)).filterMap
          (fun split_pos => do
            let bits_a := bits.take split_pos
            let bits_b := bits.drop split_pos
            let a' ← enc_α.decode bits_a
            let b' ← enc_β.decode bits_b
            return (a', b')) with
      | nil => contradiction
      | cons hd tl =>
        rw [h_result] at h_dec
        simp only [List.head?_cons] at h_dec
        injection h_dec with h_eq
        have h_hd_in : hd ∈ (List.range (bits.length + 1)).filterMap
            (fun split_pos => do
              let bits_a := bits.take split_pos
              let bits_b := bits.drop split_pos
              let a' ← enc_α.decode bits_a
              let b' ← enc_β.decode bits_b
              return (a', b')) := by rw [h_result]; simp
        rw [List.mem_filterMap] at h_hd_in
        obtain ⟨split_k, _, h_split⟩ := h_hd_in
        cases h_dec_a' : enc_α.decode (bits.take split_k) with
        | none => simp [h_dec_a'] at h_split
        | some a' =>
          cases h_dec_b' : enc_β.decode (bits.drop split_k) with
          | none => simp [h_dec_a', h_dec_b'] at h_split
          | some b' =>
            simp [h_dec_a', h_dec_b'] at h_split
            have h_pair_eq : (a', b') = hd := by cases h_split; rfl
            rw [← h_pair_eq] at h_eq
            injection h_eq with h_a_eq h_b_eq
            have h_bits_a := enc_α.decode_exact _ _ h_dec_a'
            have h_bits_b := enc_β.decode_exact _ _ h_dec_b'
            subst h_a_eq h_b_eq
            rw [← List.take_append_drop split_k bits, h_bits_a, h_bits_b]

    -- Get the concrete lengths and bound
    have h_len_a := (enc_α.encode a).length
    have h_len_b := (enc_β.encode b).length
    have h_k_lt : k < (enc_α.encode a).length + (enc_β.encode b).length := by
      rw [h_bits_eq] at h_k_bound; simp at h_k_bound; exact h_k_bound

    -- Key lemma: for every split position j ≤ k, at least one decode fails
    have h_all_splits_fail : ∀ j, j ≤ k → (do
        let bits_a := (bits.take k).take j
        let bits_b := (bits.take k).drop j
        let a' ← enc_α.decode bits_a
        let b' ← enc_β.decode bits_b
        return (a', b')) = (none : Option (α × β)) := by
      intro j h_j_le_k
      -- Rewrite bits to the concatenation form
      rw [h_bits_eq]
      -- Case analysis on j relative to (enc_α.encode a).length
      by_cases h_j_zero : j = 0
      · -- j = 0: first component is empty, fails by decode_nil_none
        simp only [h_j_zero, List.take_zero]
        have h_nil := enc_α.decode_nil_none
        simp [h_nil]
      · by_cases h_j_lt_len_a : j < (enc_α.encode a).length
        · -- 0 < j < len_a: first component is proper prefix of encode a
          have h_j_pos : 0 < j := Nat.pos_of_ne_zero h_j_zero
          have h_take_j : ((enc_α.encode a ++ enc_β.encode b).take k).take j = (enc_α.encode a).take j := by
            by_cases h_k_le_len_a : k ≤ (enc_α.encode a).length
            · -- k ≤ len_a, so take k only touches encode a
              rw [List.take_append_of_le_length h_k_le_len_a]
              rw [List.take_take]
              congr 1
              exact Nat.min_eq_left h_j_le_k
            · -- k > len_a, so take k = encode a ++ (encode b).take (k - len_a)
              push_neg at h_k_le_len_a
              rw [List.take_append]
              -- After take_append: goal is List.take j (take k (encode a) ++ take (k-len_a) (encode b)) = ...
              -- Since k > len_a, take k (encode a) = encode a
              have h_take_full : (enc_α.encode a).take k = enc_α.encode a :=
                List.take_of_length_le (Nat.le_of_lt h_k_le_len_a)
              rw [h_take_full]
              -- Now goal is List.take j (encode a ++ ...) = take j (encode a)
              rw [List.take_append_of_le_length (Nat.le_of_lt h_j_lt_len_a)]
          rw [h_take_j]
          have h_prefix_none := enc_α.no_prefix_confusion (enc_α.encode a) a j
              (enc_α.decode_encode a) h_j_pos h_j_lt_len_a
          simp [h_prefix_none]
        · push_neg at h_j_lt_len_a
          by_cases h_j_eq_len_a : j = (enc_α.encode a).length
          · -- j = len_a: first component is exactly encode a, second is proper prefix of encode b
            subst h_j_eq_len_a
            -- Case split: is k = len_a or k > len_a?
            by_cases h_k_eq_len_a : k = (enc_α.encode a).length
            · -- k = len_a: the prefix is exactly encode a, second part is empty
              rw [h_k_eq_len_a]
              have h_take_all : ((enc_α.encode a ++ enc_β.encode b).take (enc_α.encode a).length).take
                                (enc_α.encode a).length = enc_α.encode a := by
                rw [List.take_append_of_le_length (by simp)]
                simp
              have h_drop_empty : ((enc_α.encode a ++ enc_β.encode b).take (enc_α.encode a).length).drop
                                  (enc_α.encode a).length = [] := by
                rw [List.take_append_of_le_length (by simp)]
                simp
              rw [h_take_all, h_drop_empty]
              have h_nil := enc_β.decode_nil_none
              simp [enc_α.decode_encode a, h_nil]
            · -- k > len_a: the second component is a proper prefix of encode b
              have h_k_gt_len_a : k > (enc_α.encode a).length := by
                have h_le : (enc_α.encode a).length ≤ k := h_j_le_k
                omega
              have h_k_minus : k - (enc_α.encode a).length < (enc_β.encode b).length := by omega
              have h_take_j_eq : ((enc_α.encode a ++ enc_β.encode b).take k).take (enc_α.encode a).length =
                                 enc_α.encode a := by
                rw [List.take_append]
                -- take k (encode a) = encode a since k > len_a
                have h_take_full : (enc_α.encode a).take k = enc_α.encode a :=
                  List.take_of_length_le (Nat.le_of_lt h_k_gt_len_a)
                rw [h_take_full]
                simp only [List.take_append_of_le_length (by simp : (enc_α.encode a).length ≤ (enc_α.encode a).length), List.take_length]
              have h_drop_j_eq : ((enc_α.encode a ++ enc_β.encode b).take k).drop (enc_α.encode a).length =
                                 (enc_β.encode b).take (k - (enc_α.encode a).length) := by
                rw [List.take_append]
                have h_take_full : (enc_α.encode a).take k = enc_α.encode a :=
                  List.take_of_length_le (Nat.le_of_lt h_k_gt_len_a)
                rw [h_take_full]
                rw [List.drop_append_of_le_length (by simp)]
                simp only [List.drop_length, List.nil_append]
              rw [h_take_j_eq, h_drop_j_eq]
              have h_k_minus_pos : 0 < k - (enc_α.encode a).length := by omega
              have h_prefix_b := enc_β.no_prefix_confusion (enc_β.encode b) b
                  (k - (enc_α.encode a).length) (enc_β.decode_encode b) h_k_minus_pos h_k_minus
              simp [enc_α.decode_encode a, h_prefix_b]
          · -- j > len_a: first component is encode a ++ non-empty prefix of encode b
            have h_j_gt_len_a : j > (enc_α.encode a).length := by omega
            have h_k_gt_len_a : k > (enc_α.encode a).length := by omega
            have h_extra_len : j - (enc_α.encode a).length > 0 := by omega
            have h_extra_le : j - (enc_α.encode a).length ≤ k - (enc_α.encode a).length := by omega
            have h_take_j_struct : ((enc_α.encode a ++ enc_β.encode b).take k).take j =
                enc_α.encode a ++ (enc_β.encode b).take (j - (enc_α.encode a).length) := by
              rw [List.take_append]
              -- take k (encode a) = encode a since k > len_a
              have h_take_k_full : (enc_α.encode a).take k = enc_α.encode a :=
                List.take_of_length_le (Nat.le_of_lt h_k_gt_len_a)
              rw [h_take_k_full]
              -- Now take j from (encode a ++ (encode b).take (k - len_a))
              rw [List.take_append]
              -- take j (encode a) = encode a since j > len_a
              have h_take_j_full : (enc_α.encode a).take j = enc_α.encode a :=
                List.take_of_length_le (Nat.le_of_lt h_j_gt_len_a)
              rw [h_take_j_full]
              congr 1
              rw [List.take_take, Nat.min_eq_left h_extra_le]
            rw [h_take_j_struct]
            -- Use decode_extend_none: decode (encode a ++ extra) = none when extra ≠ []
            have h_extra_nonempty : ((enc_β.encode b).take (j - (enc_α.encode a).length)).length > 0 := by
              rw [List.length_take]
              have h_j_minus_le_len_b : j - (enc_α.encode a).length ≤ (enc_β.encode b).length := by omega
              simp only [Nat.min_eq_left h_j_minus_le_len_b]
              omega
            have h_ext := enc_α.decode_extend_none a
                ((enc_β.encode b).take (j - (enc_α.encode a).length)) h_extra_nonempty
            simp [h_ext]

    -- Now show filterMap on range (k+1) is empty
    have h_filterMap_empty : (List.range (k + 1)).filterMap (fun j => do
        let bits_a := (bits.take k).take j
        let bits_b := (bits.take k).drop j
        let a' ← enc_α.decode bits_a
        let b' ← enc_β.decode bits_b
        return (a', b')) = [] := by
      rw [filterMap_range_eq_nil]
      intro j h_j_lt
      exact h_all_splits_fail j (Nat.lt_succ_iff.mp h_j_lt)

    -- Finally, decode (bits.take k) = head? [] = none
    simp only [decode]
    have h_range_eq : (bits.take k).length + 1 = k + 1 := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt h_k_bound)]
    conv => lhs; arg 1; rw [h_range_eq]
    rw [h_filterMap_empty]
    rfl

  blank := (enc_α.blank, enc_β.blank)

  blank_bits := enc_α.blank_bits ++ enc_β.blank_bits

  blank_encoding := by
    simp only [enc_α.blank_encoding, enc_β.blank_encoding]

  blank_decode := by
    -- Use filterMap_head?_first_success helper like decode_encode
    -- blank_bits = enc_α.blank_bits ++ enc_β.blank_bits
    -- The correct split is at k = enc_α.blank_bits.length
    let bits := enc_α.blank_bits ++ enc_β.blank_bits
    let k := enc_α.blank_bits.length
    let n := bits.length
    let f : Nat → Option (α × β) := fun split_pos => do
      let bits_a := bits.take split_pos
      let bits_b := bits.drop split_pos
      let a' ← enc_α.decode bits_a
      let b' ← enc_β.decode bits_b
      return (a', b')

    have h_k_bound : k ≤ n := by simp only [k, n, bits, List.length_append]; omega

    have h_success : f k = some (enc_α.blank, enc_β.blank) := by
      simp only [f, k, bits]
      have h_take : (enc_α.blank_bits ++ enc_β.blank_bits).take enc_α.blank_bits.length = enc_α.blank_bits := by simp
      have h_drop : (enc_α.blank_bits ++ enc_β.blank_bits).drop enc_α.blank_bits.length = enc_β.blank_bits := by simp
      simp only [h_take, h_drop, enc_α.blank_decode, enc_β.blank_decode]
      rfl

    have h_earlier_fail : ∀ j, j < k → f j = none := by
      intro j h_j_lt
      simp only [f, bits]
      have h_j_lt_len : j < enc_α.blank_bits.length := h_j_lt
      have h_take_eq : (enc_α.blank_bits ++ enc_β.blank_bits).take j = enc_α.blank_bits.take j := by
        rw [List.take_append_of_le_length (Nat.le_of_lt h_j_lt_len)]
      rw [h_take_eq]
      by_cases h_j_pos : j > 0
      · -- j > 0: use no_prefix_confusion on blank_bits via blank_encoding
        have h_blank_dec : enc_α.decode enc_α.blank_bits = some enc_α.blank := enc_α.blank_decode
        have h_prefix_fail : enc_α.decode (enc_α.blank_bits.take j) = none :=
          enc_α.no_prefix_confusion enc_α.blank_bits enc_α.blank j h_blank_dec h_j_pos h_j_lt_len
        -- Reduce do-notation: let a' ← none; ... = none
        simp only [h_prefix_fail]
        rfl  -- none >>= f = none by definition
      · -- j = 0: empty prefix - use decode_nil_none
        push_neg at h_j_pos
        have h_j_zero : j = 0 := Nat.le_zero.mp h_j_pos
        simp only [h_j_zero, List.take_zero]
        have h_nil_none := enc_α.decode_nil_none
        simp only [h_nil_none]
        rfl  -- none >>= f = none by definition

    have h_result := filterMap_head?_first_success f k (enc_α.blank, enc_β.blank) n h_k_bound h_success h_earlier_fail
    simp only [decode, encode, bits, n] at h_result ⊢
    exact h_result

/-- Helper: Convert Nat to standard binary (LSB first, for internal use). -/
def Nat.toBinaryListStandard (n : Nat) : List Bool :=
  if n = 0 then []
  else (n % 2 = 1) :: toBinaryListStandard (n / 2)
termination_by n
decreasing_by
  simp_wf
  apply Nat.div_lt_self
  · omega
  · omega

/-- Prefix-free binary encoding for Nat using unary-length header.
    Encoding: replicate len true ++ [false] ++ standard_binary(n)
    where len = length(standard_binary(n))

    Examples: 0→[false], 1→[true,false,true], 2→[true,true,false,true,false]

    Genuinely prefix-free: the position of first false uniquely determines length. -/
def Nat.toBinaryList (n : Nat) : List Bool :=
  let bits := toBinaryListStandard n
  List.replicate bits.length true ++ false :: bits

/-- Expansion of toBinaryList without let binding -/
lemma Nat.toBinaryList_expand (n : Nat) :
    toBinaryList n = List.replicate (toBinaryListStandard n).length true ++ false :: toBinaryListStandard n := rfl

/-- toBinaryList 0 = [false] (base case: empty standard binary) -/
lemma Nat.toBinaryList_zero : toBinaryList 0 = [false] := by
  unfold toBinaryList toBinaryListStandard
  simp

/-- Standard binary length bound -/
lemma Nat.toBinaryListStandard_length_le (n : Nat) : (toBinaryListStandard n).length ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold toBinaryListStandard
    by_cases h : n = 0
    · simp [h]
    · simp [h]
      have h_pos : 0 < n := Nat.pos_of_ne_zero h
      have h_div_lt : n / 2 < n := Nat.div_lt_self h_pos (by omega : 1 < 2)
      have ih_rec := ih (n / 2) h_div_lt
      -- length = 1 + (toBinaryListStandard (n/2)).length ≤ 1 + (n/2 + 1) ≤ n + 1
      have : (toBinaryListStandard (n / 2)).length + 1 ≤ n / 2 + 1 + 1 :=
        Nat.add_le_add_right ih_rec 1
      omega

/-- Prefix-free encoding length bound: length ≤ 2*n + 3.
    New encoding: replicate len true ++ [false] ++ bits
    where len = bits.length, so total = len + 1 + len = 2*len + 1
    Since len ≤ n + 1, we have length ≤ 2*(n+1) + 1 = 2*n + 3 -/
lemma Nat.toBinaryList_length_le (n : Nat) : (toBinaryList n).length ≤ 2 * n + 3 := by
  unfold toBinaryList
  let bits := toBinaryListStandard n
  have h_std_le : bits.length ≤ n + 1 := toBinaryListStandard_length_le n
  have h_len : (List.replicate bits.length true ++ false :: bits).length =
               2 * bits.length + 1 := by
    rw [List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [h_len]
  omega

/-- Nat.log2 is monotone. -/
lemma Nat.log2_mono {m n : Nat} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  -- Use log2_eq_log_two to convert to Nat.log 2, then apply log_mono_right
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

/-- Standard binary length is at most log2(n) + 1 -/
lemma Nat.toBinaryListStandard_length_le_log (n : Nat) :
    (toBinaryListStandard n).length ≤ Nat.log2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold toBinaryListStandard
    by_cases h : n = 0
    · simp [h, Nat.log2_zero]
    · simp [h]
      by_cases h1 : n = 1
      · -- For n=1: toBinaryListStandard 1 = [true], length = 1
        simp [h1, toBinaryListStandard]
      · -- n ≥ 2
        have h_ge2 : n ≥ 2 := by omega
        have h_pos : 0 < n := Nat.pos_of_ne_zero h
        have h_div_lt : n / 2 < n := Nat.div_lt_self h_pos (by omega : 1 < 2)
        have ih_rec := ih (n / 2) h_div_lt
        -- Use log2 division property
        have h_log_div : Nat.log2 (n / 2) + 1 ≤ Nat.log2 n := by
          have h_div : Nat.log 2 (n / 2) = Nat.log 2 n - 1 := Nat.log_div_base 2 n
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          rw [h_div]
          have : Nat.log 2 n ≥ 1 := by
            rw [← Nat.log2_eq_log_two]
            have : 2 ≤ n := h_ge2
            have : Nat.log2 2 ≤ Nat.log2 n := Nat.log2_mono this
            simp [Nat.log2_two] at this
            exact this
          omega
        omega

/-- Logarithmic length bound: length ≤ 2*log2(n) + 3.
    New encoding doubles the standard binary length plus 1 for delimiter. -/
lemma Nat.toBinaryList_length_le_log (n : Nat) : (toBinaryList n).length ≤ 2 * Nat.log2 n + 3 := by
  unfold toBinaryList
  let bits := toBinaryListStandard n
  have h_std_le : bits.length ≤ Nat.log2 n + 1 := toBinaryListStandard_length_le_log n
  have h_len : (List.replicate bits.length true ++ false :: bits).length =
               2 * bits.length + 1 := by
    rw [List.length_append, List.length_replicate, List.length_cons]
    omega
  rw [h_len]
  omega

/-- Helper: Decode prefix-free binary encoding.
    Returns None if bits doesn't match replicate len true ++ [false] ++ body structure.
    Structure: len leading trues, then false delimiter, then len-bit body.
    Only accepts CANONICAL encodings: body must be the standard representation of the number.
    This ensures decode_exact: decode ∘ encode = id on valid encodings. -/
def Nat.fromBinaryList (bits : List Bool) : Option Nat :=
  let len := (bits.takeWhile (· = true)).length
  let rest := bits.drop len
  match rest with
  | false :: value_bits =>
      if value_bits.length = len then
        let n := value_bits.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0
        -- Only accept canonical encoding: body length must match standard encoding length
        if (toBinaryListStandard n).length = len then some n else none
      else none
  | _ => none

/-- Helper: Standard binary foldr reconstructs n -/
lemma Nat.foldr_toBinaryListStandard (n : Nat) :
    (toBinaryListStandard n).foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold toBinaryListStandard
    by_cases h : n = 0
    · simp [h]
    · simp [h]
      have h_pos : 0 < n := Nat.pos_of_ne_zero h
      have h_div_lt : n / 2 < n := Nat.div_lt_self h_pos (by omega : 1 < 2)
      have ih_rec := ih (n / 2) h_div_lt
      rw [ih_rec]
      by_cases h_odd : n % 2 = 1
      · simp [h_odd]; omega
      · have : n % 2 = 0 := by omega
        simp [this]; omega

/-- Helper: Binary foldr is injective on same-length lists.
    If two lists of the same length produce the same number via foldr, they are equal. -/
lemma Nat.foldr_binary_injective (l1 l2 : List Bool)
    (h_len : l1.length = l2.length)
    (h_val : l1.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 =
             l2.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at h_len
  | cons hd1 tl1 ih =>
    cases l2 with
    | nil => simp at h_len
    | cons hd2 tl2 =>
      simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj] at h_len
      simp only [List.foldr_cons] at h_val
      -- h_val: foldr tl1 * 2 + (hd1 ? 1 : 0) = foldr tl2 * 2 + (hd2 ? 1 : 0)
      -- The bits must be equal (mod 2 of each side)
      have h_heads : hd1 = hd2 := by
        cases hd1 <;> cases hd2 <;> simp_all <;> omega
      -- The tails must also produce equal values
      have h_tails : tl1.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 =
                     tl2.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 := by
        cases hd1 <;> simp_all <;> omega
      rw [h_heads, ih tl2 h_len h_tails]

/-- toBinaryListStandard is injective (standard binary encoding is unique). -/
lemma Nat.toBinaryListStandard_injective : Function.Injective Nat.toBinaryListStandard := by
  intros m n h
  -- Prove by showing foldr reconstructs uniquely
  have hm := Nat.foldr_toBinaryListStandard m
  have hn := Nat.foldr_toBinaryListStandard n
  rw [h] at hm
  -- Now: hm says foldr (toBinaryListStandard n) = m, hn says foldr (toBinaryListStandard n) = n
  calc m
    _ = (toBinaryListStandard n).foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 := hm.symm
    _ = n := hn

/-- Helper: If a ++ x = a ++ y then x = y -/
private lemma append_cancel_left {α : Type} (a x y : List α) (h : a ++ x = a ++ y) : x = y := by
  induction a with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.cons_append] at h
    exact ih (List.cons.inj h).2

/-- Helper: Count leading trues in a list -/
private def countLeadingTrues : List Bool → Nat
  | [] => 0
  | true :: rest => 1 + countLeadingTrues rest
  | false :: _ => 0

/-- Helper: Leading trues of replicate k true ++ rest -/
private lemma countLeadingTrues_replicate_true (k : Nat) (rest : List Bool) :
    countLeadingTrues (List.replicate k true ++ rest) =
    k + countLeadingTrues rest := by
  induction k with
  | zero => simp [countLeadingTrues]
  | succ k ih =>
    simp [List.replicate_succ, countLeadingTrues]
    rw [ih]
    omega

/-- Helper: Leading trues of false :: rest is 0 -/
private lemma countLeadingTrues_false_cons (rest : List Bool) :
    countLeadingTrues (false :: rest) = 0 := rfl

/-- toBinaryList is injective: different numbers have different encodings. -/
lemma Nat.toBinaryList_injective : Function.Injective Nat.toBinaryList := by
  intros m n h
  -- Use the expansion form directly
  have h' : List.replicate (toBinaryListStandard m).length true ++ false :: toBinaryListStandard m =
            List.replicate (toBinaryListStandard n).length true ++ false :: toBinaryListStandard n := by
    simp only [← Nat.toBinaryList_expand]; exact h
  -- Abbreviate lengths
  let len_m := (toBinaryListStandard m).length
  let len_n := (toBinaryListStandard n).length
  -- Count leading trues to show len_m = len_n
  have h_count : countLeadingTrues (List.replicate len_m true ++ false :: toBinaryListStandard m) =
                 countLeadingTrues (List.replicate len_n true ++ false :: toBinaryListStandard n) := by
    rw [h']
  have h_left : countLeadingTrues (List.replicate len_m true ++ false :: toBinaryListStandard m) = len_m := by
    rw [countLeadingTrues_replicate_true, countLeadingTrues_false_cons]; omega
  have h_right : countLeadingTrues (List.replicate len_n true ++ false :: toBinaryListStandard n) = len_n := by
    rw [countLeadingTrues_replicate_true, countLeadingTrues_false_cons]; omega
  rw [h_left, h_right] at h_count
  have h_len_eq : len_m = len_n := h_count
  -- Use length equality to cancel the prefix and extract body equality
  have h_bodies : toBinaryListStandard m = toBinaryListStandard n := by
    -- Use h_len_eq to convert h' to use the same length on both sides
    have h_len_m : len_m = (toBinaryListStandard m).length := rfl
    have h_len_n : len_n = (toBinaryListStandard n).length := rfl
    rw [← h_len_m, ← h_len_n, h_len_eq] at h'
    -- Now h' : replicate len_n true ++ false :: body_m = replicate len_n true ++ false :: body_n
    -- Cancel the common prefix
    have h_cancel := append_cancel_left (List.replicate len_n true)
                       (false :: toBinaryListStandard m) (false :: toBinaryListStandard n) h'
    exact (List.cons.inj h_cancel).2
  exact Nat.toBinaryListStandard_injective h_bodies

/-- Helper: takeWhile of replicate k true ++ rest -/
private lemma takeWhile_replicate_true (k : Nat) (rest : List Bool) :
    (List.replicate k true ++ rest).takeWhile (· = true) =
    List.replicate k true ++ rest.takeWhile (· = true) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, List.takeWhile_cons, decide_eq_true_eq]
    simp only [ih, ite_true]

/-- Helper: takeWhile of false :: rest is empty -/
private lemma takeWhile_false_cons (rest : List Bool) :
    (false :: rest).takeWhile (· = true) = [] := rfl

/-- Helper: Drop replicate len true from front -/
private lemma drop_replicate_append (k : Nat) (rest : List Bool) :
    (List.replicate k true ++ rest).drop k = rest := by
  rw [List.drop_append_of_le_length (by simp [List.length_replicate])]
  simp

/-- Helper: If takeWhile (· = true) has length n, first n elements are all true -/
private lemma takeWhile_true_means_prefix_all_true (bits : List Bool) :
    bits.take (bits.takeWhile (· = true)).length = List.replicate (bits.takeWhile (· = true)).length true := by
  induction bits with
  | nil => simp
  | cons hd tl ih =>
    cases hd with
    | true =>
      simp only [List.takeWhile_cons, decide_true, ite_true, List.length_cons,
                 List.take_succ_cons, List.replicate_succ, List.cons.injEq, true_and]
      exact ih
    | false =>
      simp

/-- Helper: Reconstruct list from takeWhile/drop when delimiter is found -/
private lemma reconstruct_from_takeWhile_drop (bits : List Bool) (tl : List Bool)
    (h_drop : bits.drop (bits.takeWhile (· = true)).length = false :: tl) :
    bits = List.replicate (bits.takeWhile (· = true)).length true ++ false :: tl := by
  have h1 := takeWhile_true_means_prefix_all_true bits
  have h2 := List.take_append_drop (bits.takeWhile (· = true)).length bits
  rw [h1, h_drop] at h2
  exact h2.symm

/-- Round-trip lemma: fromBinaryList (toBinaryList n) = some n -/
lemma Nat.fromBinaryList_toBinaryList (n : Nat) :
    fromBinaryList (toBinaryList n) = some n := by
  unfold fromBinaryList toBinaryList
  -- Let body = toBinaryListStandard n
  -- Encoding is: replicate body.length true ++ false :: body
  simp only [takeWhile_replicate_true, takeWhile_false_cons, List.takeWhile_nil,
             List.length_replicate, List.length_append, List.append_nil,
             drop_replicate_append, List.length_cons]
  -- After simp: match (false :: toBinaryListStandard n) with | false :: value_bits => ...
  -- This matches with value_bits = toBinaryListStandard n
  -- Check 1: (toBinaryListStandard n).length = (toBinaryListStandard n).length ✓
  -- Check 2: (toBinaryListStandard (foldr body)).length = len, and foldr body = n ✓
  simp only [ite_true, foldr_toBinaryListStandard]

/-- Helper: If decode succeeds, bits has the encoded structure -/
lemma Nat.fromBinaryList_structure (bits : List Bool) (n : Nat)
    (h : fromBinaryList bits = some n) : bits = toBinaryList n := by
  -- Unfold and simplify the lets in the definition
  simp only [fromBinaryList] at h
  -- Now h has: (match bits.drop (bits.takeWhile ...).length with | false :: _ => ... | _ => none) = some n
  -- Case split on the drop result
  generalize h_len : (bits.takeWhile (· = true)).length = len at h
  generalize h_drop : bits.drop len = rest at h
  cases rest with
  | nil =>
    -- match [] returns none
    simp at h
  | cons hd tl =>
    cases hd with
    | true =>
      -- match (true :: _) returns none
      simp at h
    | false =>
      -- match (false :: tl) proceeds with ifs
      simp only at h
      -- h : (if tl.length = len then (let n := ...; if ... then some n else none) else none) = some n
      split_ifs at h with h_len_check h_canon_check
      · -- Both if conditions passed
        injection h with h_n
        -- h_len_check: tl.length = len
        -- h_canon_check: (toBinaryListStandard (foldr tl)).length = len
        -- h_n: foldr tl = n
        have h_std_len : (toBinaryListStandard n).length = len := by
          rw [← h_n]; exact h_canon_check
        have h_foldr_val : tl.foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 =
                           (toBinaryListStandard n).foldr (fun b acc => acc * 2 + if b then 1 else 0) 0 := by
          rw [h_n, foldr_toBinaryListStandard]
        have h_len_eq : tl.length = (toBinaryListStandard n).length := by
          rw [h_len_check, h_std_len]
        have h_body_eq : tl = toBinaryListStandard n :=
          foldr_binary_injective tl (toBinaryListStandard n) h_len_eq h_foldr_val
        -- Reconstruct: we need to show bits.drop (bits.takeWhile ...).length = false :: tl
        -- We have h_drop : bits.drop len = false :: tl and h_len : (...).length = len
        have h_drop' : bits.drop (bits.takeWhile (· = true)).length = false :: tl := by
          rw [h_len]; exact h_drop
        have h_bits_struct := reconstruct_from_takeWhile_drop bits tl h_drop'
        rw [h_body_eq] at h_bits_struct
        -- h_bits_struct : bits = replicate (bits.takeWhile ...).length true ++ false :: toBinaryListStandard n
        -- Goal: bits = toBinaryList n
        --     = replicate (toBinaryListStandard n).length true ++ false :: toBinaryListStandard n
        -- We need to show (bits.takeWhile ...).length = (toBinaryListStandard n).length
        -- From h_len: (bits.takeWhile ...).length = len
        -- From h_std_len: (toBinaryListStandard n).length = len
        rw [h_bits_struct]
        unfold toBinaryList
        congr 1
        rw [h_len, h_std_len]
      all_goals simp at h

/-- Bool encoding with non-empty encodings.
    Encoding: false → [false], true → [true].
    Single-bit encoding ensures encode_nonempty. -/
def BitEncoding.bool : BitEncoding Bool where
  encode := fun b => [b]
  C_len := 1
  k_len := 1
  len_bound := fun b => by simp [size]
  decode := fun bits =>
    match bits with
    | [b] => some b
    | _ => none
  decode_encode := fun b => by simp
  decode_exact := fun bits x h => by
    cases bits with
    | nil => simp at h
    | cons hd tl =>
      cases tl with
      | nil => simp at h; simp [h]
      | cons _ _ => simp at h
  encode_nonempty := fun b => by simp
  no_prefix_confusion := fun bits x k h_dec h_k_pos h_k_bound => by
    -- Bool encodings are single bits: [false] or [true]
    -- Proper non-empty prefix means 0 < k < 1, which is impossible
    -- First show bits = [x] (inline decode_exact logic)
    have h_bits : bits = [x] := by
      cases bits with
      | nil => simp at h_dec
      | cons hd tl =>
        cases tl with
        | nil => simp at h_dec; simp [h_dec]
        | cons _ _ => simp at h_dec
    rw [h_bits] at h_k_bound
    simp at h_k_bound
    omega
  blank := false
  blank_bits := [false]
  blank_encoding := by simp
  blank_decode := by simp

/-- Nat encoding (binary). -/
def BitEncoding.nat : BitEncoding Nat where
  encode := Nat.toBinaryList
  C_len := 3  -- Unary-header prefix-free encoding: length ≤ 2*n + 3 = 2*(size n - 1) + 3 = 2*size n + 1
  k_len := 1
  len_bound := fun n => by
    -- Prefix-free binary encoding length ≤ 2*n + 3
    have h := Nat.toBinaryList_length_le n
    show (Nat.toBinaryList n).length ≤ 3 * (size n + 1) ^ 1
    simp only [pow_one]
    -- size n = n + 1 for Nat (by sizedNat instance), so n = size n - 1
    -- length ≤ 2*n + 3 = 2*(size n - 1) + 3 = 2*size n + 1 ≤ 3*(size n + 1)
    calc (Nat.toBinaryList n).length
      _ ≤ 2 * n + 3 := h
      _ = 2 * (size n - 1) + 3 := by simp [size]  -- size n = n + 1
      _ ≤ 3 * (size n + 1) := by omega
  decode := Nat.fromBinaryList
  decode_encode := Nat.fromBinaryList_toBinaryList
  decode_exact := fun bits n h => Nat.fromBinaryList_structure bits n h
  encode_nonempty := fun n => by
    -- toBinaryList n = replicate len true ++ [false] ++ body, length ≥ 1
    unfold Nat.toBinaryList
    simp
  no_prefix_confusion := fun bits n k h_dec h_k_pos h_k_bound => by
    -- bits = toBinaryList n = replicate len true ++ [false] ++ body
    -- where len = body.length and body = toBinaryListStandard n
    have h_bits_eq := Nat.fromBinaryList_structure bits n h_dec
    rw [h_bits_eq]
    -- Now: show fromBinaryList (toBinaryList n).take k = none
    --   where 0 < k < (toBinaryList n).length
    set body := Nat.toBinaryListStandard n with h_body_def
    set len := body.length with h_len_def
    -- toBinaryList n = replicate len true ++ [false] ++ body
    -- length = len + 1 + len = 2*len + 1
    have h_total_len : (Nat.toBinaryList n).length = 2 * len + 1 := by
      unfold Nat.toBinaryList
      simp only [List.length_append, List.length_replicate, List.length_cons, h_len_def]
      ring
    rw [h_bits_eq] at h_k_bound
    rw [h_total_len] at h_k_bound
    -- Now: 0 < k < 2*len + 1
    -- First, establish that toBinaryList n = replicate len true ++ false :: body
    have h_expand : Nat.toBinaryList n = List.replicate len true ++ false :: body := by
      unfold Nat.toBinaryList
      rfl
    -- Case split: is k ≤ len? (still in header) or k > len?
    by_cases h_case : k ≤ len
    · -- Case 1: k ≤ len → prefix is all trues → drop gives [] → no match
      -- Take k elements from replicate len true ++ [false] ++ body
      -- Since k ≤ len, this is just replicate k true
      unfold Nat.fromBinaryList
      -- Rewrite toBinaryList n to the expanded form
      simp only [h_expand]
      have h_prefix_all_true : (List.replicate len true ++ false :: body).take k =
                               List.replicate k true := by
        have h_len_ge : (List.replicate len true).length ≥ k := by simp; omega
        rw [List.take_append_of_le_length h_len_ge]
        simp only [List.take_replicate, Nat.min_eq_left h_case]
      rw [h_prefix_all_true]
      -- takeWhile (· = true) of replicate k true is replicate k true
      have h_takeWhile : ∀ m, (List.replicate m true).takeWhile (· = true) = List.replicate m true := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          simp only [List.replicate_succ, List.takeWhile_cons, decide_eq_true_eq, ite_true, ih]
      simp only [h_takeWhile, List.length_replicate, List.drop_replicate, Nat.sub_self]
      -- drop k from replicate k true gives []
      -- After substitution: match [] with false :: _ => ... | x => none
      -- Since [] doesn't match false :: _, we get none
      rfl
    · -- Case 2: k > len → prefix includes false delimiter → body truncated → length check fails
      push_neg at h_case
      unfold Nat.fromBinaryList
      -- Rewrite toBinaryList n to the expanded form
      simp only [h_expand]
      -- Take k elements: replicate len true ++ [false] ++ body.take (k - len - 1)
      have h_prefix : (List.replicate len true ++ false :: body).take k =
                      List.replicate len true ++ false :: body.take (k - len - 1) := by
        rw [List.take_append]
        simp only [List.length_replicate, List.take_replicate, Nat.min_eq_right (Nat.le_of_lt h_case)]
        congr 1
        -- take (k - len) from (false :: body)
        have h_k_len_pos : k - len > 0 := by omega
        have h_km : ∃ m, k - len = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
        obtain ⟨m, hm⟩ := h_km
        rw [hm]
        simp only [List.take_succ_cons, List.cons.injEq, true_and]
        -- m = k - len - 1, so the goal is List.take m body = List.take (m + 1 - 1) body
        -- Since m + 1 - 1 = m, this is trivial
        simp only [Nat.add_sub_cancel]
      rw [h_prefix]
      -- takeWhile (· = true) gives replicate len true
      have h_takeWhile : (List.replicate len true ++ false :: body.take (k - len - 1)).takeWhile (· = true)
                         = List.replicate len true := by
        rw [takeWhile_replicate_true, takeWhile_false_cons, List.append_nil]
      rw [h_takeWhile]
      simp only [List.length_replicate]
      rw [drop_replicate_append]
      -- Check: body.take (k - len - 1).length =? len
      -- Since k < 2*len + 1, we have k - len - 1 < len
      have h_body_take_len : (body.take (k - len - 1)).length = k - len - 1 := by
        apply List.length_take_of_le
        rw [← h_len_def]
        omega
      simp only [h_body_take_len]
      -- k - len - 1 ≠ len (since k < 2*len + 1 means k - len - 1 < len)
      have h_len_ne : k - len - 1 ≠ len := by omega
      simp [h_len_ne]

  blank := 0
  blank_bits := [false]  -- toBinaryList 0 = [false] with unary-header encoding
  blank_encoding := Nat.toBinaryList_zero
  blank_decode := by
    -- fromBinaryList [false] = some 0
    rw [← Nat.toBinaryList_zero]
    exact Nat.fromBinaryList_toBinaryList 0

/-- Fin n encoding (bounded natural).
    Requires n > 0 for well-formedness. -/
def BitEncoding.fin (n : Nat) (h_pos : n > 0) : BitEncoding (Fin n) where
  encode := fun i => Nat.toBinaryList i.val
  C_len := 3  -- Same as Nat encoding with unary-header
  k_len := 1
  len_bound := fun i => by
    -- Use log2 bound with prefix-free encoding: length ≤ 2*log2(i.val) + 3
    show (Nat.toBinaryList i.val).length ≤ 3 * (size i + 1) ^ 1
    simp only [pow_one]
    -- Step 1: toBinaryList length ≤ 2*log2(i.val) + 3 (unary header encoding)
    have h_log : (Nat.toBinaryList i.val).length ≤ 2 * Nat.log2 i.val + 3 :=
      Nat.toBinaryList_length_le_log i.val
    -- Step 2: log2(i.val) ≤ log2(n) (since i.val < n, use log2_mono)
    have h_mono : Nat.log2 i.val ≤ Nat.log2 n := by
      apply Nat.log2_mono
      exact Nat.le_of_lt i.isLt
    -- Step 3: Combine: 2*log2(n) + 3 ≤ 3*(log2(n) + 1 + 1) = 3*(size i + 1)
    have h_size : size i = Nat.log2 n + 1 := rfl
    calc (Nat.toBinaryList i.val).length
      _ ≤ 2 * Nat.log2 i.val + 3 := h_log
      _ ≤ 2 * Nat.log2 n + 3 := by omega
      _ ≤ 3 * (Nat.log2 n + 2) := by omega
      _ = 3 * (size i + 1) := by rw [h_size]
  decode := fun bits => do
    let val ← Nat.fromBinaryList bits
    if h : val < n then some ⟨val, h⟩ else none
  decode_encode := fun i => by
    -- Use Nat round-trip + bound check
    simp only [Nat.fromBinaryList]
    have h_round := Nat.fromBinaryList_toBinaryList i.val
    simp only [Nat.fromBinaryList] at h_round
    simp only [Option.bind_eq_bind, Option.bind_some, h_round]
    -- Goal: (if i.val < n then some ⟨i.val, ...⟩ else none) = some i
    -- Since i : Fin n, we have i.val < n
    have h_lt : i.val < n := i.isLt
    simp only [h_lt, ↓reduceDIte]
    -- Goal: some ⟨i.val, h_lt⟩ = some i (already simplified)
  decode_exact := fun bits i h => by
    -- Decode uses Nat.fromBinaryList, which has decode_exact
    -- h : decode bits = some i
    -- Show that decode bits expands to the do-block, then work with that structure
    have h_expand : (do let val ← Nat.fromBinaryList bits
                        if h : val < n then some ⟨val, h⟩ else none) = some i := h
    -- Cases on the Nat.fromBinaryList result
    cases h_from : Nat.fromBinaryList bits with
    | none =>
      simp [h_from] at h_expand
    | some val =>
      simp [h_from] at h_expand
      -- h_expand is now: ∃ (h : val < n), ⟨val, h⟩ = i
      obtain ⟨h_lt, h_eq⟩ := h_expand
      -- h_eq : ⟨val, h_lt⟩ = i, so val = i.val
      have h_val_eq : val = i.val := by
        have := congrArg Fin.val h_eq
        simp at this
        exact this
      -- Use Nat's fromBinaryList_structure lemma directly
      have : bits = Nat.toBinaryList val :=
        Nat.fromBinaryList_structure bits val h_from
      rw [this, h_val_eq]
  encode_nonempty := fun i => by
    -- toBinaryList i.val is always non-empty
    unfold Nat.toBinaryList
    simp
  no_prefix_confusion := fun bits i k h_dec h_k_pos h_k_bound => by
    -- Fin decode uses Nat.fromBinaryList, so if Nat decode fails, Fin decode fails
    -- First get the structure of bits from h_dec
    -- h_dec : (do let val ← Nat.fromBinaryList bits; if val < n then ... else none) = some i
    cases h_from : Nat.fromBinaryList bits with
    | none => simp [h_from] at h_dec
    | some val =>
      -- bits = Nat.toBinaryList val
      have h_bits_eq : bits = Nat.toBinaryList val :=
        Nat.fromBinaryList_structure bits val h_from
      -- Get val = i.val
      simp [h_from] at h_dec
      obtain ⟨h_lt, h_eq⟩ := h_dec
      have h_val_eq : val = i.val := by
        have := congrArg Fin.val h_eq
        simp at this
        exact this
      -- Specialize using val (before rewriting)
      -- nat.decode = Nat.fromBinaryList, so we get Nat.fromBinaryList (bits.take k) = none
      have h_nat_npc : Nat.fromBinaryList (List.take k bits) = none :=
        BitEncoding.nat.no_prefix_confusion bits val k h_from h_k_pos h_k_bound
      -- Goal: Fin.decode (bits.take k) = none
      -- Fin.decode does (Nat.fromBinaryList bits).bind (bound check)
      -- Since Nat.fromBinaryList (bits.take k) = none, the bind returns none
      simp only [Option.bind_eq_bind, h_nat_npc, Option.none_bind]
  blank := ⟨0, h_pos⟩
  blank_bits := [false]  -- toBinaryList 0 = [false] with unary-header encoding
  blank_encoding := by simp only [Nat.toBinaryList_zero]
  blank_decode := by
    -- Need: decode [false] = some ⟨0, h_pos⟩
    -- fromBinaryList [false] = some 0 (by toBinaryList_zero and roundtrip)
    simp only [Option.bind_eq_bind, Option.bind_some]
    -- Show: Nat.fromBinaryList [false] = some 0
    have h_from : Nat.fromBinaryList [false] = some 0 := by
      rw [← Nat.toBinaryList_zero]
      exact Nat.fromBinaryList_toBinaryList 0
    simp only [h_from, Option.some_bind]
    -- Now: if 0 < n then some ⟨0, _⟩ else none = some ⟨0, h_pos⟩
    simp only [h_pos, ↓reduceDIte]

/-- Vector Bool encoding with prefix for non-empty encoding.
    Encoding: v → true :: v.toList (prefix ensures encode_nonempty).
    Decode strips the prefix and checks length. -/
def BitEncoding.vector (n : Nat) : BitEncoding (Vector Bool n) where
  encode := fun v => true :: v.toList
  C_len := 2
  k_len := 1
  len_bound := fun v => by
    simp only [List.length_cons]
    have h_len : v.toList.length = n := v.2
    have h_size : size v = n + 1 := rfl
    rw [h_len, h_size]
    simp only [pow_one]
    -- Need: n + 1 ≤ 2 * (n + 1 + 1) = 2 * (n + 2) = 2n + 4
    omega
  decode := fun bits =>
    match bits with
    | true :: rest =>
      if h : rest.length = n then
        some (Vector.mk rest.toArray h)
      else
        none
    | _ => none
  decode_encode := fun v => by
    -- decode (true :: v.toList) = some (Vector.mk v.toList.toArray _) = some v
    have h_len : v.toList.length = n := v.2
    simp only [h_len, ↓reduceDIte]
    -- Goal: some (Vector.mk v.toList.toArray h_len) = some v
    congr 1
  decode_exact := fun bits v h => by
    match h_bits : bits with
    | [] => simp [h_bits] at h
    | false :: _ => simp [h_bits] at h
    | true :: rest =>
      simp only [h_bits] at h
      split at h
      · injection h with h_eq
        simp only [List.cons.injEq, true_and]
        -- Goal: rest = v.toList
        -- h_eq : Vector.mk rest.toArray _ = v
        have : (Vector.mk rest.toArray (by assumption : rest.toArray.size = n)).toList = v.toList := by
          rw [h_eq]
        simp at this
        exact this
      · cases h
  encode_nonempty := fun v => by simp
  no_prefix_confusion := fun bits v k h_dec h_k_pos h_k_bound => by
    -- Inline decode_exact logic to get bits = true :: v.toList
    have h_bits_eq : bits = true :: v.toList := by
      match h_bits : bits with
      | [] => simp [h_bits] at h_dec
      | false :: _ => simp [h_bits] at h_dec
      | true :: rest =>
        simp only [h_bits] at h_dec
        split at h_dec
        · injection h_dec with h_eq
          simp only [List.cons.injEq, true_and]
          have h_rest_eq : rest = v.toList := by
            have : (Vector.mk rest.toArray (by assumption : rest.toArray.size = n)).toList = v.toList := by
              rw [h_eq]
            simp at this
            exact this
          rw [h_rest_eq]
        · cases h_dec
    rw [h_bits_eq]
    -- bits.take k where bits = true :: v.toList, k < n + 1
    have h_take : (true :: v.toList).take k =
      if k = 0 then [] else true :: (v.toList.take (k - 1)) := by
      cases k with
      | zero => simp
      | succ k' => simp
    rw [h_take]
    have h_k_ne_zero : k ≠ 0 := Nat.pos_iff_ne_zero.mp h_k_pos
    simp only [h_k_ne_zero, ↓reduceIte]
    -- decode (true :: v.toList.take (k-1)) = none when (k-1) < n
    have h_v_len : v.toList.length = n := v.2
    have h_k_bound' : k < n + 1 := by
      rw [h_bits_eq] at h_k_bound
      simpa using h_k_bound
    have h_take_len : (v.toList.take (k - 1)).length = k - 1 := by
      rw [List.length_take, h_v_len]
      omega
    have h_ne_n : (v.toList.take (k - 1)).length ≠ n := by
      rw [h_take_len]
      omega
    simp only [h_ne_n, ↓reduceDIte]
  blank := Vector.replicate n false
  blank_bits := true :: List.replicate n false
  blank_encoding := by simp [Vector.toList_replicate]
  blank_decode := by
    simp only
    have h_len : (List.replicate n false).length = n := by simp
    simp only [h_len, ↓reduceDIte]
    ext i
    simp [Vector.toList_replicate]

-- Axiom Audits
#print axioms BitEncoding
#print axioms BitEncoding.pair
#print axioms BitEncoding.bool
#print axioms BitEncoding.nat
#print axioms BitEncoding.fin
#print axioms BitEncoding.vector

end LStar.Complexity
