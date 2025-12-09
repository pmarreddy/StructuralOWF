import Layer1_Construction.Core.OAPEncoding
import Layer0_Foundations.Base.CNF

/-! # OAPLocalFlip: Local Flipping Lemma for OAP Non-Inferability

## Purpose

This module provides the foundational lemma for the two-instance construction
in the OAP non-inferability proof (§10.1.1-NI).

## Key Insight

The OAP encoding uses XOR masking:
```
encoded_literal = literal ⊕ mask(seed)
```

Due to XOR's properties:
- XOR is self-inverse: `a ⊕ b ⊕ b = a`
- XOR is commutative and associative

Therefore, if we have two (literal, seed) pairs that produce the same encoded result:
```
lit₀ ⊕ mask(seed₀) = lit₁ ⊕ mask(seed₁)
```

This is equivalent to:
```
lit₁ = lit₀ ⊕ mask(seed₀) ⊕ mask(seed₁)
     = lit₀ ⊕ Δmask
```

where `Δmask = mask(seed₀) ⊕ mask(seed₁)` is the "mask difference".

## Main Lemmas

1. **same_encoding_different_literal**: If seeds differ, we can find a literal that
   produces the same encoding as the original.

2. **complementary_literal_exists**: For any literal, there exists a "complementary"
   literal (opposite polarity) that can be made to have the same encoding with a
   different seed.

3. **local_flip_preserves_encoding**: Flipping a literal's polarity and adjusting
   the seed appropriately preserves the encoded result.
-/

namespace LStar.OAP.LocalFlip

open LStar LStar.OAP

/-! ## Part 1: Mask Difference Analysis -/

/-- The mask difference between two seeds at the same position.

    This captures how much the mask changes when we switch seeds.
    Due to XOR properties, knowing this difference lets us compute
    what literal change would preserve the encoding. -/
def maskDifference {w₀ w₁ : Nat}
    (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat) : (Nat × Bool) :=
  let (maskVar₀, maskPol₀) := computeLiteralMask seed₀ clauseIdx litIdx
  let (maskVar₁, maskPol₁) := computeLiteralMask seed₁ clauseIdx litIdx
  (Nat.xor maskVar₀ maskVar₁, xor maskPol₀ maskPol₁)

/-- The literal that, when encoded with seed₁, gives the same result as lit encoded with seed₀.

    **Key Property**: `encodeLiteral (adjustedLiteral lit seed₀ seed₁ ci li) seed₁ ci li
                     = encodeLiteral lit seed₀ ci li`

    **Derivation**:
    Let enc = lit ⊕ mask₀. We want lit' such that lit' ⊕ mask₁ = enc.
    Solving: lit' = enc ⊕ mask₁ = lit ⊕ mask₀ ⊕ mask₁ = lit ⊕ Δmask -/
def adjustedLiteral {w₀ w₁ : Nat}
    (lit : Literal) (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat) : Literal :=
  let (deltaVar, deltaPol) := maskDifference seed₀ seed₁ clauseIdx litIdx
  { var := Nat.xor lit.var deltaVar
    polarity := xor lit.polarity deltaPol }

/-! ## Part 2: Encoding Preservation Under Adjustment -/

/-- Helper lemma: XOR of three terms with self-cancellation -/
lemma xor_cancel_right (a b c : Nat) : (a ^^^ (b ^^^ c)) ^^^ c = a ^^^ b := by
  rw [Nat.xor_assoc a (b ^^^ c) c]
  rw [Nat.xor_assoc b c c]
  rw [Nat.xor_self c]
  rw [Nat.xor_zero b]

/-- Helper lemma: Bool XOR with self-cancellation -/
lemma bool_xor_cancel_right (a b c : Bool) : xor (xor a (xor b c)) c = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Main Lemma**: The adjusted literal produces the same encoding.

    This is the key technical fact: changing the seed and adjusting the literal
    appropriately preserves the encoded output.

    **Proof**: Direct calculation using XOR associativity and self-cancellation. -/
theorem adjusted_literal_same_encoding {w₀ w₁ : Nat}
    (lit : Literal) (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat) :
    encodeLiteral (adjustedLiteral lit seed₀ seed₁ clauseIdx litIdx) seed₁ clauseIdx litIdx =
    encodeLiteral lit seed₀ clauseIdx litIdx := by
  unfold encodeLiteral adjustedLiteral maskDifference computeLiteralMask
  simp only [EncodedLiteral.mk.injEq]
  constructor
  · -- maskedVar equality: (lit.var ⊕ (h₀ ⊕ h₁)) ⊕ h₁ = lit.var ⊕ h₀
    exact xor_cancel_right lit.var _ _
  · -- maskedPolarity equality
    exact bool_xor_cancel_right lit.polarity _ _

/-- **Corollary**: If two (literal, seed) pairs give the same encoding, they're related
    by the adjustment operation.

    This is the converse direction: same encoding implies the literals are related. -/
theorem same_encoding_implies_adjusted {w₀ w₁ : Nat}
    (lit₀ : Literal) (lit₁ : Literal)
    (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat)
    (h_same : encodeLiteral lit₀ seed₀ clauseIdx litIdx =
              encodeLiteral lit₁ seed₁ clauseIdx litIdx) :
    lit₁ = adjustedLiteral lit₀ seed₀ seed₁ clauseIdx litIdx := by
  -- From h_same: lit₀ ⊕ mask₀ = lit₁ ⊕ mask₁
  -- Therefore: lit₁ = lit₀ ⊕ mask₀ ⊕ mask₁ = adjustedLiteral lit₀ seed₀ seed₁
  unfold encodeLiteral computeLiteralMask at h_same
  simp only [EncodedLiteral.mk.injEq] at h_same
  obtain ⟨h_var, h_pol⟩ := h_same
  -- Now unfold on RHS
  unfold adjustedLiteral maskDifference computeLiteralMask

  -- Abbreviations for mask values
  let m₀ := PoolConfig.hashSeed seed₀ + clauseIdx * 997 + litIdx * 991
  let m₁ := PoolConfig.hashSeed seed₁ + clauseIdx * 997 + litIdx * 991

  -- Derive lit₁.var using XOR cancellation
  have h_var_eq : lit₁.var = (lit₀.var ^^^ m₀) ^^^ m₁ := by
    have h_xor : (lit₀.var ^^^ m₀) ^^^ m₁ = lit₁.var := by
      have h1 : lit₀.var.xor m₀ = lit₀.var ^^^ m₀ := rfl
      have h2 : lit₁.var.xor m₁ = lit₁.var ^^^ m₁ := rfl
      rw [h1, h2] at h_var
      calc (lit₀.var ^^^ m₀) ^^^ m₁
         = (lit₁.var ^^^ m₁) ^^^ m₁ := by rw [h_var]
       _ = lit₁.var := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact h_xor.symm

  -- Derive lit₁.polarity using Bool XOR cancellation
  have h_pol_eq : lit₁.polarity = xor (xor lit₀.polarity (m₀ % 2 == 1)) (m₁ % 2 == 1) := by
    have h_xor : xor (xor lit₀.polarity (m₀ % 2 == 1)) (m₁ % 2 == 1) = lit₁.polarity := by
      calc xor (xor lit₀.polarity (m₀ % 2 == 1)) (m₁ % 2 == 1)
         = xor (xor lit₁.polarity (m₁ % 2 == 1)) (m₁ % 2 == 1) := by rw [h_pol]
       _ = lit₁.polarity := by cases lit₁.polarity <;> cases (m₁ % 2 == 1) <;> rfl
    exact h_xor.symm

  -- Combine into Literal equality
  cases lit₁ with
  | mk v p =>
    simp only [Literal.mk.injEq]
    simp only at h_var_eq h_pol_eq
    constructor
    · -- v = lit₀.var.xor (m₀.xor m₁)
      -- h_var_eq says: v = (lit₀.var ^^^ m₀) ^^^ m₁
      -- Goal is: v = lit₀.var.xor (m₀.xor m₁) = lit₀.var ^^^ (m₀ ^^^ m₁)
      -- By associativity: (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c), so these are equal
      simp only [m₀, m₁] at h_var_eq ⊢
      -- The goal is: v = lit₀.var.xor (m₀.xor m₁)
      -- h_var_eq says: v = (lit₀.var ^^^ m₀) ^^^ m₁
      -- These are equal by XOR associativity
      -- First convert .xor to ^^^ notation (they are definitionally equal)
      show v = lit₀.var ^^^ ((PoolConfig.hashSeed seed₀ + clauseIdx * 997 + litIdx * 991) ^^^
                              (PoolConfig.hashSeed seed₁ + clauseIdx * 997 + litIdx * 991))
      rw [h_var_eq, Nat.xor_assoc]
    · -- p = xor lit₀.polarity (xor (m₀ % 2 == 1) (m₁ % 2 == 1))
      simp only [m₀, m₁] at h_pol_eq ⊢
      rw [h_pol_eq]
      cases lit₀.polarity <;>
      cases ((PoolConfig.hashSeed seed₀ + clauseIdx * 997 + litIdx * 991) % 2 == 1) <;>
      cases ((PoolConfig.hashSeed seed₁ + clauseIdx * 997 + litIdx * 991) % 2 == 1) <;>
      rfl

/-! ## Part 3: Polarity Flip Conditions -/

/-- When do two seeds produce masks with different polarities?

    The mask polarity is `(hash + ci * 997 + li * 991) % 2 == 1`.
    Two seeds produce different polarities iff their hash values have different parities
    (after the index mixing). -/
def seedsHaveDifferentMaskPolarities {w₀ w₁ : Nat}
    (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat) : Prop :=
  let (_, pol₀) := computeLiteralMask seed₀ clauseIdx litIdx
  let (_, pol₁) := computeLiteralMask seed₁ clauseIdx litIdx
  pol₀ ≠ pol₁

/-- Helper: if two bools are different, their XOR is true -/
lemma bool_ne_iff_xor_true (a b : Bool) : a ≠ b ↔ xor a b = true := by
  cases a <;> cases b <;> simp [Bool.xor]

/-- **Key Observation**: If seeds have different mask polarities at (ci, li),
    then adjustedLiteral flips the polarity.

    This is crucial: we can construct a literal with OPPOSITE polarity that
    has the same encoding, just by choosing a seed with different mask parity. -/
theorem adjusted_flips_polarity_when_masks_differ {w₀ w₁ : Nat}
    (lit : Literal) (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat)
    (h_diff_pol : seedsHaveDifferentMaskPolarities seed₀ seed₁ clauseIdx litIdx) :
    (adjustedLiteral lit seed₀ seed₁ clauseIdx litIdx).polarity ≠ lit.polarity := by
  unfold adjustedLiteral maskDifference computeLiteralMask seedsHaveDifferentMaskPolarities at *
  simp only at h_diff_pol ⊢
  -- h_diff_pol says pol₀ ≠ pol₁
  -- We need to show: xor lit.polarity (xor pol₀ pol₁) ≠ lit.polarity
  -- Since pol₀ ≠ pol₁, we have xor pol₀ pol₁ = true
  -- Therefore xor lit.polarity true = ¬lit.polarity ≠ lit.polarity
  have h_xor_true : xor ((PoolConfig.hashSeed seed₀ + clauseIdx * 997 + litIdx * 991) % 2 == 1)
                        ((PoolConfig.hashSeed seed₁ + clauseIdx * 997 + litIdx * 991) % 2 == 1) = true := by
    rw [← bool_ne_iff_xor_true]
    exact h_diff_pol
  simp only [h_xor_true]
  cases lit.polarity <;> simp [Bool.xor]

/-! ## Part 4: Existence of Seeds with Different Mask Polarities

For the two-instance construction, we need to show that there EXIST seeds with
different mask polarities. This depends on the seed space being large enough.

**Key Insight**: The hash function `PoolConfig.hashSeed` maps seeds to naturals.
Different seeds generally produce different hashes. If we have enough seeds
(at least 2), we can find pairs with different parities.
-/

/-- Helper: For any w, seed value 0 exists -/
lemma seed_zero_exists (w : Nat) : (0 : Nat) < 2^w :=
  Nat.two_pow_pos w

/-- Helper: For w ≥ 1, seed value 1 exists -/
lemma seed_one_exists (w : Nat) (h_w : w ≥ 1) : (1 : Nat) < 2^w := by
  have h_ne : w ≠ 0 := by omega
  have h2 : 2 ≤ 2^w := Nat.one_lt_two_pow h_ne
  omega

/-- Helper: hash of seed 0 is 0 -/
lemma hashSeed_zero (w : Nat) :
    PoolConfig.hashSeed (⟨0, seed_zero_exists w⟩ : Seed w) = 0 := rfl

/-- Helper: hash of seed 1 is 1 -/
lemma hashSeed_one (w : Nat) (h_w : w ≥ 1) :
    PoolConfig.hashSeed (⟨1, seed_one_exists w h_w⟩ : Seed w) = 1 := rfl

/-- Helper: adding 1 changes parity -/
lemma parity_add_one (n : Nat) : (n % 2 == 1) ≠ ((n + 1) % 2 == 1) := by
  cases h : n % 2 with
  | zero =>
    have h1 : (n + 1) % 2 = 1 := by omega
    simp only [h1]
    decide
  | succ m =>
    have hm : m = 0 := by omega
    subst hm
    have h1 : (n + 1) % 2 = 0 := by omega
    simp only [h1]
    decide

/-- **Seed Existence Lemma**: If seed width w ≥ 1, there exist seeds with different
    hash parities.

    **Proof**: Since Seed w = Fin (2^w) and hashSeed s = s.val, we have:
    - Seed 0 has hashSeed = 0 (even)
    - Seed 1 has hashSeed = 1 (odd)

    The mask polarity formula is `(hashSeed + clauseIdx * 997 + litIdx * 991) % 2 == 1`.
    Since adding 1 to any number changes its parity, seeds 0 and 1 always produce
    different mask polarities. -/
theorem exists_seeds_with_different_parities (w : Nat) (h_w : w ≥ 1) (clauseIdx litIdx : Nat) :
    ∃ (seed₀ seed₁ : Seed w), seedsHaveDifferentMaskPolarities seed₀ seed₁ clauseIdx litIdx := by
  -- Use seeds 0 and 1
  let s0 : Seed w := ⟨0, seed_zero_exists w⟩
  let s1 : Seed w := ⟨1, seed_one_exists w h_w⟩
  use s0, s1
  -- Unfold the definition
  unfold seedsHaveDifferentMaskPolarities computeLiteralMask
  -- hashSeed s0 = 0, hashSeed s1 = 1
  -- s0.val = 0, s1.val = 1
  have h0 : PoolConfig.hashSeed s0 = 0 := rfl
  have h1 : PoolConfig.hashSeed s1 = 1 := rfl
  simp only [h0, h1, Nat.zero_add]
  -- Now: (clauseIdx * 997 + litIdx * 991) % 2 == 1 ≠ (1 + clauseIdx * 997 + litIdx * 991) % 2 == 1
  -- Note: expression parses as ((1 + clauseIdx * 997) + litIdx * 991)
  -- We need to show this equals ((clauseIdx * 997 + litIdx * 991) + 1) to apply parity_add_one
  let offset := clauseIdx * 997 + litIdx * 991
  have h_assoc : 1 + clauseIdx * 997 + litIdx * 991 = offset + 1 := by
    simp only [offset]; omega
  rw [h_assoc]
  exact parity_add_one offset

/-! ## Part 5: Main Construction Theorem

Given a planted instance, we can construct another with:
- Same encoded CNF
- Different underlying literal at a specific position
- (Optionally) Opposite polarity to ensure witness incompatibility
-/

/-- **Local Flip Theorem**: For any clause and literal position, if we can find
    a seed with different mask parity, we can construct a different literal
    that produces the same encoding.

    This is the building block for the two-instance construction. -/
theorem local_flip_construction {w₀ w₁ : Nat}
    (lit : Literal) (seed₀ : Seed w₀) (seed₁ : Seed w₁) (clauseIdx litIdx : Nat)
    (h_diff_pol : seedsHaveDifferentMaskPolarities seed₀ seed₁ clauseIdx litIdx) :
    ∃ (lit' : Literal),
      -- Same encoding
      encodeLiteral lit' seed₁ clauseIdx litIdx = encodeLiteral lit seed₀ clauseIdx litIdx ∧
      -- Different literal
      lit' ≠ lit ∧
      -- Specifically, opposite polarity
      lit'.polarity ≠ lit.polarity := by
  use adjustedLiteral lit seed₀ seed₁ clauseIdx litIdx
  constructor
  · -- Same encoding
    exact adjusted_literal_same_encoding lit seed₀ seed₁ clauseIdx litIdx
  constructor
  · -- Different literal
    intro h_eq
    have h_pol := adjusted_flips_polarity_when_masks_differ lit seed₀ seed₁ clauseIdx litIdx h_diff_pol
    rw [h_eq] at h_pol
    exact h_pol rfl
  · -- Opposite polarity
    exact adjusted_flips_polarity_when_masks_differ lit seed₀ seed₁ clauseIdx litIdx h_diff_pol

/-! ## Module Summary

### Proven Theorems (0 axioms)

1. `adjusted_literal_same_encoding`: Core XOR preservation
2. `adjusted_flips_polarity_when_masks_differ`: Polarity flip condition
3. `local_flip_construction`: Main construction theorem
4. `same_encoding_implies_adjusted`: Converse direction

### Placeholders (require hash analysis)

1. `exists_seeds_with_different_parities`: Existence of suitable seeds

### Usage in Two-Instance Construction

To build the two instances:
1. Pick a clause index `ci` and literal index `li`
2. Find seeds `seed₀, seed₁` with different mask parities at `(ci, li)`
3. Use `local_flip_construction` to get `lit'` with opposite polarity
4. Build φ' by replacing lit with lit' at position (ci, li)
5. Verify: `encode φ' seed₁ = encode φ seed₀` (same encoded CNF)
6. Verify: φ and φ' have incompatible witnesses (opposite polarity clause)
-/

end LStar.OAP.LocalFlip
