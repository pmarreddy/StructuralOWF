import Layer3_InformationBounds.Support.ObservationModel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! ## StructuralLowerBound: Classical Parity Decision Tree Lower Bound

**Theorem**: `parity_requires_all_bits` — incomplete observation → ∃ indistinguishable
configs with different parities.

**Classical result** (folklore, ~1970s): Computing PARITY(x₁,...,xₙ) requires reading all n bits.

**Proof idea**: For any subset S ⊊ {1,...,n}, flip an unread bit to change parity
without changing observed values.

---

## Architectural Role: 1-bit Parity as DISCRIMINATOR

**Why 1-bit parity is acceptable here**:

Parity is used as a DISCRIMINATOR (witness that configs differ), NOT as the
source of hardness. The proof chain is:

```
incomplete_obs
  → ∃ cfg1, cfg2: parity(cfg1) ≠ parity(cfg2)   [THIS FILE: 1-bit discriminator]
  → cfg1 ≠ cfg2                                  [trivial: same parity if equal]
  → encodeSeed(cfg1) ≠ encodeSeed(cfg2)          [A2 injectivity: R-bit hardness]
```

The 2^R lower bound comes from A2 injectivity on FULL R-bit emergent vectors,
not from parity itself. Parity is convenient because flipping ANY single bit
flips parity, guaranteeing we can always find distinguishing configs.

---

**Application to FG** (§6, Appendix C):
- FG observable digest = parity over emergent bits at node v
- Incomplete obs → cannot determine correct parity
- Hardness: must explore 2^R configs (from A2), not 2 parity classes

**Key theorems** (Wegener 1987):
- `parity_requires_all_bits`: Constructive witnesses (cfg1, cfg2) for indistinguishability
- `correct_parity_requires_complete_observation`: Contrapositive form

**Trust boundary**: 0 axioms — proven using ZMod 2 arithmetic + bit manipulation

See Layer3_InformationBounds/Layer3_README.md §Segment Reduction.
-/

namespace LStar.StructuralOWF.Foundations

open LStar
open scoped BigOperators

/-! ## Bit Manipulation Helpers -/

/-- getBit always returns 0 or 1. -/
lemma getBit_lt_two (cfg : Nat) (i : Nat) : getBit cfg i < 2 := by
  unfold getBit
  apply Nat.mod_lt
  norm_num

/-- getBit is bounded by 2. -/
lemma getBit_le_one (cfg : Nat) (i : Nat) : getBit cfg i ≤ 1 := by
  have := getBit_lt_two cfg i
  omega

/-- **XOR Bounds**: XOR with small value preserves bounds. -/
lemma xor_pow_two_lt {n i : Nat} (hi : i < n) (cfg : Nat) (hcfg : cfg < 2^n) :
    cfg ^^^ (2^i) < 2^n := by
  -- Use the generic bitwise bound for functions with f false false = false
  -- XOR satisfies this condition.
  have hmask : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by omega : 1 < 2) hi
  -- `Nat.bitwise_lt_two_pow` is stated for a general boolean function `f`.
  -- Instantiate it with `Bool.xor` and the two bounds above.
  simpa using (Nat.bitwise_lt_two_pow (f := fun a b => a ^^ b) hcfg hmask)

/-! ### Bridge: getBit ↔ testBit -/

/-- Bridge lemma: getBit (Nat 0/1) corresponds to testBit (Bool).

    **Proof Strategy**: Use mathlib's testBit characterization. Split on whether bit is set. -/
lemma getBit_eq_testBit (n i : Nat) :
    getBit n i = (if Nat.testBit n i then 1 else 0) := by
  unfold getBit
  -- Goal: (n / 2^i) % 2 = (if Nat.testBit n i then 1 else 0)

  -- Use mathlib: testBit i = decide ((n/2^i) % 2 = 1)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  -- Now: (n / 2^i) % 2 = (if decide ((n/2^i) % 2 = 1) then 1 else 0)

  -- Split on the decidable proposition
  split_ifs with h_decide
  case pos =>
    -- h_decide : decide ((n / 2^i) % 2 = 1) = true
    -- Convert decide = true to the proposition
    rwa [decide_eq_true_iff] at h_decide
  case neg =>
    -- h_decide : ¬(decide ((n / 2^i) % 2 = 1) = true)
    -- This means the proposition is false: ¬((n / 2^i) % 2 = 1)
    have h_not_one : ¬((n / 2^i) % 2 = 1) := fun h => h_decide (decide_eq_true h)
    -- Goal: (n / 2^i) % 2 = 0
    -- Since (n / 2^i) % 2 < 2 and ≠ 1, must be 0
    have h_bound : (n / 2^i) % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    -- (n / 2^i) % 2 < 2 and ≠ 1 → must be 0
    interval_cases (n / 2^i) % 2
    · rfl
    · contradiction

/-! ### Bit Manipulation via Modular Arithmetic -/

/-- **Bit Flip**: XOR with 2^i flips bit i.

    **Proof Strategy**: Use testBit_xor to decompose XOR, testBit_two_pow_self
    shows 2^i has bit i set, then Bool.xor_true shows XOR with true flips the bit. -/
lemma getBit_xor_pow_same (cfg i : Nat) :
    getBit (cfg ^^^  2^i) i = 1 - getBit cfg i := by
  -- Convert both sides to testBit form
  rw [getBit_eq_testBit, getBit_eq_testBit]
  -- Goal: (if testBit (cfg ^^^ 2^i) i then 1 else 0) = 1 - (if testBit cfg i then 1 else 0)

  -- Use testBit_xor to decompose the XOR
  rw [Nat.testBit_xor]
  -- Goal: (if testBit cfg i ^^ testBit (2^i) i then 1 else 0) = 1 - (if testBit cfg i then 1 else 0)

  -- testBit (2^i) i = true
  rw [Nat.testBit_two_pow_self]
  -- Goal: (if testBit cfg i ^^ true then 1 else 0) = 1 - (if testBit cfg i then 1 else 0)

  -- XOR with true is Boolean negation
  rw [Bool.xor_true]
  -- Goal: (if !testBit cfg i then 1 else 0) = 1 - (if testBit cfg i then 1 else 0)

  -- Case analysis on Nat.testBit cfg i (it's a Bool)
  cases Nat.testBit cfg i <;> simp

/-- **Bit Preserve**: XOR with 2^i preserves bits j ≠ i.

    **Proof Strategy**: Similar to getBit_xor_pow_same, but testBit_two_pow_of_ne
    shows 2^i has bit j = false when i ≠ j, so XOR with false preserves the bit. -/
lemma getBit_xor_pow_other (cfg i j : Nat) (h_ne : i ≠ j) :
    getBit (cfg ^^^ 2^i) j = getBit cfg j := by
  -- Convert both sides to testBit form
  rw [getBit_eq_testBit, getBit_eq_testBit]
  -- Goal: (if testBit (cfg ^^^ 2^i) j then 1 else 0) = (if testBit cfg j then 1 else 0)

  -- Use testBit_xor to decompose the XOR
  rw [Nat.testBit_xor]
  -- Goal: (if testBit cfg j ^^ testBit (2^i) j then 1 else 0) = (if testBit cfg j then 1 else 0)

  -- testBit (2^i) j = false (since i ≠ j)
  rw [Nat.testBit_two_pow_of_ne h_ne]
  -- Goal: (if testBit cfg j ^^ false then 1 else 0) = (if testBit cfg j then 1 else 0)

  -- XOR with false is identity
  rw [Bool.xor_false]
  -- Goal is now reflexive: (if testBit cfg j then 1 else 0) = (if testBit cfg j then 1 else 0)

/-! ## Parity Function -/

/-- Compute parity of a configuration (treating it as bit vector).

    **Definition**: XOR of all bits in the configuration.

    **Example**:
    - cfg = 0b1011 (decimal 11)
    - Bits: 1, 1, 0, 1
    - Parity: 1 ⊕ 1 ⊕ 0 ⊕ 1 = 1 (odd number of 1s)

    **Implementation**: Sum all bits modulo 2. -/
def parity {n : Nat} (cfg : Fin (2^n)) : Nat :=
  (List.range n).foldl (fun acc i => (acc + getBit cfg.val i) % 2) 0

/-- Parity is always 0 or 1 (bounded by mod 2).

    **Proof Strategy**: Induction on the list fold. The invariant `(acc + getBit ...) % 2 < 2`
    is maintained at each step since mod 2 always produces 0 or 1. -/
lemma parity_lt_two {n : Nat} (cfg : Fin (2^n)) : parity cfg < 2 := by
  unfold parity
  -- Goal: (List.range n).foldl (fun acc i => (acc + getBit cfg.val i) % 2) 0 < 2

  -- Prove a stronger statement: for any accumulator acc < 2, the fold maintains < 2
  suffices ∀ (xs : List Nat) (acc : Nat), acc < 2 →
      xs.foldl (fun acc i => (acc + getBit cfg.val i) % 2) acc < 2 by
    exact this (List.range n) 0 (by norm_num : 0 < 2)

  -- Induction on the list
  intro xs
  induction xs with
  | nil =>
    -- Base case: empty list returns accumulator
    intro acc h_acc
    simp [h_acc]
  | cons x xs ih =>
    -- Inductive case
    intro acc h_acc
    simp only [List.foldl_cons]
    -- Goal: foldl ... ((acc + getBit cfg.val x) % 2) < 2
    -- Apply IH with new accumulator
    apply ih
    -- Show: (acc + getBit cfg.val x) % 2 < 2
    apply Nat.mod_lt
    norm_num

/-! ## Bit Flipping -/

/-- Flip bit i in configuration cfg.

    **Definition**: cfg ⊕ 2^i (XOR with single bit mask).

    **Example**:
    - cfg = 0b1010 (decimal 10), i = 2
    - Flip bit 2: 0b1010 ⊕ 0b0100 = 0b1110 (decimal 14)

    **Property**: Flipping bit i changes exactly one bit position. -/
def flipBit {n : Nat} (cfg : Fin (2^n)) (i : Fin n) : Fin (2^n) :=
  ⟨cfg.val ^^^ (2^i.val), by
    -- Bounds check: flipping a bit in 2^n range stays in range
    apply xor_pow_two_lt
    · exact i.isLt  -- i < n
    · exact cfg.isLt  -- cfg < 2^n
  ⟩

/-- Flipping bit i changes only position i, preserves others. -/
lemma flipBit_preserves_others {n : Nat} (cfg : Fin (2^n)) (i j : Fin n)
    (h_ne : i ≠ j) :
    getBit (flipBit cfg i).val j.val = getBit cfg.val j.val := by
  unfold flipBit
  simp
  -- Use library lemma: XOR with 2^i preserves bits j ≠ i
  have : i.val ≠ j.val := by intro h; exact h_ne (Fin.ext h)
  exact getBit_xor_pow_other cfg.val i.val j.val this

/-- Flipping bit i changes bit i. -/
lemma flipBit_changes_target {n : Nat} (cfg : Fin (2^n)) (i : Fin n) :
    getBit (flipBit cfg i).val i.val = 1 - getBit cfg.val i.val := by
  unfold flipBit
  simp
  exact getBit_xor_pow_same cfg.val i.val

/-- ZMod 2 version of parity for cleaner arithmetic. -/
def parityZMod {n : Nat} (cfg : Fin (2^n)) : ZMod 2 :=
  (List.range n).foldl (fun (acc : ZMod 2) i => acc + (getBit cfg.val i : ZMod 2)) 0

/-- ZMod parity equals Nat parity (as ZMod 2 value). -/
lemma parity_eq_parityZMod_val {n : Nat} (cfg : Fin (2^n)) :
    (parity cfg : ZMod 2) = parityZMod cfg := by
  -- We prove a more general fold lemma and then specialize to `acc = 0` and `xs = List.range n`.
  -- Step cast lemma: casting modulo 2 into ZMod 2 removes the modulo.
  have cast_step (acc bit : Nat) :
      (((acc + bit) % 2 : Nat) : ZMod 2) = (acc : ZMod 2) + (bit : ZMod 2) := by
    -- From Nat.mod_add_div: (acc+bit) % 2 + 2 * ((acc+bit) / 2) = acc + bit
    have h := Nat.mod_add_div (acc + bit) 2
    -- Cast to ZMod 2 and simplify using (2 : ZMod 2) = 0
    have h' := congrArg (fun t : Nat => (t : ZMod 2)) h
    have htwo : ((2 : Nat) : ZMod 2) = 0 := by
      simp; exact (ZMod.natCast_self (n := 2))
    -- Rearrange and simplify
    -- h' is: ((acc+bit)%2 : ZMod 2) + ((2:ZMod 2) * ((acc+bit)/2 : ZMod 2)) = (acc : ZMod 2) + (bit : ZMod 2)
    -- With (2 : ZMod 2) = 0, the middle term vanishes.
    simp only [Nat.cast_add, Nat.cast_mul, htwo, zero_mul, add_zero] at h'
    exact h'

  -- General fold lemma: Nat-fold (with mod 2) cast to ZMod 2 equals ZMod-fold.
  have fold_cast : ∀ (xs : List Nat) (acc : Nat),
      (((xs.foldl (fun acc i => (acc + getBit cfg.val i) % 2) acc : Nat) : ZMod 2))
        = xs.foldl (fun (accz : ZMod 2) i => accz + (getBit cfg.val i : ZMod 2)) (acc : ZMod 2) := by
    intro xs acc
    induction xs generalizing acc with
    | nil => simp
    | cons x xs ih =>
      -- Unfold one fold step on both sides, then use the induction hypothesis.
      simp only [List.foldl_cons]
      -- Apply IH with the updated Nat accumulator
      simpa [cast_step acc (getBit cfg.val x)] using ih ((acc + getBit cfg.val x) % 2)

  -- Specialize to acc = 0 and xs = List.range n
  unfold parity parityZMod
  simpa using fold_cast (List.range n) 0

/-- Helper: fold distributes over addition in accumulator (generic version). -/
private lemma fold_add_distributes_gen {xs : List Nat} (f : Nat → ZMod 2) (acc c : ZMod 2) :
    xs.foldl (fun (acc : ZMod 2) a => acc + f a) (acc + c) =
    xs.foldl (fun (acc : ZMod 2) a => acc + f a) acc + c := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_assoc : acc + c + f x = (acc + f x) + c := by ring
    rw [h_assoc, ih]

/-- Helper: fold distributes over addition in accumulator. -/
private lemma fold_add_distributes {n : Nat} (cfg : Fin (2^n)) (xs : List Nat) (acc c : ZMod 2) :
    xs.foldl (fun (acc : ZMod 2) a => acc + (getBit cfg.val a : ZMod 2)) (acc + c) =
    xs.foldl (fun (acc : ZMod 2) a => acc + (getBit cfg.val a : ZMod 2)) acc + c :=
  fold_add_distributes_gen (fun a => (getBit cfg.val a : ZMod 2)) acc c

/-! ### Finset-Based Parity Proof -/

/-- Finset-based parity definition using Fintype.sum.

    **Purpose**: Enables clean algebraic proofs via Finset.sum lemmas.
    Equivalent to List-based parityZMod. -/
def parityZMod_finset {n : Nat} (cfg : Fin (2^n)) : ZMod 2 :=
  ∑ i : Fin n, (getBit cfg.val i.val : ZMod 2)

/-- Auxiliary lemma: fold/sum equivalence for any natural number m.

    **Key**: Generalizes over the value m : Nat, not tied to Fin (2^n). -/
private lemma parityZMod_eq_finset_aux (n : Nat) (m : Nat) :
    (List.range n).foldl (fun (acc : ZMod 2) i => acc + (getBit m i : ZMod 2)) 0 =
    ∑ i : Fin n, (getBit m i.val : ZMod 2) := by
  induction n with
  | zero =>
    simp [List.range_zero]
  | succ n ih =>
    -- LHS: fold over range (n+1) = fold over range n + getBit m n
    rw [List.range_succ]
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    -- Apply IH to the first part
    rw [ih]
    -- RHS: sum over Fin (n+1) splits into Fin n and the last element
    rw [Fin.sum_univ_castSucc]
    -- Last element: Fin.last n has value n
    simp [Fin.val_last]

/-- Bridge lemma: List.foldl equals Finset.sum for parity.

    **Proof Strategy**: Use auxiliary lemma generalized over Nat values. -/
lemma parityZMod_eq_finset {n : Nat} (cfg : Fin (2^n)) :
    parityZMod cfg = parityZMod_finset cfg := by
  unfold parityZMod parityZMod_finset
  exact parityZMod_eq_finset_aux n cfg.val

/-- **Flipping bit i adds 1 to parity in ZMod 2** (formerly axiom, now proven).

    **Proof Strategy**: Direct proof using Finset.sum with case analysis on each term.
    When bit i flips from b to (1-b), it contributes (1-b) - b = 1 - 2b ≡ 1 (mod 2). -/
theorem parityZMod_flip {n : Nat} (cfg : Fin (2^n)) (i : Fin n) :
    parityZMod (flipBit cfg i) = parityZMod cfg + 1 := by
  -- Convert both sides to Finset form
  rw [parityZMod_eq_finset, parityZMod_eq_finset]
  unfold parityZMod_finset

  -- Key: show the difference between flipped and original sum equals 1
  suffices h : ∑ j : Fin n, (getBit (flipBit cfg i).val j.val : ZMod 2) =
               ∑ j : Fin n, (getBit cfg.val j.val : ZMod 2) + 1 by
    calc ∑ j : Fin n, (getBit (flipBit cfg i).val j.val : ZMod 2)
        = ∑ j : Fin n, (getBit cfg.val j.val : ZMod 2) + 1 := h
      _ = (∑ j : Fin n, (getBit cfg.val j.val : ZMod 2)) + 1 := by ring

  -- Rewrite flipped sum in terms of original bits
  have flip_decomp : ∑ j : Fin n, (getBit (flipBit cfg i).val j.val : ZMod 2) =
                     ∑ j : Fin n, (getBit cfg.val j.val : ZMod 2) +
                     ∑ j : Fin n, (if j = i then (1 : ZMod 2) else 0) := by
    -- Step 1: Express flipped bits in terms of original + correction
    have term_eq : ∀ j : Fin n,
        (getBit (flipBit cfg i).val j.val : ZMod 2) =
        (getBit cfg.val j.val : ZMod 2) + (if j = i then 1 else 0) := by
      intro j
      by_cases h_eq : j = i
      · -- Case j = i: bit flipped
        rw [h_eq]
        have flip_eq := flipBit_changes_target cfg i
        simp [flip_eq]
        -- Goal: ↑(1 - getBit cfg.val i.val) = ↑(getBit cfg.val i.val) + 1
        have hb := getBit_le_one cfg.val i.val
        interval_cases hb' : getBit cfg.val i.val
        · -- getBit = 0: (1-0) = 0 + 1
          simp
        · -- getBit = 1: (1-1) = 1 + 1 in ZMod 2
          norm_num [hb']
          -- In ZMod 2: 1 + 1 = 2 ≡ 0
          decide
      · -- Case j ≠ i: bit unchanged
        have preserve := flipBit_preserves_others cfg i j (Ne.symm h_eq)
        simp [h_eq, preserve]

    -- Step 2: Sum the equality
    calc ∑ j : Fin n, (getBit (flipBit cfg i).val j.val : ZMod 2)
        = ∑ j : Fin n, ((getBit cfg.val j.val : ZMod 2) + (if j = i then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact term_eq j
      _ = ∑ j : Fin n, (getBit cfg.val j.val : ZMod 2) + ∑ j : Fin n, (if j = i then (1 : ZMod 2) else 0) := by
            rw [Finset.sum_add_distrib]

  rw [flip_decomp]

  -- Step 3: Show the correction term equals 1
  have correction_eq_one : ∑ j : Fin n, (if j = i then (1 : ZMod 2) else 0) = 1 := by
    -- Only i contributes 1, all others contribute 0
    rw [Finset.sum_ite]
    simp
    -- Goal: 1 * Finset.card (Finset.filter (fun j => j = i) Finset.univ) = 1
    have : Finset.filter (fun j => j = i) Finset.univ = {i} := by
      ext j
      simp
    rw [this]
    simp

  rw [correction_eq_one]

/-- **Flipping a bit changes parity** (main theorem).

    **Proof Strategy**: Use ZMod 2 arithmetic where flipping adds 1,
    then convert back to Nat using the fact that parity is 0 or 1. -/
lemma flipBit_changes_parity {n : Nat} (cfg : Fin (2^n)) (i : Fin n) :
    parity (flipBit cfg i) = 1 - parity cfg := by
  -- Convert to ZMod 2
  have h_flip_zmod : (parity (flipBit cfg i) : ZMod 2) = (parity cfg : ZMod 2) + 1 := by
    rw [parity_eq_parityZMod_val, parity_eq_parityZMod_val]
    exact parityZMod_flip cfg i

  -- parity is 0 or 1, so we can case split
  have h_parity_bound := parity_lt_two cfg
  have h_flip_bound := parity_lt_two (flipBit cfg i)

  -- Case analysis on parity cfg
  interval_cases h_parity : parity cfg
  · -- Case: parity cfg = 0
    -- Goal: parity (flipBit cfg i) = 1 - 0 = 1
    -- From h_flip_zmod: (parity (flipBit cfg i) : ZMod 2) = (0 : ZMod 2) + 1 = 1
    have h_flip_zmod_0 : (parity (flipBit cfg i) : ZMod 2) = 1 := by
      simpa using h_flip_zmod
    -- Since parity (flipBit cfg i) < 2 and ≡ 1 (mod 2), it must be 1
    interval_cases h_flip_eq : parity (flipBit cfg i)
    · -- If parity (flipBit cfg i) = 0, then (0 : ZMod 2) = 1, contradiction
      have : (0 : ZMod 2) = 1 := by simp at h_flip_zmod_0
      norm_num at this
    · -- parity (flipBit cfg i) = 1, goal: 1 = 1 - 0
      rfl
  · -- Case: parity cfg = 1
    -- Goal: parity (flipBit cfg i) = 1 - 1 = 0
    -- From h_flip_zmod: (parity (flipBit cfg i) : ZMod 2) = (1 : ZMod 2) + 1 = 0
    have h_flip_zmod_1 : (parity (flipBit cfg i) : ZMod 2) = 0 := by
      simpa using h_flip_zmod
    -- Since parity (flipBit cfg i) < 2 and ≡ 0 (mod 2), it must be 0
    interval_cases h_flip_eq : parity (flipBit cfg i)
    · -- parity (flipBit cfg i) = 0, goal: 0 = 1 - 1
      rfl
    · -- If parity (flipBit cfg i) = 1, then (1 : ZMod 2) = 0, contradiction
      have : (1 : ZMod 2) = 0 := by simp at h_flip_zmod_1
      norm_num at this

/-! ## Core Lower Bound Theorem (1-bit Discriminator) -/

/-- **PARITY LOWER BOUND**: Incomplete observation → ∃ indistinguishable configs
    with different parities.

    **Statement**: If observation is incomplete (< R bits read), then ∃ cfg1, cfg2:
    1. Agree on all observed positions (indistinguishable to algorithm)
    2. Have different parities (parity(cfg1) ≠ parity(cfg2))

    **Proof**: Flip any unobserved bit → configs agree on observed, parity flips.

    ---

    **Why 1-bit parity is acceptable here**:

    Parity is a DISCRIMINATOR: it witnesses that cfg1 ≠ cfg2.
    The hardness comes LATER via A2 injectivity on full R-bit vectors:

    ```
    parity(cfg1) ≠ parity(cfg2)           [this theorem]
      → cfg1 ≠ cfg2                        [trivial]
      → encodeSeed(cfg1) ≠ encodeSeed(cfg2) [A2: 2^R hardness]
    ```

    Parity is convenient because flipping ANY bit flips parity.
    Any 1-bit function with this property would work equally well.

    --- -/
theorem parity_requires_all_bits
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (obs : Observation L v)
    (h_incomplete : obs.isIncomplete)
    : ∃ (cfg1 cfg2 : Fin (2^(L.R v))),
        obs.configsAgree cfg1 cfg2 ∧
        parity cfg1 ≠ parity cfg2 := by
  -- **STEP 1**: Get unobserved position
  -- Since incomplete, ∃i such that i ∉ obs.read_positions
  unfold Observation.isIncomplete at h_incomplete

  -- obs.read_positions.card < L.R v means it's not the full set
  have h_exists_missing : ∃ (i : Fin (L.R v)), i ∉ obs.read_positions := by
    by_contra h_all
    push_neg at h_all
    -- If all positions are in obs.read_positions, then card = R_v
    have h_complete : obs.read_positions = Finset.univ := by
      ext i
      simp [h_all]
    -- But then card = R_v, contradicting h_incomplete
    have h_card : obs.read_positions.card = L.R v := by
      rw [h_complete]
      exact Finset.card_fin _
    -- h_incomplete says card < R_v, contradiction
    rw [h_card] at h_incomplete
    exact Nat.lt_irrefl _ h_incomplete

  obtain ⟨i_unobs, h_unobs⟩ := h_exists_missing

  -- **STEP 2**: Construct witness configurations
  -- Take cfg1 = 0 (arbitrary choice, any config works)
  let cfg1 : Fin (2^(L.R v)) := ⟨0, by
    apply Nat.pow_pos
    norm_num
  ⟩

  -- Define cfg2 by flipping the unobserved bit
  let cfg2 : Fin (2^(L.R v)) := flipBit cfg1 i_unobs

  -- **STEP 3**: Prove they agree on observed positions
  have h_agree : obs.configsAgree cfg1 cfg2 := by
    unfold Observation.configsAgree
    intro i h_obs
    -- For any observed position i, show cfg1 and cfg2 have same bit
    by_cases h_eq : i = i_unobs
    · -- Case: i = i_unobs (the flipped position)
      -- But i_unobs is unobserved, so this case is vacuous
      rw [h_eq] at h_obs
      exact absurd h_obs h_unobs
    · -- Case: i ≠ i_unobs
      -- Flipping i_unobs doesn't affect other positions
      have h_ne : i_unobs ≠ i := Ne.symm h_eq
      have h_preserve := flipBit_preserves_others cfg1 i_unobs i h_ne
      -- h_preserve says: getBit (flipBit cfg1 i_unobs) i = getBit cfg1 i
      -- But cfg2 = flipBit cfg1 i_unobs, so: getBit cfg2 i = getBit cfg1 i
      -- We need: getBit cfg1 i = getBit cfg2 i
      exact h_preserve.symm

  -- **STEP 4**: Prove they have different parities
  have h_parity_diff : parity cfg1 ≠ parity cfg2 := by
    -- Flipping any bit changes parity
    have h_flip : parity cfg2 = 1 - parity cfg1 :=
      flipBit_changes_parity cfg1 i_unobs
    -- Therefore parity cfg1 ≠ parity cfg2
    intro h_eq
    -- If equal, then substituting cfg1 for cfg2 in h_flip:
    -- parity cfg1 = 1 - parity cfg1
    have h_bad : parity cfg1 = 1 - parity cfg1 := by
      calc parity cfg1
          = parity cfg2 := h_eq
        _ = 1 - parity cfg1 := h_flip
    -- But parity is 0 or 1, so this is impossible
    cases h_parity : parity cfg1 with
    | zero =>
      rw [h_parity] at h_bad
      norm_num at h_bad
    | succ n =>
      -- parity is always 0 or 1 (by mod 2)
      have h_bound : parity cfg1 < 2 := parity_lt_two cfg1
      rw [h_parity] at h_bound
      have : n.succ < 2 := h_bound
      have : n < 1 := Nat.succ_lt_succ_iff.mp this
      interval_cases n
      · -- n = 0, so parity cfg1 = 1
        rw [h_parity] at h_bad
        norm_num at h_bad

  -- **CONCLUSION**: cfg1 and cfg2 are the witnesses
  exact ⟨cfg1, cfg2, h_agree, h_parity_diff⟩

/-! ## Configuration Collision (Identity-Based Lower Bound)

**Key insight**: The identity-based proof above is stronger than needed.
For FP ≠ FNP (search hardness), we only need to show that incomplete
observation creates *indistinguishable but different* configurations.

The identity function (all bits) is also "bit-sensitive" - flipping any
bit produces a different configuration. This provides a more direct proof
that connects cleanly to the OWF inversion problem.

**Mathematical relationship**:
- `parity_requires_all_bits`: cfg1 ≠ cfg2 implied by parity difference
- `incomplete_obs_has_collision`: cfg1 ≠ cfg2 directly (stronger statement)

Both theorems use the same construction (flipBit on unobserved position),
but the collision theorem is simpler and sufficient for search hardness.
-/

/-- **CONFIGURATION COLLISION**: Incomplete observation → indistinguishable
    but different configurations.

    **Theorem**: If observation at node v is incomplete (didn't read all R_v bits),
    then there exist two configurations that:
    1. Agree on all observed positions (indistinguishable from partial view)
    2. Are different (cfg1 ≠ cfg2)

    **Proof Sketch**:
    1. Since incomplete, ∃ unobserved position i ∉ obs.read_positions
    2. Take cfg1 = 0
    3. Define cfg2 = flipBit cfg1 i (flip the unobserved bit)
    4. cfg1 and cfg2 agree on all observed positions (i wasn't observed)
    5. cfg1 ≠ cfg2 (we flipped a bit!)

    **This is the PUBLIC INTERFACE** for the lower bound:
    - Returns cfg1 ≠ cfg2 directly (no mention of parity)
    - Sufficient for hardness via A2 injectivity: cfg1 ≠ cfg2 → different seeds
    - External callers should use this, not `parity_requires_all_bits`

    **Internal mechanism** (for digest difference proofs):
    - `parity_requires_all_bits` returns parity(cfg1) ≠ parity(cfg2)
    - Used to derive fgDigestBit(cfg1) ≠ fgDigestBit(cfg2)
    - Parity is just a discriminator; hardness comes from A2 on full vectors

    **This is sufficient for the 2^R lower bound!** -/
theorem incomplete_obs_has_collision
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (obs : Observation L v)
    (h_incomplete : obs.isIncomplete)
    : ∃ (cfg1 cfg2 : Fin (2^(L.R v))),
        obs.configsAgree cfg1 cfg2 ∧
        cfg1 ≠ cfg2 := by
  -- **STEP 1**: Get unobserved position (same as parity version)
  unfold Observation.isIncomplete at h_incomplete

  have h_exists_missing : ∃ (i : Fin (L.R v)), i ∉ obs.read_positions := by
    by_contra h_all
    push_neg at h_all
    have h_complete : obs.read_positions = Finset.univ := by
      ext i
      simp [h_all]
    have h_card : obs.read_positions.card = L.R v := by
      rw [h_complete]
      exact Finset.card_fin _
    rw [h_card] at h_incomplete
    exact Nat.lt_irrefl _ h_incomplete

  obtain ⟨i_unobs, h_unobs⟩ := h_exists_missing

  -- **STEP 2**: Construct witness configurations (same as parity version)
  let cfg1 : Fin (2^(L.R v)) := ⟨0, by apply Nat.pow_pos; norm_num⟩
  let cfg2 : Fin (2^(L.R v)) := flipBit cfg1 i_unobs

  -- **STEP 3**: Prove they agree on observed positions (same as parity version)
  have h_agree : obs.configsAgree cfg1 cfg2 := by
    unfold Observation.configsAgree
    intro i h_obs
    by_cases h_eq : i = i_unobs
    · rw [h_eq] at h_obs
      exact absurd h_obs h_unobs
    · have h_ne : i_unobs ≠ i := Ne.symm h_eq
      have h_preserve := flipBit_preserves_others cfg1 i_unobs i h_ne
      exact h_preserve.symm

  -- **STEP 4**: Prove they are different (SIMPLER than parity version!)
  have h_diff : cfg1 ≠ cfg2 := by
    intro h_eq
    -- If cfg1 = cfg2, then their bits at position i_unobs are equal
    have h_bits_eq : getBit cfg1.val i_unobs.val = getBit cfg2.val i_unobs.val := by
      rw [h_eq]
    -- But flipBit changes the target bit
    have h_flip := flipBit_changes_target cfg1 i_unobs
    -- cfg2 = flipBit cfg1 i_unobs, so:
    -- getBit cfg2.val i_unobs.val = 1 - getBit cfg1.val i_unobs.val
    rw [h_flip] at h_bits_eq
    -- So: getBit cfg1.val i_unobs.val = 1 - getBit cfg1.val i_unobs.val
    -- This is impossible for 0 or 1
    have h_bound := getBit_le_one cfg1.val i_unobs.val
    interval_cases h_bit : getBit cfg1.val i_unobs.val
    · -- bit = 0: 0 = 1 - 0 = 1, contradiction
      simp at h_bits_eq
    · -- bit = 1: 1 = 1 - 1 = 0, contradiction
      simp at h_bits_eq

  -- **CONCLUSION**: cfg1 and cfg2 are the witnesses
  exact ⟨cfg1, cfg2, h_agree, h_diff⟩

/-- **Corollary**: Incomplete observation implies config collision via parity.

    This connects the two theorems: parity difference implies config difference.
    Useful for backward compatibility with existing proofs. -/
theorem parity_diff_implies_config_diff
    {n : Nat} (cfg1 cfg2 : Fin (2^n))
    (h_parity : parity cfg1 ≠ parity cfg2)
    : cfg1 ≠ cfg2 := by
  intro h_eq
  rw [h_eq] at h_parity
  exact h_parity rfl

/-! ## Corollaries -/

/-- **Contrapositive form**: Correct parity computation requires complete observation.

    **Interpretation**: If algorithm correctly computes parity for ALL configurations,
    then it must have observed all bit positions.

    **Application to FG**: If witness finder correctly computes FG digest (= parity)
    for all possible emergent configurations, then observation must be complete. -/
theorem correct_parity_requires_complete_observation
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (obs : Observation L v)
    (h_correct : ∀ (cfg : Fin (2^(L.R v))),
      ∃ (output : Nat), output = parity cfg ∧
        (∀ (cfg' : Fin (2^(L.R v))), obs.configsAgree cfg cfg' →
          output = parity cfg'))
    : obs.isComplete := by
  -- Proof by contrapositive
  by_contra h_not_complete

  -- If not complete, then incomplete (exhaustive dichotomy)
  cases observation_complete_or_incomplete obs with
  | inl h => exact h_not_complete h
  | inr h_incomplete =>
    -- By parity lower bound, ∃ indistinguishable configs with different parities
    have ⟨cfg1, cfg2, h_agree, h_parity_diff⟩ :=
      parity_requires_all_bits L v obs h_incomplete

    -- But correctness says cfg1's output works for cfg2 (they agree)
    obtain ⟨output1, h_eq1, h_works⟩ := h_correct cfg1
    have h_output_cfg2 : output1 = parity cfg2 := h_works cfg2 h_agree

    -- So parity cfg1 = output1 = parity cfg2
    have h_parities_eq : parity cfg1 = parity cfg2 := by
      rw [← h_eq1, h_output_cfg2]

    -- Contradiction with h_parity_diff
    exact h_parity_diff h_parities_eq

/-! ## Module Status

**Completed**:
- Parity function definitions (list and finset variants)
- Bit flipping operations (flipBit with properties)
- **Core theorem**: `parity_requires_all_bits` (incomplete → ∃ indistinguishable configs with diff parity)
- **Contrapositive**: `correct_parity_requires_complete_observation` (correct parity → complete obs)

**Sorries**: 2 non-critical proofs (step 1 verified without these):
1. `flipBit_changes_parity`: Proof that flipping one bit changes parity (~50 lines)
2. Depends on this: `parity_requires_all_bits` uses flipBit_changes_parity

**Step 1 status**: Verified - `localParity_eq_parity` compiles. It only needs:
- `parity` definition
- `getBit` helper
- `parity_lt_two`
The complex flip/observation proofs are not needed for step 1.

**Dependencies**:
- ObservationModel.lean (provides Observation, configsAgree, completeness)
- Mathlib.Data.Finset.Basic (finset operations)
- Mathlib.Data.Fin.Basic (bounded naturals)

**Key Innovation**:
This module doesn't just state "parity requires all bits" as folklore—it provides
constructive witnesses (cfg1, cfg2) that an incomplete observation cannot distinguish.
This constructive approach is essential for Stage 3, where we'll use these witnesses
to prove FG indistinguishability.

**Next stage**: FGIndistinguishability.lean (Stage 3)
- Will apply this theorem to FG gates specifically
- Connect to KeyednessProperty: indistinguishable configs → duplicate states → contradiction
- Complete the proof chain: correctness → complete observation → exponential state visits

**Mathematical Significance**:
The parity lower bound is one of the simplest non-trivial lower bounds in complexity theory.
Every deterministic algorithm computing parity must query all n inputs—no clever
strategy can reduce the query complexity. This fundamental limitation is what makes
FG gates effective: the digest wiring forces unavoidable work.

**Proof Technique**:
Classic adversarial argument: for any incomplete query set, adversary constructs
two inputs (differing only on unqueried positions) with opposite parities. This
forces the algorithm to make one of two errors, proving impossibility of correctness
without complete queries.

**Effort**: ~6 hours (parity formalization + bit manipulation + core theorem)
**Risk**: Low (standard complexity theory result, well-understood)
-/

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms parityZMod_flip
#print axioms parity_requires_all_bits
#print axioms incomplete_obs_has_collision
#print axioms parity_diff_implies_config_diff
#print axioms correct_parity_requires_complete_observation

end LStar.StructuralOWF.Foundations
