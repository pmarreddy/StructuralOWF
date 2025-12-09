import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Bitwise

/-! ## FiniteEncoding: Fixed-Width Bitstring Seeds (Fin (2^k))

**Purpose**: Finite seed types enabling SCL exponential bounds |State| ≥ 2^λ.

**Main Definitions**:
- `Seed k`: k-bit seeds = Fin (2^k) (finite by construction)
- `get s j`: Extract j-th bit from seed (Boolean bit access)
- `ofBits k f`: Construct seed from bit function f : Fin k → Bool
- `cast h s`: Transport seeds across type equality

**Why Fin (2^k)?**: Automatic Fintype instance (enables SCL cardinality theorem).
```
Seed k = Fin (2^k) → |Seed k| = 2^k definitionally → SCL_node applies
```

**Alternative (NOT used)**: ByteString or Nat (infinite types, can't instantiate Fintype, SCL inapplicable).

**Key Theorem** (axiom elimination): `ofBits_injective` - bijection between seeds and bit functions (PROVEN from Fin properties, not assumed).

**Paper**: §2.3 "Seed representation", §6 "L* encoding".

**Key Theorems and Their Roles**:

**1. `card : Fintype.card (Seed k) = 2^k`**
   - **Mathematical content**: The k-bit seed space has exactly 2^k elements
   - **Why crucial**: Establishes exponential cardinality used in SCL bounds
   - **Proof**: Direct from Fintype.card_fin (definitional for Fin types)

**2. `ext : (∀j, get s1 j = get s2 j) → s1 = s2`**
   - **Mathematical content**: Seeds equal iff all bits equal (bit-level extensionality)
   - **Why crucial**: Enables injectivity proofs via bit-by-bit reasoning
   - **Proof**: Induction on k with bit reconstruction via division algorithm
   - **Application**: Essential for proving Plant function injectivity (OWF security)

**3. `ofBits_get : get (ofBits k f) j = f j`**
   - **Mathematical content**: Round-trip property—constructing seed from bits then
     reading bits recovers original values
   - **Why crucial**: Proves ofBits is a constructive bijection Fin k → Bool ≅ Seed k
   - **Proof**: Induction on k with shift-right cancellation lemmas
   - **Application**: Shows assignments (Fin k → Bool) isomorphic to seeds (Seed k)

**4. `ofBits_injective : Function.Injective (ofBits k)`**
   - **Mathematical content**: Different bit patterns produce different seeds
   - **Why crucial**: Core injectivity for encoding assignments to natural numbers
   - **Proof**: Follows from ext and ofBits_get (bit equality implies seed equality)
   - **Application**: Used in CNF.encodeAssignment_injective (OWF security theorem)

**Proof Technique**:
Structural induction on seed width k combined with bitwise arithmetic:
- **Bit extraction**: Use Nat.shiftRight and mod 2 to isolate individual bits
- **Bit reconstruction**: Division algorithm (n = 2*(n/2) + n%2) to rebuild from bits
- **Inductive step**: Shift-right by 1 reduces k+1 case to k case
- **No axioms**: Pure computational reasoning with Mathlib bitwise operations

**Paper References**:
- §6 "L* Construction" - Seed types in instance structure
- §2.2 "Emergence rank R_v" - Measured in bits (log₂ of seed space size)
- Appendix A "Encoding injectivity" - Critical for A2 (Injectivity) property
- §9.1 "Plant function" - Uses seeds as random coins for instance generation
- §7.0.1 "SCL framework" - Fintype requirement for cardinality bounds

**Dependencies**:
- Mathlib.Data.Nat.Bitwise: Bit shift and modular arithmetic
- Mathlib.Data.Fin.Basic: Finite type Fin n
- Mathlib.Data.Fintype.Card: Cardinality API for finite types

**Applications in Proof Chain**:
- **Layer 1 (Construction)**: SeedChain, Pools, EmergenceMatrix all use Seed types
- **Layer 1 (Properties)**: A2 (Injectivity) uses ofBits_injective transitively
- **Layer 0 (SCL)**: NodeData.State instances built from Seed enable SCL_node theorem
- **Layer 2 (OWF)**: Plant function injectivity traces back to ofBits_injective
- **Layer 5 (Complexity)**: Witness encoding (CNF.encodeAssignment) uses Seed representation

**Trust Boundary**: All theorems proven from Mathlib primitives—no custom axioms
introduced. The finite seed representation eliminates the need for axiomatizing
boundedness of randomness in the OWF construction.
-/

namespace LStar

/-- **Seed**: k-bit finite seed type for randomness and state encoding.

    **Type Definition**: Seed k = Fin (2^k)

    **Mathematical Content**:
    A k-bit seed is a natural number in the range [0, 2^k - 1]. The type Seed k wraps
    Fin (2^k), which automatically provides:
    - Finite cardinality: Exactly 2^k distinct seeds
    - Decidable equality: Seeds can be compared in finite time
    - Fintype instance: Enables cardinality reasoning for SCL bounds

    **Why Fin (2^k)**:
    Using Fin rather than raw Nat provides type-level guarantees:
    - s : Seed k automatically satisfies s.val < 2^k (no need to prove bounds)
    - Type system prevents mixing seeds of different widths
    - Fintype instance inherited from Fin enables exponential cardinality theorems

    **Example Seeds**:
    - Seed 3 = {0, 1, 2, 3, 4, 5, 6, 7} (3-bit seeds, 2^3 = 8 elements)
    - Seed 10 = {0, ..., 1023} (10-bit seeds, 2^10 = 1024 elements)
    - Seed 256 = {0, ..., 2^256 - 1} (large parameter size, 256-bit seeds)

    **Usage in L* Construction**:
    - **Seed chains**: Parent seeds combined to derive child seeds
    - **Pools**: Designated/emergence seed pools for each node
    - **State spaces**: NodeData.State built from Seed products
    - **OWF construction**: Plant function uses seeds as randomness
-/
def Seed (k : Nat) := Fin (2^k)

namespace Seed

variable {k : Nat}

/-- **Decidable equality**: Seeds can be compared for equality in finite time.
    Inherited from Fin's decidable equality. Essential for computational verification. -/
instance instDecidableEq (k : Nat) : DecidableEq (Seed k) := by
  unfold Seed; infer_instance

/-- **Inhabited instance**: Seed spaces are non-empty (zero seed always exists).
    The default element is 0 : Seed k, representing the all-zeros bit pattern. -/
instance instInhabited (k : Nat) : Inhabited (Seed k) :=
  ⟨⟨0, Nat.two_pow_pos k⟩⟩

/-- **Fintype instance**: Seed k is a finite type with computable enumeration.
    Inherited from Fin (2^k). This is THE critical instance enabling SCL cardinality bounds.
    Without this, we couldn't prove |State| ≥ 2^λ for NodeData constructed from seeds. -/
instance instFintype (k : Nat) : Fintype (Seed k) := by
  unfold Seed; infer_instance

/-- **Exponential cardinality**: The k-bit seed space has exactly 2^k elements.

    **Theorem Statement**: Fintype.card (Seed k) = 2^k

    **Mathematical Content**:
    This theorem establishes the exponential cardinality that powers the SCL framework:
    - |Seed k| = 2^k (not just ≤ or ≥, but exact equality)
    - Exponential in k: doubling k quadruples the seed space
    - Foundation for 2^λ bounds in SCL_node theorem

    **Why Crucial for SCL**:
    The SCL framework proves |State| ≥ 2^λ via injection from assignments to states.
    When State is built from Seed λ (as in L* construction), this theorem provides:
    ```
    |State| ≥ |Seed λ| = 2^λ  (exponential lower bound)
    ```

    **Proof**: Direct from Fintype.card_fin (Mathlib theorem for Fin types).
    No induction needed—definitional for finite types.
-/
theorem card (k : Nat) : Fintype.card (Seed k) = 2 ^ k := by
  simp [Seed, Fintype.card_fin]

/-- **Bit extraction**: Read the j-th bit of a seed (0-indexed, LSB first).

    **Function**: get s j returns Bool indicating whether bit j is set in seed s

    **Mathematical Content**:
    Interprets seed s.val as k-bit binary number and extracts bit at position j:
    - Bit 0 (LSB): Least significant bit (coefficient of 2^0)
    - Bit j: Coefficient of 2^j in binary expansion
    - Bit k-1 (MSB): Most significant bit (coefficient of 2^(k-1))

    **Implementation**: (s.val >>> j.val) % 2 = 1
    - `>>>` is right shift by j positions (divides by 2^j, discarding remainder)
    - `% 2` extracts the low bit (0 or 1)
    - `= 1` converts to Bool (true if bit set, false otherwise)

    **Example**: For s.val = 13 (binary 1101 in 4-bit representation):
    - get s 0 = true  (LSB: 1101₂ & 1 = 1)
    - get s 1 = false (     1101₂ >> 1 = 110₂, & 1 = 0)
    - get s 2 = true  (     1101₂ >> 2 = 11₂,  & 1 = 1)
    - get s 3 = true  (MSB: 1101₂ >> 3 = 1₂,   & 1 = 1)

    **Usage in Extensionality**: The `ext` theorem uses bit-by-bit equality via `get`
    to prove seed equality—seeds equal iff all bits agree.
-/
def get {k : Nat} (s : Seed k) (j : Fin k) : Bool :=
  ((s.val >>> j.val) % 2 = 1)

/-- **Bit-level extensionality**: Seeds equal iff all bits equal.

    **Theorem Statement**: (∀j < k, get s1 j = get s2 j) → s1 = s2

    **Mathematical Content**:
    Seeds are uniquely determined by their bit patterns. If two seeds agree on all k bits,
    they must be the same seed. This is the fundamental extensionality principle for the
    Seed type—equality is characterized by bitwise equality.

    **Why Crucial**:
    Enables proving seed equality by bit-by-bit comparison rather than directly comparing
    natural number values. This is essential for:
    1. **Injectivity proofs**: Show f(x) = f(y) → x = y by showing all bits agree
    2. **ofBits injectivity**: Core theorem for assignment encoding security
    3. **Plant injectivity**: Traces back to this theorem via ofBits_injective

    **Proof Strategy**:
    Induction on seed width k with bit reconstruction via division algorithm:
    - **Base case (k=0)**: Both seeds are 0 (only value < 2^0 = 1)
    - **Inductive step (k+1)**:
      1. Extract LSB (least significant bit) via `val % 2`
      2. Extract high k bits via right-shift `val >>> 1`
      3. Apply IH to prove high bits equal
      4. Combine LSB equality + high bits equality via division algorithm:
         `val = 2*(val >>> 1) + val % 2`
      5. Both seeds reconstruct to same value → Fin.ext gives equality

    **Key Technique**: Division algorithm for natural numbers:
    ```
    n = 2*(n / 2) + n % 2  (for all n ∈ ℕ)
    ```
    This decomposes any number into "high bits" (n/2) and "low bit" (n%2), enabling
    inductive reasoning on bit patterns.

    **Paper Reference**: Appendix A "Encoding injectivity for OWF security" - This
    extensionality principle underlies all encoding injectivity arguments in the OWF construction.
-/
theorem ext {k : Nat} {s1 s2 : Seed k} (h : ∀ j : Fin k, get s1 j = get s2 j) : s1 = s2 := by
  -- Seeds are Fin (2^k), so extensionality reduces to showing s1.val = s2.val
  apply Fin.ext
  -- Induction on k
  induction k with
  | zero =>
      -- For k=0: both values are 0
      have : s1.val < 1 := s1.isLt
      have : s2.val < 1 := s2.isLt
      omega
  | succ k ih =>
      -- For k+1: compare LSB and then recurse on high bits
      -- Extract LSB
      have hlsb : (s1.val % 2 = 1) = (s2.val % 2 = 1) := by
        have := h ⟨0, Nat.succ_pos k⟩
        unfold get at this
        simp only [Nat.shiftRight_zero] at this
        -- this : decide (s1.val % 2 = 1) = decide (s2.val % 2 = 1)
        exact propext (decide_eq_decide.mp this)
      -- Extract high bits via shift-right by 1
      have hs1_half_lt : s1.val >>> 1 < 2 ^ k := by
        rw [Nat.shiftRight_eq_div_pow]
        calc s1.val / 2
            < 2^(k+1) / 2 := Nat.div_lt_div_of_lt_of_dvd (by omega) s1.isLt
          _ = 2^k := by rw [pow_succ]; omega
      have hs2_half_lt : s2.val >>> 1 < 2 ^ k := by
        rw [Nat.shiftRight_eq_div_pow]
        calc s2.val / 2
            < 2^(k+1) / 2 := Nat.div_lt_div_of_lt_of_dvd (by omega) s2.isLt
          _ = 2^k := by rw [pow_succ]; omega
      -- Apply IH to the shifted values
      have hhalves : (s1.val >>> 1) = (s2.val >>> 1) := by
        apply ih (s1 := ⟨s1.val >>> 1, hs1_half_lt⟩) (s2 := ⟨s2.val >>> 1, hs2_half_lt⟩)
        intro j
        have := h ⟨j.succ, Nat.succ_lt_succ j.isLt⟩
        unfold get
        unfold get at this
        simp only [Fin.val_succ] at this
        -- this : decide ((s1.val >>> (j.val + 1)) % 2 = 1) = decide ((s2.val >>> (j.val + 1)) % 2 = 1)
        -- Goal: decide (((s1.val >>> 1) >>> j.val) % 2 = 1) = decide (((s2.val >>> 1) >>> j.val) % 2 = 1)
        -- Use: a >>> (b + c) = (a >>> b) >>> c, with b=1, c=j.val
        convert this using 2 <;> (rw [← Nat.shiftRight_add]; simp [Nat.add_comm])
      -- Deduce LSB equality from hlsb
      have hbit_eq : s1.val % 2 = s2.val % 2 := by
        have h1 : s1.val % 2 < 2 := Nat.mod_lt _ (by omega)
        have h2 : s2.val % 2 < 2 := Nat.mod_lt _ (by omega)
        cases h1' : s1.val % 2
        · -- s1.val % 2 = 0
          cases h2' : s2.val % 2
          · rfl
          · rename_i n
            have : n = 0 := by omega
            subst this
            -- Now s1 % 2 = 0, s2 % 2 = 1, but hlsb says they're equal as bools
            rw [h1', h2'] at hlsb
            simp at hlsb
        · -- s1.val % 2 = succ n
          rename_i n
          have : n = 0 := by omega
          subst this
          -- s1.val % 2 = 1
          cases h2' : s2.val % 2
          · -- s2.val % 2 = 0, contradiction with hlsb
            rw [h1', h2'] at hlsb
            simp at hlsb
          · -- s2.val % 2 = succ m
            rename_i m
            have : m = 0 := by omega
            subst this
            rfl
      -- Reconstruct using division algorithm
      calc s1.val
          = 2 * (s1.val / 2) + s1.val % 2 := (Nat.div_add_mod s1.val 2).symm
        _ = 2 * (s1.val >>> 1) + s1.val % 2 := by rw [Nat.shiftRight_eq_div_pow]
        _ = 2 * (s2.val >>> 1) + s2.val % 2 := by rw [hhalves, hbit_eq]
        _ = 2 * (s2.val / 2) + s2.val % 2 := by rw [Nat.shiftRight_eq_div_pow]
        _ = s2.val := Nat.div_add_mod s2.val 2

/-- Two seeds are equal iff their bit-reading functions agree. -/
theorem ext_iff {k : Nat} {s1 s2 : Seed k} : s1 = s2 ↔ ∀ j : Fin k, get s1 j = get s2 j := by
  constructor
  · intro h j; rw [h]
  · exact ext

end Seed

/-! ## Seed Construction Utilities

Helper functions to build seeds from bit patterns and natural numbers.
-/

/-- **Build seed from natural number**: Interpret n as k-bit pattern (truncated/wrapped mod 2^k).

    **Function**: ofNat k n creates Seed k by taking n modulo 2^k

    **Example**:
    - ofNat 3 13 = 5 (13 mod 8 = 5, fits in 3 bits as 101₂)
    - ofNat 5 7 = 7 (7 mod 32 = 7, fits in 5 bits as 00111₂)

    **Use case**: Quick seed construction from literal constants or arithmetic results.
-/
def ofNat (k : Nat) (n : Nat) : Seed k :=
  ⟨n % (2^k), Nat.mod_lt n (Nat.two_pow_pos k)⟩

/-- **Build seed from bit function**: Construct k-bit seed from Boolean function f : Fin k → Bool.

    **Function**: ofBits k f creates Seed k where bit j equals f j

    **Mathematical Content**:
    Interprets the function f as a k-bit pattern and encodes it as a natural number:
    - Bit 0 (LSB): f 0 contributes 2^0 = 1 if true
    - Bit j: f j contributes 2^j if true
    - Bit k-1 (MSB): f (k-1) contributes 2^(k-1) if true
    - Result: Σⱼ (if f j then 2^j else 0) ∈ {0, ..., 2^k - 1}

    **Why Crucial**:
    ofBits provides the bijection (Fin k → Bool) ≅ Seed k that underlies:
    1. **Assignment encoding**: CNF assignments (Nat → Bool) → Seed k
    2. **Injectivity**: ofBits_injective proves different bit patterns → different seeds
    3. **Round-trip**: ofBits_get proves get (ofBits k f) j = f j (perfect reconstruction)

    **Implementation**: Structural recursion on k (efficient computation)
    - Base (k=0): Return zero seed (no bits)
    - Step (k+1): Combine LSB (f 0) with recursively-encoded high k bits
      Result: 2*(high bits) + (LSB)

    **Example**:
    - ofBits 3 (fun j => [true, false, true][j]) = 5 (binary 101₂)
    - ofBits 4 (fun j => j.val % 2 = 0) = 5 (binary 0101₂ = alternate bits)

    **Paper Reference**: Appendix A "Encoding injectivity" - This bijection is security-critical
    for OWF construction (Plant function injectivity).
-/
def ofBits : (k : Nat) → (Fin k → Bool) → Seed k
  | 0, _ => ⟨0, by simp⟩
  | k+1, f =>
    let f0 : Bool := f ⟨0, Nat.succ_pos k⟩
    let f' : Fin k → Bool := fun i => f i.succ
    let high := ofBits k f'
    let b : Nat := if f0 then 1 else 0
    -- bound: high.val ≤ 2^k - 1, hence 2*high.val + b < 2^(k+1)
    have hle : high.val ≤ 2 ^ k - 1 := by
      have hlt : high.val < 2 ^ k := high.isLt
      -- 2^k = (2^k - 1) + 1 since 2^k > 0
      have : high.val < (2 ^ k - 1) + 1 := by omega
      exact (Nat.lt_succ_iff.mp this)
    have hb_le : b ≤ 1 := by
      by_cases hf0 : f0
      · simp [b, hf0]
      · simp [b, hf0]
    have hb_lt : b < 2 := by
      by_cases hf0 : f0 <;> simp [b, hf0]
    ⟨2 * high.val + b, by
    -- Show 2*high.val + b < 2^(k+1)
    have : 2 * high.val + b ≤ 2 * (2 ^ k - 1) + 1 := by omega
    -- 2*(2^k - 1) + 1 = 2^(k+1) - 1 < 2^(k+1)
    calc 2 * high.val + b
        ≤ 2 * (2 ^ k - 1) + 1 := this
      _ < 2 ^ (k+1) := by omega⟩

/-- All-zero seed. -/
def zero (k : Nat) : Seed k := ⟨0, Nat.two_pow_pos k⟩

/-- Mod-2 for double-add: reduces the low bit when you have 2*a + b. -/
@[simp] theorem mod_two_double_add (a b : Nat) :
    (2 * a + b) % 2 = b % 2 := by
  calc
    (2 * a + b) % 2
      = ((2 * a) % 2 + b % 2) % 2 := by rw [Nat.add_mod]
    _ = (0 + b % 2) % 2 := by rw [Nat.mul_mod]; simp
    _ = b % 2 := by simp

/-- Shift-right helper (succ): cancels the *2 and low bit in shiftRight by (j.succ). -/
@[simp] theorem shiftRight_succ_double_add (a b j : Nat) (hb : b < 2) :
    (2 * a + b) >>> j.succ = a >>> j := by
  simp only [Nat.shiftRight_eq_div_pow, pow_succ]
  -- Goal: (2 * a + b) / (2 ^ j * 2) = a / 2 ^ j

  -- Key insight: Since b < 2, we have b ∈ {0, 1}. Prove by cases.
  have hb_cases : b = 0 ∨ b = 1 := by omega
  cases hb_cases with
  | inl h_b_eq_0 =>
    -- Case b = 0
    rw [h_b_eq_0, Nat.add_zero]
    have : 2 ^ j * 2 = 2 * 2 ^ j := Nat.mul_comm (2 ^ j) 2
    rw [this]
    exact Nat.mul_div_mul_left a (2 ^ j) (by omega : 0 < 2)

  | inr h_b_eq_1 =>
    -- Case b = 1
    rw [h_b_eq_1]
    -- When b = 1: Need to show remainder of (2*a) allows adding 1
    -- Key fact: (2*a) % (2*2^j) is even, so remainder + 1 < 2*2^j
    have d_eq : 2 ^ j * 2 = 2 * 2 ^ j := Nat.mul_comm (2 ^ j) 2
    rw [d_eq]

    -- Define d for clarity
    have d_pos : 0 < 2 * 2 ^ j := by
      have : 0 < 2 := by omega
      have : 0 < 2 ^ j := Nat.two_pow_pos j
      omega

    -- Apply division algorithm to 2*a
    have div_2a := Nat.div_add_mod (2 * a) (2 * 2 ^ j)
    -- 2 * a = (2*a / (2*2^j)) * (2*2^j) + (2*a % (2*2^j))

    -- Key: remainder is even (since 2*a and 2*2^j are both even)
    -- Proof: By Nat.div_add_mod, we have 2*a = q*(2*2^j) + r where r = (2*a) % (2*2^j)
    -- Since 2*a is even and q*(2*2^j) is even, r must be even
    have r_even : Even ((2 * a) % (2 * 2 ^ j)) := by
      -- The remainder of an even number divided by an even divisor is even
      -- We prove this by showing the remainder is 0 mod 2
      have h_even_mod : (2 * a) % (2 * 2 ^ j) % 2 = 0 := by
        -- Use the fact that n % (2*m) % 2 = n % 2 for any m > 0
        have : (2 * a) % (2 * 2 ^ j) % 2 = (2 * a) % 2 := by
          rw [Nat.mod_mod_of_dvd]
          exact ⟨2 ^ j, rfl⟩
        rw [this]
        simp
      -- Convert from n % 2 = 0 to Even n
      rw [Nat.even_iff]
      exact h_even_mod

    -- Show remainder + 1 < divisor, so quotient unchanged when adding 1
    have r_bound : (2 * a) % (2 * 2 ^ j) + 1 < 2 * 2 ^ j := by
      have r_lt : (2 * a) % (2 * 2 ^ j) < 2 * 2 ^ j := Nat.mod_lt (2 * a) d_pos
      -- Since remainder is even, it's at most (2*2^j - 2), so remainder + 1 ≤ 2*2^j - 1 < 2*2^j
      cases r_even with | intro k hk =>
        -- (2*a) % (2*2^j) = k + k, and k + k < 2*2^j
        calc (2 * a) % (2 * 2 ^ j) + 1
            = (k + k) + 1 := by rw [hk]
          _ < 2 * 2 ^ j := by
              have : k + k < 2 * 2 ^ j := by rw [← hk]; exact r_lt
              omega

    -- Therefore (2*a + 1) / (2*2^j) = (2*a) / (2*2^j)
    have quot_eq : (2 * a + 1) / (2 * 2 ^ j) = (2 * a) / (2 * 2 ^ j) := by
      -- Since remainder + 1 < divisor, adding 1 doesn't change quotient
      have h_div_zero : ((2 * a) % (2 * 2 ^ j) + 1) / (2 * 2 ^ j) = 0 := by
        apply Nat.div_eq_zero_iff.mpr; right; exact r_bound
      -- Rewrite 2*a using division algorithm
      have : 2 * a + 1 = ((2*a) / (2*2^j)) * (2*2^j) + ((2*a) % (2*2^j) + 1) := by
        -- div_2a : (2 * 2 ^ j) * (2 * a / (2 * 2 ^ j)) + 2 * a % (2 * 2 ^ j) = 2 * a
        have h1 : 2 * a = (2 * 2 ^ j) * ((2*a) / (2*2^j)) + (2*a) % (2*2^j) := div_2a.symm
        calc 2 * a + 1
            = ((2 * 2 ^ j) * ((2*a) / (2*2^j)) + (2*a) % (2*2^j)) + 1 := by
                rw [← h1]
          _ = ((2*a) / (2*2^j)) * (2*2^j) + ((2*a) % (2*2^j) + 1) := by
              have : (2 * 2 ^ j) * ((2*a) / (2*2^j)) = ((2*a) / (2*2^j)) * (2*2^j) := Nat.mul_comm _ _
              omega
      rw [this]
      -- Commute to match Nat.add_mul_div_left pattern
      have : ((2*a) / (2*2^j)) * (2*2^j) = (2*2^j) * ((2*a) / (2*2^j)) := Nat.mul_comm _ _
      rw [Nat.add_comm, this, Nat.add_mul_div_left _ _ d_pos, h_div_zero]
      simp

    rw [quot_eq]
    -- Now show (2*a) / (2*2^j) = a / 2^j
    -- Rewrite to match pattern for Nat.mul_div_mul_left: m*n / (m*k) = n/k
    have : 2 * a / (2 * 2 ^ j) = a / 2 ^ j := by
      conv_lhs => rw [show 2 * 2 ^ j = 2 * (2 ^ j) from rfl]
      exact Nat.mul_div_mul_left a (2 ^ j) (by omega : 0 < 2)
    exact this

/-- **ofBits preserves bits**: Round-trip property for seed construction.

    **Theorem Statement**: get (ofBits k f) j = f j

    **Mathematical Content**:
    Constructing a seed from bit function f and then reading bit j yields the original value f j.
    This is the round-trip property proving ofBits is a faithful encoding:
    ```
    f : Fin k → Bool  ⟶[ofBits]  Seed k  ⟶[get j]  Bool
    ↓                                                 ↓
    f j  ←───────────────────────────────────────────┘
    ```

    **Why Crucial**:
    Combined with `ext` theorem, this proves ofBits is injective:
    - If ofBits k f1 = ofBits k f2, then get (ofBits k f1) j = get (ofBits k f2) j for all j
    - By this theorem: f1 j = f2 j for all j
    - Therefore: f1 = f2 (function extensionality)

    **Proof Strategy**:
    Structural induction on k matching ofBits definition:
    - **Base case (k=0)**: No bits to check (j : Fin 0 is empty type)
    - **Inductive step (k+1)**:
      - LSB (j=0): Direct computation shows (2*high + b) % 2 = b
      - High bits (j>0): Shift-right cancellation gives (2*high + b) >>> j.succ = high >>> j,
        then apply IH to high bits

    **Simp attribute**: Marked @[simp] to enable automatic rewriting in bit-manipulation proofs.

    **Paper Reference**: Appendix A "Encoding injectivity for OWF security" - This round-trip
    property is essential for proving Plant function injectivity.
-/
@[simp] theorem ofBits_get (k : Nat) (f : Fin k → Bool) (j : Fin k) :
    Seed.get (ofBits k f) j = f j := by
  revert j
  induction k with
  | zero =>
      intro j; cases j with | mk jv hj => cases hj
  | succ k ih =>
      intro j
      -- Unfold and simplify the structural ofBits (k+1) f
      unfold ofBits
      -- Split over j = 0 and j = succ j
      cases j using Fin.cases with
      | zero =>
          -- LSB: (2 * high + b) % 2 = b % 2, and b = 1 iff f 0
          simp only [Seed.get, Nat.shiftRight_zero, Fin.val_zero]
          -- mod_two_double_add is @[simp] so it fires automatically
          cases h : f 0
          · simp [h]  -- false case: 0 % 2 = 0
          · simp [h]  -- true case: 1 % 2 = 1
      | succ j =>
          -- Higher bits: use induction hypothesis and helper lemma
          simp only [Seed.get, Fin.val_succ]
          -- Goal: decide ((2 * high.val + b) >>> j.succ % 2 = 1) = f j.succ
          -- shiftRight_succ_double_add gives: (2 * a + b) >>> j.succ = a >>> j
          have hb : (if f ⟨0, Nat.succ_pos k⟩ then 1 else 0) < 2 := by
            by_cases h : f ⟨0, Nat.succ_pos k⟩
            · rw [if_pos h]; omega
            · rw [if_neg h]; omega
          simp only [shiftRight_succ_double_add _ _ _ hb]
          -- Now use IH: ofBits_get for high bits
          exact ih (fun i => f i.succ) j

/-- **ofBits extensionality**: Functions agreeing on all bits produce the same seed.

    **Theorem**: (∀j, f j = g j) → ofBits k f = ofBits k g

    **Proof**: Apply Seed.ext (bit-level extensionality) and ofBits_get (round-trip property).
-/
theorem ofBits_ext (k : Nat) (f g : Fin k → Bool) (h : ∀ j, f j = g j) :
  ofBits k f = ofBits k g := by
  apply Seed.ext
  intro j
  rw [ofBits_get, ofBits_get, h]

/-- **ofBits injectivity**: Different bit patterns produce different seeds.

    **Theorem Statement**: Function.Injective (ofBits k)
    (Equivalently: ofBits k f = ofBits k g → f = g)

    **Mathematical Content**:
    The encoding ofBits : (Fin k → Bool) → Seed k is injective—different Boolean functions
    map to different seeds. Combined with `ofBits_get` (surjectivity on range), this proves
    ofBits is a bijection between k-bit Boolean functions and k-bit seeds.

    **Why Crucial - Security Foundation for OWF**:
    This theorem is the ULTIMATE SOURCE of Plant function injectivity, which is critical
    for OWF security. The proof chain:

    1. **This theorem**: ofBits k injective on Boolean functions
    2. **CNF.encodeAssignment_injective**: Assignment encoding injective (uses ofBits via Seed)
    3. **Plant injectivity**: Distinct witnesses → distinct planted instances (uses assignment encoding)
    4. **OWF security**: Inverting Plant produces valid witness (requires injectivity)

    Without this theorem, we'd need to axiomatize encoding injectivity, expanding trust boundary.

    **Proof Strategy**:
    Assume ofBits k f = ofBits k g. Goal: f = g.
    - By function extensionality, suffices to show f j = g j for all j
    - From ofBits k f = ofBits k g, get Seed.get (ofBits k f) j = Seed.get (ofBits k g) j
    - By ofBits_get theorem: f j = Seed.get (ofBits k f) j and g j = Seed.get (ofBits k g) j
    - Therefore: f j = g j for all j ∎

    **Trust Boundary**: Proven theorem (no axioms beyond Lean foundations). Eliminates need
    to axiomatize "encoding preserves distinctness" in the OWF construction.

    **Paper Reference**: Appendix A "Encoding injectivity for OWF security" - Explicitly identified
    as security-critical property. This formalization provides a complete proof rather than
    assuming injectivity as an axiom.
-/
theorem ofBits_injective (k : Nat) : Function.Injective (ofBits k) := by
  intros f g h
  ext j
  have : Seed.get (ofBits k f) j = Seed.get (ofBits k g) j := by rw [h]
  rw [ofBits_get, ofBits_get] at this
  exact this

/-!
## Infrastructure for axiom elimination

Lemmas for working with seeds across type boundaries and Vector/Array indexing.
-/

namespace Seed

/-- Cast a seed when widths are provably equal. -/
def cast {k1 k2 : Nat} (h : k1 = k2) (s : Seed k1) : Seed k2 :=
  h ▸ s

/-- Casting preserves bit reading (when indices are also transported). -/
@[simp] theorem cast_get {k1 k2 : Nat} (h : k1 = k2) (s : Seed k1) (j : Fin k2) :
    get (cast h s) j = get s (h ▸ j) := by
  subst h
  rfl

/-- Cast composed with ofBits. -/
theorem cast_ofBits {k1 k2 : Nat} (h : k1 = k2) (f : Fin k1 → Bool) :
    cast h (ofBits k1 f) = ofBits k2 (fun j => f (h.symm ▸ j)) := by
  subst h
  simp [cast]

/-- ofBits with function precomposed with Fin.cast. -/
theorem ofBits_fin_cast_comp {k1 k2 : Nat} (h : k1 = k2) (f : Fin k1 → Bool) :
    ofBits k2 (f ∘ Fin.cast h.symm) = cast h (ofBits k1 f) := by
  subst h
  rfl

/-- Casting with inverse proofs cancels: cast h (cast h.symm s) = s -/
@[simp] theorem cast_cast_symm {k1 k2 : Nat} (h : k1 = k2) (s : Seed k2) :
    cast h (cast h.symm s) = s := by
  subst h
  rfl

/-- Inverse cancellation: cast h.symm (cast h s) = s -/
@[simp] theorem cast_symm_cast {k1 k2 : Nat} (h : k1 = k2) (s : Seed k1) :
    cast h.symm (cast h s) = s := by
  subst h
  rfl

/-- Casting preserves the underlying value. -/
@[simp] theorem val_cast {k1 k2 : Nat} (h : k1 = k2) (s : Seed k1) :
    (cast h s).val = s.val := by
  subst h
  rfl

/-- Transport for `get` across equal seeds and equal index values.
If `s1 = s2` and `j1.val = j2.val`, then the read bits are equal. -/
theorem get_eq_of_val_eq {k : Nat} {s1 s2 : Seed k} {j1 j2 : Fin k}
    (hs : s1 = s2) (hj : j1.val = j2.val) :
    get s1 j1 = get s2 j2 := by
  subst hs
  unfold get
  simp [hj]

-- Note: A heterogeneous transport for `get` can be added if needed.

end Seed

/-!
## Vector and Array indexing lemmas

Bridge theorems for working with Vector.ofFn and Array operations.
-/

namespace Vector

variable {α : Type*} {n : Nat}

/-- Accessing Vector.ofFn at an index gives the function value. -/
theorem get_ofFn (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get, Array.getElem_ofFn]

/-- Vector.ofFn is injective when indexed through an equivalence. -/
theorem get_ofFn_equiv {β : Type*} (e : Fin n ≃ β) (f : Fin n → α) (b : β) :
    (Vector.ofFn f).get (e.symm b) = f (e.symm b) := by
  rw [get_ofFn]

end Vector

/-! ## Axiom Verification

Comprehensive audit of finite seed encoding and security-critical theorems.

**Trust Boundary**: All theorems proven from standard Lean foundations—no custom axioms.
The finite seed representation (Fin (2^k)) provides automatic Fintype instances and
eliminates the need for axiomatizing boundedness of randomness in OWF construction.

**Key Achievement**: Three potential axioms ELIMINATED by proofs:
1. "Seeds determined by bits" → **PROVEN** (Seed.ext)
2. "Bit encoding faithful" → **PROVEN** (ofBits_get)
3. "Encoding preserves distinctness" → **PROVEN** (ofBits_injective)

Without these proofs, we'd axiomatize "distinct witnesses encode distinctly" for OWF security.
By proving rather than assuming, we shrink the trust boundary.
-/

-- Core type and instances (automatic from Fin)
#print axioms Seed.instDecidableEq
#print axioms Seed.instInhabited
#print axioms Seed.instFintype

-- Exponential cardinality theorem (enables SCL bounds)
#print axioms Seed.card

-- Bit extraction and extensionality
#print axioms Seed.get
#print axioms Seed.ext
#print axioms Seed.ext_iff

-- Seed construction and arithmetic helpers
#print axioms ofNat
#print axioms ofBits
#print axioms zero
#print axioms mod_two_double_add
#print axioms shiftRight_succ_double_add

-- Security-critical theorems (axiom elimination)
#print axioms ofBits_get
#print axioms ofBits_ext
#print axioms ofBits_injective

-- Infrastructure for type transport
#print axioms Seed.cast
#print axioms Seed.cast_get
#print axioms Seed.cast_ofBits
#print axioms Seed.get_eq_of_val_eq

-- Vector/Array bridge lemmas
#print axioms Vector.get_ofFn
#print axioms Vector.get_ofFn_equiv

end LStar
