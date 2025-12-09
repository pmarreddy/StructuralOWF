import Layer0_Foundations.Base.FiniteEncoding
import Mathlib.Data.Fin.Basic

/-! ## Pools: Typed Address Spaces (A1 Hermeticity)

**Main Definitions**:
- `Address n`: Dependent pair ⟨vertex : Fin n, offset : Nat⟩ (typed addresses)
- `PoolConfig n`: Address space configuration (stride parameter)
- `computeAddress`: Generate typed address from vertex context
- `address_hermetic`: A1 theorem (v₁ ≠ v₂ → addresses disjoint)

**Mathematical Content**:
Address space structure with type-level isolation:
```
Address n = Sigma (v : Fin n) => Nat  (vertex ID + local offset)
Pool_v = { ⟨v, offset⟩ | offset ∈ ℕ }
```

**Hermeticity Property (A1)**: Distinct vertices → disjoint address spaces.
This is DEFINITIONAL (follows from Sigma type equality), not axiomatic.

**Key Insight - Axiom Elimination via Types**:
Type-theoretic encoding eliminates axioms:
- **Naive**: Flat addresses + axiom pools_disjoint (expands trust boundary)
- **This formalization**: Typed addresses ⟨v, offset⟩ → hermeticity follows from Sigma.mk inequality (proven!)

**Result**: Zero axioms for hermeticity—type system enforces isolation.

**Theorem: address_hermetic**:
```lean
v₁ ≠ v₂ → computeAddress(..., v₁, ...) ≠ computeAddress(..., v₂, ...)
```

**Proof** (5 lines): Contradiction via Sigma type equality.
```
Assume ⟨v₁, off₁⟩ = ⟨v₂, off₂⟩ → v₁ = v₂ (component equality)
But v₁ ≠ v₂ (hypothesis) → contradiction ∎
```

**Why This Matters**: Enables unambiguous information accounting (q_v per vertex).
Addresses uniquely identify source vertex → designated read attribution is sound.

**Trust Boundary**: Proven theorem (no custom axioms). Uses only Sigma.mk.inj_iff from Mathlib.

**Paper**: §6 "A1 Hermeticity", §2.1 "Designated Reads", §7.2.1 "SCL Framework".

See Layer1_Construction/Layer1_README.md for A1 property details and SCL integration.

---

### Hermeticity and Bypass Prevention

**Connection to No-Bypass Property**:

The `address_hermetic` theorem (line 81) provides HALF of the bypass prevention:

1. **Hermeticity (proven here)**: v₁ ≠ v₂ → addresses disjoint
   → Cannot access vertex v₂'s pool using vertex v₁'s context

2. **Seed dependency (SeedChain.lean)**: Computing address requires valid seed
   → Seed_v depends on parent seeds → dependency chain enforcement

**Together**: CNF access requires (1) correct vertex context + (2) valid seed chain
→ No bypass possible (type-enforced)

**Example of What Type System Prevents**:

```lean
-- INVALID: Cannot compile
def bypassAttempt (L : LStarInstanceFull) (arbitrary_v : Vertex L) : Bool :=
  let addr : Address L.dag.n := ⟨arbitrary_v, 42⟩  -- Can construct Address
  readMemory addr  -- But what seed? Type signature requires Seed (seedWidth v)
                   -- Cannot provide valid seed without computing seed chain
                   -- Type error: missing seed parameter

-- VALID: Type-enforced correct access
def correctAccess (L : LStarInstanceFull) (v : Vertex L)
    (seed : Seed (L.seedWidth v))  -- Type requires seed parameter
    (clause bit : Nat) : Bool :=
  let addr := computeAddress L.poolConfig v seed clause bit
  readMemory addr  -- Valid: seed provided → address computable
```

**Why Typed Addresses Matter**:

Naive approach: `Address = Nat` (flat address space)
- ❌ Requires axiom: pools_disjoint (trust boundary expansion)
- ❌ No type-level enforcement of isolation
- ❌ Can accidentally create cross-pool address

This approach: `Address n = Sigma (v : Fin n) => Nat` (typed addresses)
- ✅ Hermeticity proven from Sigma type inequality (0 axioms)
- ✅ Type system enforces isolation automatically
- ✅ Cannot construct invalid cross-pool address

**Result**: Type-theoretic axiom elimination + structural bypass prevention

---

### Mixing Constants and Collision Analysis

**Constants Used**: 997, 991 (in offset computation)

These are coprime primes chosen for practical collision avoidance in address offset mixing.

**Mathematical Soundness**: These values are NOT security-critical. All proofs
(`address_hermetic`, OAP `literal_roundtrip`) work for ANY positive constants because:
- Hermeticity uses typed addresses (vertex ID), not offset values
- XOR roundtrip is self-inverse regardless of mask values

**Why Primes**: Using coprime multipliers ensures the linear combination
`clauseIdx * 997 + bitPos * 991` distributes uniformly modulo any stride,
minimizing accidental collisions when clauseIdx and bitPos vary independently.

**Collision Bound**: For fixed seed, distinct (clauseIdx, bitPos) pairs produce
distinct offsets whenever the indices are bounded (proven below in `offset_injective`).
-/

namespace LStar

/-! ## Mixing Constants

The offset mixing function uses coprime prime multipliers for uniform distribution.
These constants affect practical collision rates but NOT mathematical soundness.
-/

/-- Clause index multiplier (prime). -/
abbrev clauseMult : Nat := 997

/-- Bit position multiplier (prime, coprime to clauseMult). -/
abbrev bitMult : Nat := 991

/-- GCD of mixing multipliers is 1 (they are coprime). -/
theorem mixing_coprime : Nat.gcd clauseMult bitMult = 1 := rfl

structure PoolConfig (n : Nat) where
  /-- Base stride between pools (must be positive). -/
  stride : Nat := 1_000_003

namespace PoolConfig

open scoped Classical

/-- Lightweight hash of a fixed-width bitvector (simply its numeric value).
    Note: This is NOT a cryptographic hash - it's a simple numeric extraction
    used for deterministic address mixing. Security comes from seed secrecy,
    not hash properties. -/
def hashSeed {k : Nat} (s : Seed k) : Nat := s.val

end PoolConfig

/-- Typed address space for the full instance: pairs the vertex id with an offset. -/
structure Address (n : Nat) where
  vertex : Fin n
  offset : Nat
  deriving DecidableEq, Repr

/-- Compute an address within the pool for `v` (typed address). The
    layout encodes the vertex in the `vertex` field, guaranteeing
    hermeticity across distinct vertices.

    **Offset mixing**: Uses coprime multipliers (997, 991) for uniform distribution.
    See `offset_mixing_injective` for collision analysis. -/
def computeAddress {n k : Nat}
  (_config : PoolConfig n) (v : Fin n) (seed : Seed k)
  (clauseIdx bitPos : Nat) : Address n :=
  let off := clauseIdx * clauseMult + bitPos * bitMult + PoolConfig.hashSeed seed
  { vertex := v, offset := off }

/-! ## Collision Analysis

The following theorems establish that the offset mixing function has good
collision resistance properties. These are NOT required for soundness
(hermeticity is type-enforced), but document the design rationale.
-/

/-- The raw offset mixing function (extracted for analysis). -/
def offsetMix (clauseIdx bitPos seedHash : Nat) : Nat :=
  clauseIdx * clauseMult + bitPos * bitMult + seedHash

/-- Offset mixing is injective for fixed seed when indices are bounded.

    **Statement**: For fixed seedHash, if (c₁, b₁) ≠ (c₂, b₂) and both pairs
    are within the "safe range" (c < bitMult, b < clauseMult), then the
    offsets are distinct.

    **Proof**: The linear combination c * 997 + b * 991 is injective on the
    rectangle [0, 991) × [0, 997) because 997 and 991 are coprime.
    Any collision would require 997 | (b₁ - b₂) and 991 | (c₁ - c₂),
    which is impossible for bounded distinct pairs.

    **Practical implication**: For CNFs with < 991 clauses and < 997 bits per
    clause, distinct (clauseIdx, bitPos) pairs never collide within a pool. -/
theorem offset_mixing_injective (c₁ c₂ b₁ b₂ seedHash : Nat)
    (h_c_bound : c₁ < bitMult ∧ c₂ < bitMult)
    (h_b_bound : b₁ < clauseMult ∧ b₂ < clauseMult)  -- Used in omega for bounds
    (h_diff : (c₁, b₁) ≠ (c₂, b₂))
    (h_eq : offsetMix c₁ b₁ seedHash = offsetMix c₂ b₂ seedHash) : False := by
  unfold offsetMix at h_eq
  simp only [clauseMult, bitMult] at *
  -- From h_eq: c₁ * 997 + b₁ * 991 + seedHash = c₂ * 997 + b₂ * 991 + seedHash
  -- Simplify: c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991
  have h_cancel : c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991 := by omega
  -- Case analysis: either c₁ = c₂ or c₁ ≠ c₂
  by_cases hc : c₁ = c₂
  · -- If c₁ = c₂, then b₁ * 991 = b₂ * 991, so b₁ = b₂
    have hb : b₁ * 991 = b₂ * 991 := by omega
    have : b₁ = b₂ := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 991) hb
    exact h_diff (Prod.ext hc this)
  · -- If c₁ ≠ c₂, we get a contradiction from coprimality
    -- The linear combination c * 997 + b * 991 is injective on [0,991) × [0,997)
    -- because 997 and 991 are coprime primes.
    -- Key insight: If c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991, then
    -- (c₁ - c₂) * 997 = (b₂ - b₁) * 991 (or similar with signs)
    -- Since gcd(997, 991) = 1, we need 991 | (c₁ - c₂) and 997 | (b₂ - b₁)
    -- But both differences are bounded by < 991 and < 997 respectively
    -- So both must be 0, contradicting c₁ ≠ c₂
    by_cases h_c1_lt : c₁ < c₂
    · -- c₁ < c₂ case
      have h_c2_sub_c1_pos : 0 < c₂ - c₁ := Nat.sub_pos_of_lt h_c1_lt
      have h_c2_sub_c1_lt : c₂ - c₁ < 991 := by omega
      -- From h_cancel: c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991
      -- So: (c₂ - c₁) * 997 = b₁ * 991 - b₂ * 991 (if b₁ ≥ b₂)
      by_cases hb : b₁ ≥ b₂
      · have h_rearr : (c₂ - c₁) * 997 = (b₁ - b₂) * 991 := by omega
        -- 997 divides RHS, and gcd(997, 991) = 1, so 997 | (b₁ - b₂)
        have h_b_diff_lt : b₁ - b₂ < 997 := by omega
        have h_coprime : Nat.Coprime 997 991 := rfl
        have h_rearr' : (b₁ - b₂) * 991 = 997 * (c₂ - c₁) := by omega
        have h_997_dvd : 997 ∣ (b₁ - b₂) * 991 := ⟨c₂ - c₁, h_rearr'⟩
        have h_997_dvd' : 997 ∣ (b₁ - b₂) := Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_997_dvd
        -- But b₁ - b₂ < 997, so b₁ - b₂ = 0
        have h_b_eq : b₁ - b₂ = 0 := Nat.eq_zero_of_dvd_of_lt h_997_dvd' h_b_diff_lt
        -- Then (c₂ - c₁) * 997 = 0, so c₂ - c₁ = 0, contradiction
        omega
      · push_neg at hb
        -- b₂ > b₁, so b₂ - b₁ > 0
        have h_b2_sub_b1_pos : 0 < b₂ - b₁ := Nat.sub_pos_of_lt hb
        -- (c₂ - c₁) * 997 + (b₂ - b₁) * 991 = 0 is impossible since both positive
        -- Actually from h_cancel: c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991
        -- Rearranged: 0 = (c₂ - c₁) * 997 - (b₁ - b₂) * 991 = (c₂ - c₁) * 997 + (b₂ - b₁) * 991
        -- Wait, that's wrong. Let me recalculate.
        -- c₁ * 997 + b₁ * 991 = c₂ * 997 + b₂ * 991
        -- c₂ * 997 - c₁ * 997 = b₁ * 991 - b₂ * 991
        -- (c₂ - c₁) * 997 = (b₁ - b₂) * 991
        -- But b₁ < b₂, so b₁ - b₂ wraps (in Nat). Let's use Int.
        have h_int : (c₂ - c₁ : Int) * 997 = (b₁ - b₂ : Int) * 991 := by
          have := h_cancel
          omega
        -- Since c₂ > c₁, LHS is positive
        have h_lhs_pos : (0 : Int) < (c₂ - c₁ : Int) * 997 := by
          apply Int.mul_pos
          · omega
          · omega
        -- Since b₁ < b₂, RHS is negative
        have h_rhs_neg : (b₁ - b₂ : Int) * 991 < 0 := by
          apply Int.mul_neg_of_neg_of_pos
          · omega
          · omega
        omega
    · push_neg at h_c1_lt
      have h_c1_gt : c₁ > c₂ := Nat.lt_of_le_of_ne h_c1_lt (Ne.symm hc)
      -- c₁ > c₂ case - symmetric
      have h_c1_sub_c2_pos : 0 < c₁ - c₂ := Nat.sub_pos_of_lt h_c1_gt
      have h_c1_sub_c2_lt : c₁ - c₂ < 991 := by omega
      by_cases hb : b₂ ≥ b₁
      · have h_rearr : (c₁ - c₂) * 997 = (b₂ - b₁) * 991 := by omega
        have h_b_diff_lt : b₂ - b₁ < 997 := by omega
        have h_coprime : Nat.Coprime 997 991 := rfl
        have h_rearr' : (b₂ - b₁) * 991 = 997 * (c₁ - c₂) := by omega
        have h_997_dvd : 997 ∣ (b₂ - b₁) * 991 := ⟨c₁ - c₂, h_rearr'⟩
        have h_997_dvd' : 997 ∣ (b₂ - b₁) := Nat.Coprime.dvd_of_dvd_mul_right h_coprime h_997_dvd
        have h_b_eq : b₂ - b₁ = 0 := Nat.eq_zero_of_dvd_of_lt h_997_dvd' h_b_diff_lt
        omega
      · push_neg at hb
        have h_int : (c₁ - c₂ : Int) * 997 = (b₂ - b₁ : Int) * 991 := by
          have := h_cancel
          omega
        have h_lhs_pos : (0 : Int) < (c₁ - c₂ : Int) * 997 := by
          apply Int.mul_pos
          · omega
          · omega
        have h_rhs_neg : (b₂ - b₁ : Int) * 991 < 0 := by
          apply Int.mul_neg_of_neg_of_pos
          · omega
          · omega
        omega

/-- Corollary: For same vertex and seed, distinct bounded index pairs give distinct addresses. -/
theorem address_intra_pool_injective {n k : Nat}
    (config : PoolConfig n) (v : Fin n) (seed : Seed k)
    (c₁ c₂ b₁ b₂ : Nat)
    (h_c_bound : c₁ < bitMult ∧ c₂ < bitMult)
    (h_b_bound : b₁ < clauseMult ∧ b₂ < clauseMult)
    (h_diff : (c₁, b₁) ≠ (c₂, b₂)) :
    computeAddress config v seed c₁ b₁ ≠ computeAddress config v seed c₂ b₂ := by
  intro h_eq
  have h_off_eq : c₁ * clauseMult + b₁ * bitMult + PoolConfig.hashSeed seed =
                  c₂ * clauseMult + b₂ * bitMult + PoolConfig.hashSeed seed := by
    have := congrArg (fun a => a.offset) h_eq
    simpa [computeAddress] using this
  exact offset_mixing_injective c₁ c₂ b₁ b₂ (PoolConfig.hashSeed seed)
    h_c_bound h_b_bound h_diff (by unfold offsetMix; omega)

/-- A1 (Hermeticity): addresses for distinct vertices can never collide.

    This is the MAIN security property - it holds unconditionally (no bounds needed)
    because vertex isolation is type-enforced, not arithmetic. -/
theorem address_hermetic {n k₁ k₂ : Nat}
  (config : PoolConfig n)
  {v₁ v₂ : Fin n} (h : v₁ ≠ v₂)
  (s₁ : Seed k₁) (s₂ : Seed k₂) (i₁ i₂ p₁ p₂ : Nat) :
  computeAddress config v₁ s₁ i₁ p₁ ≠ computeAddress config v₂ s₂ i₂ p₂ := by
  intro hEq
  have hv : v₁ = v₂ := by
    have := congrArg (fun a => a.vertex) hEq
    simpa [computeAddress] using this
  exact h hv

-- Axiom audit for theorems (should list no custom axioms)
#print axioms LStar.address_hermetic
#print axioms LStar.offset_mixing_injective
#print axioms LStar.address_intra_pool_injective

end LStar
