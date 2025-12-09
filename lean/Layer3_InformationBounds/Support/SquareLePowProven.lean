import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! ## SquareLePowProven: k² ≤ 2^k Complete Proof (Axiom Elimination)

**Purpose**: Eliminate axioms from RanksExponential.lean via rigorous proof of k² ≤ 2^k for k ≥ 4.

**Main results** (§8):
- two_k_plus_one_le_pow: Helper (2k+1 ≤ 2^k for k ≥ 11, strong induction + base cases)
- square_le_pow_step: Inductive step (IH: k² ≤ 2^k → (k+1)² ≤ 2^{k+1})
- square_le_pow_all: Main theorem (k² ≤ 2^k for k ≥ 4)

**Proof technique**: Strong induction with explicit base cases (k ∈ [4,10] by decide, k ∈ [11,20] by interval_cases).

**Result**:  0 axioms, 0 sorries - complete rigorous proof

**Usage**: Import instead of using axioms in RanksExponential.lean

**Trust boundary**: 3 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

/-! ## Helper Lemma: Linear vs Exponential -/

/-- **Helper**: 2k+1 ≤ 2^k for k ≥ 11

This is the key to the inductive step: showing that the "overhead" from
(k+1)² = k² + 2k + 1 is absorbed by the doubling from 2^k to 2^(k+1).

**Proof**: Strong induction with explicit base cases k ∈ [11, 20]
-/
lemma two_k_plus_one_le_pow : ∀ k ≥ 11, 2 * k + 1 ≤ 2^k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h_k
    -- Base cases: k ∈ [11, 20] by computation
    by_cases h_small : k ≤ 20
    case pos =>
      have h_range : 11 ≤ k ∧ k ≤ 20 := ⟨h_k, h_small⟩
      interval_cases k <;> decide
    case neg =>
      -- k ≥ 21: use induction
      push_neg at h_small
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h_k'_ge_11 : k' ≥ 11 := by omega
      have h_k'_lt : k' < k := by omega

      -- Apply IH: 2*k' + 1 ≤ 2^k'
      have ih_k' : 2 * k' + 1 ≤ 2^k' := ih k' h_k'_lt h_k'_ge_11

      -- Prove for k = k' + 1
      calc 2 * k + 1
          = 2 * (k' + 1) + 1 := by rw [hk']
        _ = 2 * k' + 3 := by ring
        _ ≤ 2 * k' + 1 + 2 := by omega
        _ ≤ 2^k' + 2 := by omega
        _ ≤ 2^k' + 2^k' := by {
            have : 2 ≤ 2^k' := by {
              have h_2_11 : 2 ≤ 2^11 := by decide
              calc 2
                  ≤ 2^11 := h_2_11
                _ ≤ 2^k' := Nat.pow_le_pow_right (by omega) h_k'_ge_11
            }
            omega
          }
        _ = 2 * 2^k' := by ring
        _ = 2^(k'+1) := by {
            have : 2^(k'+1) = 2^k' * 2 := Nat.pow_succ _ _
            omega
          }
        _ = 2^k := by rw [← hk']

/-! ## Inductive Step -/

/-- **Inductive step**: If k² ≤ 2^k, then (k+1)² ≤ 2^(k+1) for k ≥ 11

Uses `two_k_plus_one_le_pow` to show that 2k+1 ≤ 2^k, allowing us to
double both sides and absorb the overhead.
-/
lemma square_le_pow_step (k : Nat) (h_k : k ≥ 11) (ih : k^2 ≤ 2^k) :
    (k+1)^2 ≤ 2^(k+1) := by
  have h_linear : 2 * k + 1 ≤ 2^k := two_k_plus_one_le_pow k h_k
  calc (k+1)^2
      = k^2 + 2*k + 1 := by ring
    _ ≤ 2^k + (2*k + 1) := by omega
    _ ≤ 2^k + 2^k := by omega
    _ = 2 * 2^k := by ring
    _ = 2^(k+1) := by {
        have : 2^(k+1) = 2^k * 2 := Nat.pow_succ _ _
        omega
      }

/-! ## Main Theorem -/

/-- **Main theorem**: k² ≤ 2^k for all k ≥ 4

**Proof**: Strong induction
- Base cases: k ∈ [4, 20] verified by computation
- Inductive step: Uses `square_le_pow_step` for k ≥ 20

**Result**: Zero axioms, zero sorries.

**Replaces**: The axiom `threshold_past_50` from RanksExponential.lean
-/
theorem square_le_pow_all : ∀ k ≥ 4, k^2 ≤ 2^k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h_k
    -- Base cases: k ∈ [4, 20] by computation
    by_cases h_small : k ≤ 20
    case pos =>
      have h_range : 4 ≤ k ∧ k ≤ 20 := ⟨h_k, h_small⟩
      interval_cases k <;> decide
    case neg =>
      -- k ≥ 21: use induction
      push_neg at h_small
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h_k'_ge_4 : k' ≥ 4 := by omega
      have h_k'_ge_11 : k' ≥ 11 := by omega
      have h_k'_lt : k' < k := by omega

      -- Apply IH: k'² ≤ 2^k'
      have ih_k' : k'^2 ≤ 2^k' := ih k' h_k'_lt h_k'_ge_4

      -- Apply inductive step
      have h_step : (k'+1)^2 ≤ 2^(k'+1) := square_le_pow_step k' h_k'_ge_11 ih_k'

      -- Substitute k = k' + 1
      calc k^2
          = (k'+1)^2 := by rw [← hk']
        _ ≤ 2^(k'+1) := h_step
        _ = 2^k := by rw [← hk']

/-! ## Corollaries -/

/-- **Corollary**: k² ≤ 2^k for all k ≥ 7 -/
theorem square_le_pow_from_seven (k : Nat) (h : k ≥ 7) : k^2 ≤ 2^k :=
  square_le_pow_all k (by omega : k ≥ 4)

/-- **Corollary**: k² ≤ 2^k for all k ≥ 51

This is the specific statement needed for RanksFlat.lean's asymptotic case.
-/
theorem square_le_pow_from_fifty_one (k : Nat) (h : k ≥ 51) : k^2 ≤ 2^k :=
  square_le_pow_all k (by omega : k ≥ 4)

/-! ## Axiom Verification

These theorems use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced - all proofs are constructive arithmetic.
-/

#print axioms square_le_pow_all
#print axioms square_le_pow_from_seven
#print axioms square_le_pow_from_fifty_one

end LStar.StructuralOWF.Foundations
