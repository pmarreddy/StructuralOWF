import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer5_Applications.PvsNP.ComplexityClasses.PPTAdversary

/-! ## MathlibPolyTimeBridge: Equivalence to Mathlib Polynomial Time

**Purpose**: Prove that the project's polynomial time definition is equivalent
to Mathlib's Polynomial-based definition.

**Project definition (PPTAdversary)**: `∃ C k, C > 0 ∧ k > 0 ∧ ∀ n, f n ≤ C * (n + 1) ^ k`
**Weaker form (used in equivalence)**: `∃ C k, C > 0 ∧ ∀ n, f n ≤ C * (n + 1) ^ k`
**Mathlib style**: `∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n`

**Key theorems**:
- `polyBoundToPolynomial`: Convert C*(n+1)^k to Polynomial ℕ
- `polyBoundToPolynomial_eval`: Evaluation correctness
- `polynomial_has_poly_bound`: Any polynomial has a C*(n+1)^k bound
- `poly_time_equiv`: Bidirectional equivalence (weaker form ↔ Mathlib)
- `PPTAdversary.poly_time_matches_mathlib`: PPTAdversary satisfies the stronger form

**Note on k > 0**: The equivalence uses the weaker form without k > 0 because:
- Constant polynomials have degree 0 (k = 0 is valid)
- PPTAdversary explicitly requires k > 0 for non-degeneracy
- `PPTAdversary.poly_time_matches_mathlib` verifies the stronger form holds

**Trust boundary**: Uses only standard Mathlib axioms (propext, Quot.sound, Classical.choice).
No domain-specific axioms introduced.

See Layer4_Operational/Layer4_README.md.
-/

namespace LStar.MathlibBridge

open Polynomial

/-!
## Part 1: Project Format → Mathlib Format

Convert `C * (n + 1) ^ k` to `Polynomial ℕ`.
-/

/-- Convert uniform polynomial bound C*(n+1)^k to a Mathlib Polynomial.

    Given constants C and k, constructs the polynomial C * (X + 1)^k
    which evaluates to C * (n + 1)^k at any natural number n. -/
noncomputable def polyBoundToPolynomial (C k : ℕ) : Polynomial ℕ :=
  C • (X + 1) ^ k

/-- The polynomial C*(X+1)^k evaluates to C*(n+1)^k at n. -/
theorem polyBoundToPolynomial_eval (C k n : ℕ) :
    (polyBoundToPolynomial C k).eval n = C * (n + 1) ^ k := by
  simp only [polyBoundToPolynomial, eval_smul, eval_pow, eval_add, eval_X, eval_one]
  ring

/-- Forward direction: If f is bounded by C*(n+1)^k, it's bounded by a polynomial. -/
theorem poly_bound_implies_polynomial_bound {f : ℕ → ℕ} (C k : ℕ)
    (h : ∀ n, f n ≤ C * (n + 1) ^ k) :
    ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n := by
  use polyBoundToPolynomial C k
  intro n
  rw [polyBoundToPolynomial_eval]
  exact h n

/-!
## Part 2: Mathlib Format → Project Format

Show any polynomial p(n) is bounded by C*(n+1)^(deg p) for some C.
-/

/-- Helper: (n+1)^k dominates n^j for j ≤ k. -/
lemma pow_le_pow_succ_of_le {n j k : ℕ} (hjk : j ≤ k) :
    n ^ j ≤ (n + 1) ^ k := by
  calc n ^ j ≤ (n + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ n) j
    _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos n) hjk

/-- Sum of coefficients of a polynomial. -/
noncomputable def coeffSum (p : Polynomial ℕ) : ℕ :=
  p.support.sum (fun i => p.coeff i)

/-- Any polynomial p(n) is bounded by (coeffSum p) * (n+1)^(natDegree p).

    This is the key lemma for the reverse direction. -/
theorem polynomial_bounded_by_coeff_sum (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ (coeffSum p + 1) * (n + 1) ^ p.natDegree := by
  -- p.eval n = sum over i of coeff(i) * n^i
  rw [eval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
  -- Each term coeff(i) * n^i ≤ coeff(i) * (n+1)^(natDegree p)
  calc (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i * n ^ i)
      ≤ (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i * (n + 1) ^ p.natDegree) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Nat.mul_le_mul_left
        apply pow_le_pow_succ_of_le
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      _ = (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i) * (n + 1) ^ p.natDegree := by
        rw [Finset.sum_mul]
      _ ≤ (coeffSum p + 1) * (n + 1) ^ p.natDegree := by
        apply Nat.mul_le_mul_right
        -- For Polynomial ℕ, coeff i = 0 for i ∉ support, so range sum = support sum
        -- Need: range_sum ≤ coeffSum + 1
        unfold coeffSum
        -- Key insight: summing over range gives same as support (zeros outside support)
        have h_eq : (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i) =
                    p.support.sum (fun i => p.coeff i) := by
          -- support ⊆ range (natDegree + 1) for any polynomial
          have hsub : p.support ⊆ Finset.range (p.natDegree + 1) := by
            intro i hi
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hi)
          -- For i ∈ range but i ∉ support, coeff i = 0 (by definition of support)
          rw [← Finset.sum_subset hsub]
          intro i _ hi_not_supp
          exact notMem_support_iff.mp hi_not_supp
        rw [h_eq]
        omega

/-- Any polynomial has a uniform polynomial bound of the form C*(n+1)^k. -/
theorem polynomial_has_poly_bound (p : Polynomial ℕ) :
    ∃ C k, C > 0 ∧ ∀ n, p.eval n ≤ C * (n + 1) ^ k := by
  use coeffSum p + 1, p.natDegree
  constructor
  · omega
  · exact polynomial_bounded_by_coeff_sum p

/-!
## Part 3: Main Equivalence Theorem
-/

/-- **Main Theorem**: Project's polynomial time definition is equivalent to
    Mathlib's Polynomial-based definition.

    This establishes that:
    - Any function bounded by C*(n+1)^k is bounded by some Polynomial ℕ
    - Any function bounded by a Polynomial ℕ is bounded by some C*(n+1)^k

    Therefore, the two definitions of "polynomial time" are interchangeable. -/
theorem poly_time_equiv {f : ℕ → ℕ} :
    (∃ C k, C > 0 ∧ ∀ n, f n ≤ C * (n + 1) ^ k) ↔
    (∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n) := by
  constructor
  · -- Forward: C*(n+1)^k → Polynomial
    rintro ⟨C, k, _, hf⟩
    exact poly_bound_implies_polynomial_bound C k hf
  · -- Backward: Polynomial → C*(n+1)^k
    rintro ⟨p, hf⟩
    obtain ⟨C, k, hC, hp⟩ := polynomial_has_poly_bound p
    use C, k, hC
    intro n
    calc f n ≤ p.eval n := hf n
      _ ≤ C * (n + 1) ^ k := hp n

/-!
## Part 4: Connection to PPTAdversary
-/

open LStar.Complexity in
/-- Any PPTAdversary's time bound can be expressed as a Mathlib Polynomial.

    This connects the project's PPTAdversary structure to Mathlib's polynomial
    infrastructure, showing they use equivalent notions of polynomial time. -/
theorem PPTAdversary.time_bound_as_polynomial
    {α β γ : Type} [Sized α] [Sized β] (A : PPTAdversary α β γ) :
    ∃ p : Polynomial ℕ, ∀ n, A.time_bound n ≤ p.eval n := by
  -- PPTAdversary has fields C, k with poly : ∀ n, time_bound n ≤ C * (n + 1) ^ k
  use polyBoundToPolynomial A.C A.k
  intro n
  rw [polyBoundToPolynomial_eval]
  exact A.poly n

open LStar.Complexity in
/-- PPTAdversary's polynomial bound witnesses the equivalence. -/
theorem PPTAdversary.poly_time_matches_mathlib
    {α β γ : Type} [Sized α] [Sized β] (A : PPTAdversary α β γ) :
    (∃ C k, C > 0 ∧ k > 0 ∧ ∀ n, A.time_bound n ≤ C * (n + 1) ^ k) := by
  exact ⟨A.C, A.k, A.h_C_pos, A.h_k_pos, A.poly⟩

/-!
## Part 5: Axiom Verification

Verify the trust boundary claim: only standard Mathlib axioms used.
-/

#check poly_time_equiv
#check PPTAdversary.time_bound_as_polynomial

-- Axiom verification for trust boundary claim
#print axioms poly_time_equiv
#print axioms polynomial_bounded_by_coeff_sum
#print axioms PPTAdversary.time_bound_as_polynomial
#print axioms PPTAdversary.poly_time_matches_mathlib

end LStar.MathlibBridge
