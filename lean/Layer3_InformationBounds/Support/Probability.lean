import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Field

/-! ## Probability: Asymptotics Helpers (Exponential Dominates Polynomial)

**Purpose**: Probability/asymptotics lemmas for Phase 4 security reduction—exponential dominance over polynomials.

**Main result** (§8, §1.2): exp_dominates_poly - exponential c^n eventually dominates any polynomial C·n^k for c > 1.

**Proof technique**: Mathlib's asymptotics (tendsto_exp_mul_div_rpow_atTop) with b = log c → for large x: C ≤ exp(log c · x) / x^k → convert to natural numbers.

**Key lemmas**:
- exp_dominates_poly: ∃ N0, ∀ n ≥ N0, C·n^k ≤ c^n (proven via Mathlib filters)
- poly_lt_exp_eventually: Strict inequality version

**Axiom-free**: Statements proven against Mathlib (~80 lines proof)

**Trust boundary**: 2 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations.Probability

open scoped Classical BigOperators
open Finset

/-!
Exponential dominates polynomial: standard Mathlib-backed facts.

We provide concrete eventual dominance lemmas. Proofs can be derived via
asymptotics: `((fun n => c^n) / (fun n => n^k)) → ∞` for `c > 1`.
These are classic results and available via Mathlib's filter machinery.
-/

/-! Exponential dominance over polynomials

We rely on Mathlib’s standard asymptotics: for any `c > 1`, there exists
`N0` such that for all `n ≥ N0`, `C · n^k ≤ c^n`. The wrapper theorems
below use that fact. -/

/-- Exponential `c^n` eventually dominates any polynomial `C·n^k` for `c > 1`.

We derive this from Mathlib's asymptotics: `exp (b * x) / x^s → +∞` as `x → +∞` for any real
`s` and any `b > 0` (`tendsto_exp_mul_div_rpow_atTop`). Taking `b = log c` with `c > 1`, and
specializing to the eventual threshold set `Ici C`, we obtain for large enough `x` that
`C ≤ exp (log c * x) / x^(k : ℝ)`. For natural `n` beyond a suitable threshold, we convert this
to `(C : ℝ) * (n : ℝ)^k ≤ c^(n : ℝ)` using positivity of `(n : ℝ)^(k : ℝ)`, `le_div_iff`, and the
identity `exp (log c * n) = c^n`. -/
theorem exp_dominates_poly (c : ℝ) (hc : 1 < c) (C k : ℕ) :
  ∃ N0 : ℕ, ∀ n ≥ N0, (C : ℝ) * (n : ℝ) ^ k ≤ c ^ (n : ℝ) := by
  classical
  -- Set b = log c (positive since 1 < c)
  have hb : 0 < Real.log c := Real.log_pos hc
  have h_tendsto :
      Filter.Tendsto (fun x : ℝ => Real.exp ((Real.log c) * x) / x ^ (k : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_exp_mul_div_rpow_atTop (s := (k : ℝ)) (b := Real.log c) hb
  -- Eventually: C ≤ exp (log c * x) / x^(k:ℝ)
  have h_ev : ∀ᶠ x in Filter.atTop,
      (C : ℝ) ≤ Real.exp ((Real.log c) * x) / x ^ (k : ℝ) :=
    (Filter.tendsto_atTop.1 h_tendsto) (C : ℝ)
  -- Instantiate the eventual statement with an explicit real threshold R1
  rcases Filter.eventually_atTop.1 h_ev with ⟨R1, hR1⟩
  -- Choose a natural threshold N ≥ R1, and ensure n ≥ 1 for strict positivity
  obtain ⟨N, hN⟩ := exists_nat_ge R1
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  -- Relate n (as ℝ) to R1
  have hx_ge_R1 : R1 ≤ (n : ℝ) := by
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    exact le_trans hN this
  -- Apply the eventual bound at x = n
  have h_bound : (C : ℝ) ≤
      Real.exp ((Real.log c) * (n : ℝ)) / (n : ℝ) ^ (k : ℝ) := hR1 _ hx_ge_R1
  -- Since n ≥ 1, (n : ℝ) > 0 hence (n : ℝ)^(k:ℝ) > 0
  have hn_pos : 0 < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    exact lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) this
  have hpow_pos : 0 < (n : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos hn_pos _
  -- Multiply the inequality by (n : ℝ)^(k:ℝ) via le_div_iff₀
  have h_mul : (C : ℝ) * (n : ℝ) ^ (k : ℝ)
      ≤ Real.exp ((Real.log c) * (n : ℝ)) :=
    (le_div_iff₀ hpow_pos).1 h_bound
  -- Convert rpow with nat exponent and rewrite exp(log c * n) = c^n
  have hpow_nat : (n : ℝ) ^ (k : ℝ) = (n : ℝ) ^ k := Real.rpow_natCast (n : ℝ) k
  have hc_pos : 0 < c := lt_trans (zero_lt_one : (0 : ℝ) < 1) hc
  have h_exp_as_pow : Real.exp ((Real.log c) * (n : ℝ)) = c ^ (n : ℝ) := by
    rw [Real.rpow_def_of_pos hc_pos, mul_comm]
  -- Finish
  rwa [← hpow_nat, ← h_exp_as_pow]

/-- Exponential `c^n` eventually dominates linear `n` for `c > 1`. -/
theorem exp_dominates_linear (c : ℝ) (hc : 1 < c) :
  ∃ N0 : ℕ, ∀ n ≥ N0, (n : ℝ) ≤ c ^ (n : ℝ) := by
  classical
  -- Specialize the polynomial dominance with C=1, k=1.
  obtain ⟨N0, h⟩ := exp_dominates_poly c hc 1 1
  exact ⟨N0, by intro n hn; simpa using h n hn⟩

/-- Exponential eventually dominates any polynomial: for every `k` and
constant multiplier `C`, and any base `c > 1`, there exists `N` such that
`C · n^k ≤ c^n` holds for all `n ≥ N` (over reals, comparing via coercions).

This is the standard calculus fact used to separate poly upper bounds
from exponential lower bounds in security reductions. -/
theorem poly_vs_exp_contradiction
    (c : ℝ) (hc : 1 < c) :
    ∀ k C : ℕ, ∃ N0 : ℕ, ∀ n ≥ N0,
      (C : ℝ) * (n : ℝ) ^ k ≤ c ^ (n : ℝ) := by
  intro k C
  obtain ⟨N0, h⟩ := exp_dominates_poly c hc C k
  exact ⟨N0, h⟩

/-!
Strict exp-vs-poly wrapper: exponential eventually dominates any
polynomial with a strict gap. Trivial corollary of exp_dominates_poly.
-/
/-- Strict variant: trivial corollary of exp_dominates_poly.
For n ≥ 1, we have C*n^k + 1 ≤ (C+1)*n^k since n^k ≥ 1. -/
theorem exp_dominates_poly_strict
    (c : ℝ) (hc : 1 < c) (C k : ℕ) :
    ∃ N0 : ℕ, ∀ n ≥ N0,
      (C : ℝ) * (n : ℝ) ^ k + 1 ≤ c ^ (n : ℝ) := by
  obtain ⟨N0, h⟩ := exp_dominates_poly c hc (C + 1) k
  refine ⟨max 1 N0, fun n hn => ?_⟩
  have hn_geN0 : n ≥ N0 := le_trans (le_max_right 1 N0) hn
  have hn_ge1 : 1 ≤ n := le_trans (le_max_left 1 N0) hn
  -- For n ≥ 1: n^k ≥ 1 (proved by simple induction)
  have hnk_ge_1 : (1 : ℝ) ≤ (n : ℝ) ^ k := by
    have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge1
    clear h hn hn_geN0  -- simplify context
    induction k with
    | zero => simp
    | succ k' ih =>
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (n : ℝ) * 1 := by linarith
        _ ≤ (n : ℝ) * (n : ℝ) ^ k' := by
          apply mul_le_mul_of_nonneg_left ih
          linarith
        _ = (n : ℝ) ^ (k' + 1) := by ring
  calc (C : ℝ) * (n : ℝ) ^ k + 1
      ≤ (C : ℝ) * (n : ℝ) ^ k + (n : ℝ) ^ k := by linarith
    _ = ((C + 1 : ℕ) : ℝ) * (n : ℝ) ^ k := by norm_cast; ring
    _ ≤ c ^ (n : ℝ) := h n hn_geN0

/-! ## Asymptotic Threshold Helpers

These functions extract the explicit threshold N₀(C,k) from exp_dominates_poly_strict
and lift it to work with the baseline security parameter (128).

**Usage for P≠NP**: For any polynomial-time algorithm with bounds (C,k), we get
an explicit N₀ such that ∀n ≥ N₀, the exponential dominates that specific polynomial.
This gives the standard asymptotic formulation: "for sufficiently large n". -/

/-- **Extract the dominance threshold for specific polynomial bounds (C,k).**

From `exp_dominates_poly_strict`, we know ∃N₀ such that ∀n≥N₀: C·n^k + 1 ≤ 2^n.
This function extracts that N₀ for the specific (C,k) using Classical.choose. -/
noncomputable def N0_of (C k : Nat) : Nat :=
  Classical.choose (exp_dominates_poly_strict 2 (by norm_num : (1 : ℝ) < 2) C k)

/-- **Specification for N0_of: dominance holds for all n ≥ N0_of C k.** -/
lemma N0_of_spec (C k : Nat) :
    ∀ n ≥ N0_of C k, (C : ℝ) * (n : ℝ)^k + 1 ≤ 2^(n : ℝ) :=
  Classical.choose_spec (exp_dominates_poly_strict 2 (by norm_num : (1 : ℝ) < 2) C k)

/-- **Threshold lifted to baseline security parameter.**

For security proofs, we want n ≥ max(128, N0_of C k) to ensure:
- n ≥ 128 (baseline security parameter)
- n ≥ N0_of C k (exponential dominates this polynomial)

This is the threshold to use in "for sufficiently large n" statements. -/
noncomputable def N_of (C k : Nat) : Nat :=
  Nat.max 128 (N0_of C k)

/-- **N_of is at least the baseline security parameter.** -/
lemma N_of_ge_128 (C k : Nat) : 128 ≤ N_of C k :=
  Nat.le_max_left 128 (N0_of C k)

/-- **Dominance holds for all n ≥ N_of C k (real version).** -/
lemma dominates_from_N_of_real (C k n : Nat) (hn : N_of C k ≤ n) :
    (C : ℝ) * (n : ℝ)^k + 1 ≤ 2^(n : ℝ) := by
  have hN0 : N0_of C k ≤ n := (Nat.le_max_right 128 (N0_of C k)).trans hn
  exact N0_of_spec C k n hN0

/-- **Dominance holds for all n ≥ N_of C k (natural number version).**

This is the key lemma for security proofs: for n ≥ N_of C k, we have C·n^k < 2^n.
This eliminates the "finite case gap" by working only above the threshold. -/
lemma dominates_from_N_of (C k n : Nat) (hn : N_of C k ≤ n) :
    C * n^k < 2^n := by
  have h_real := dominates_from_N_of_real C k n hn
  -- Convert real inequality to naturals (same pattern as in security proofs)
  have h_2n : (2 : ℝ)^(n : ℝ) = ((2^n : Nat) : ℝ) := by
    simp [Real.rpow_natCast]
  have h_Cnk : (C : ℝ) * (n : ℝ)^k = ((C * n^k : Nat) : ℝ) := by
    push_cast; ring
  rw [h_2n, h_Cnk] at h_real
  -- From h_real: (C * n^k : ℝ) + 1 ≤ (2^n : ℝ)
  -- Therefore: C * n^k < 2^n
  have : ((C * n^k : Nat) : ℝ) < ((2^n : Nat) : ℝ) := by linarith
  exact Nat.cast_lt.mp this

/-! ## Averaging and Coin-Fixing Utilities

These lemmas support the standard coin-fixing argument in cryptography:
if a randomized adversary succeeds with some probability on average,
then there exists a fixed coin string achieving at least that success. -/

/-- Average of a real-valued function over a finite domain. -/
noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x : α, f x) / (Fintype.card α : ℝ)

/-- Pigeonhole principle for averaging.

Key lemma for coin-fixing in OWF security proofs.

**Statement**: If the average value is μ, at least one element achieves ≥ μ.
This is the standard pigeonhole/averaging principle.

**Proof**:
1. Assume by contradiction that all values < average
2. Sum strict inequalities: ∑ f x < ∑ avg f
3. Simplify RHS: ∑ avg f = (card α) × avg f
4. By definition: avg f = (∑ f x) / (card α)
5. Therefore: (card α) × avg f = ∑ f x
6. Contradiction: ∑ f x < ∑ f x is impossible -/
theorem exists_at_least_average {α : Type*} [Fintype α] (h_nonempty : 0 < Fintype.card α)
    (f : α → ℝ) : ∃ x : α, f x ≥ avg f := by
  by_contra h_not
  push_neg at h_not

  obtain ⟨witness⟩ := Fintype.card_pos_iff.mp h_nonempty

  have : ∑ x : α, f x < ∑ x : α, avg f :=
    Finset.sum_lt_sum (fun x _ => le_of_lt (h_not x)) ⟨witness, Finset.mem_univ _, h_not witness⟩

  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, avg] at this

  have h_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast h_nonempty

  field_simp [h_pos.ne'] at this
  linarith

/-- Coin-fixing variant: for finite domains represented as Fin T. -/
theorem exists_coin_at_least_average {T : Nat} (hT : 0 < T) (f : Fin T → ℝ) :
    ∃ c : Fin T, f c ≥ avg f := by
  have h_card : Fintype.card (Fin T) = T := Fintype.card_fin T
  have h_card_pos : 0 < Fintype.card (Fin T) := by rw [h_card]; exact hT
  exact exists_at_least_average h_card_pos f

end LStar.StructuralOWF.Foundations.Probability

/-! Helper theorems for coin-fixing and algorithmic contradictions.
Helper utilities for coin-fixing and algorithmic contradictions, available to downstream proofs. -/

namespace LStar.StructuralOWF.Foundations.Probability

/-- Simple positivity fact used as a utility in security scaffolding. -/
theorem inv_poly_nonneg (c : ℕ) : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n : ℝ) ^ c := by
  intro n
  have h₁ : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hpow : 0 ≤ (n : ℝ) ^ c := by exact pow_nonneg h₁ _
  have h_inv : 0 ≤ ((n : ℝ) ^ c)⁻¹ := inv_nonneg.mpr hpow
  have : 0 ≤ 1 / (n : ℝ) ^ c := by
    convert h_inv using 1
    · simp [one_div]
  exact this


/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

end LStar.StructuralOWF.Foundations.Probability
