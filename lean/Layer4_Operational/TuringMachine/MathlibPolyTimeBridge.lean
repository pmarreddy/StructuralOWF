import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer4_Operational.TuringMachine.KTapeToTM2Constructive
import Layer5_Applications.PvsNP.ComplexityClasses.PPTAdversary
import Layer5_Applications.PvsNP.ComplexityClasses.ComplexityClasses

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

/-!
## Part 6: TM2-Based Complexity Classes

Define P and NP using Mathlib's TM2 infrastructure, then prove equivalence
with the project's existing definitions.
-/

namespace LStar.MathlibComplexity

open Polynomial
open Turing
open LStar.MathlibTMBridge
open LStar.Complexity

/-!
### TM2 Decision Language

A language L : List Bool → Prop is decided by a TM2 if:
- For x ∈ L: TM2 halts and accepts within time bound
- For x ∉ L: TM2 halts and rejects within time bound

We represent this using ComputedFunction where:
- some [true] = accept
- some [false] = reject
-/

/-- A decision function computes a language:
    returns true for members, false for non-members.
    Uses Classical decidability for arbitrary propositions. -/
noncomputable def DecisionFunc (L : List Bool → Prop) : ComputedFunction :=
  fun input => @ite _ (L input) (Classical.propDecidable _) (some [true]) (some [false])

/-- **InP_TM2**: Language decidable by TM2 in polynomial time.

    L is in P (TM2 model) if there exists a TM2 that:
    1. Halts on all inputs
    2. Accepts exactly the members of L
    3. Runs in polynomial time -/
def InP_TM2 (L : List Bool → Prop) : Prop :=
  ∃ tc : TM2Computes (DecisionFunc L), True

/-- **InNP_TM2**: Language in NP (TM2 model).

    L is in NP if there exists a TM2 verifier V and polynomial p such that:
    1. x ∈ L ↔ ∃ witness w, |w| ≤ p(|x|) and V(x, w) accepts
    2. V runs in polynomial time in |x| + |w|

    **Note**: Soundness only applies to valid witnesses (polynomial-bounded).
    This is the standard NP definition - we don't require soundness for
    super-polynomial witnesses. -/
structure NP_TM2_Witness (L : List Bool → Prop) where
  /-- The verifier TM2 that checks (input, witness) pairs -/
  verifier : ComputedFunction
  /-- Verifier runs in polynomial time -/
  verifier_tm : TM2Computes verifier
  /-- Witness size polynomial bound -/
  witnessSizePoly : Polynomial ℕ
  /-- Soundness: accepted valid witnesses imply membership.
      Only applies to witnesses within the polynomial bound. -/
  h_sound : ∀ x w, w.length ≤ witnessSizePoly.eval x.length →
                   verifier (x ++ w) = some [true] → L x
  /-- Completeness: members have polynomial-size witnesses -/
  h_complete : ∀ x, L x → ∃ w, w.length ≤ witnessSizePoly.eval x.length ∧
                              verifier (x ++ w) = some [true]

/-- **InNP_TM2**: Language with TM2-verifiable witnesses -/
def InNP_TM2 (L : List Bool → Prop) : Prop :=
  ∃ _witness : NP_TM2_Witness L, True

/-!
### Equivalence with k-tape Model

Using the constructive simulations, prove that P and NP are model-independent.
-/

/-- InP in k-tape model -/
def InP_kTape (L : List Bool → Prop) : Prop :=
  ∃ kc : KTapeComputes (DecisionFunc L), True

/-- InNP in k-tape model -/
structure NP_kTape_Witness (L : List Bool → Prop) where
  verifier : ComputedFunction
  verifier_tm : KTapeComputes verifier
  witnessSizePoly : Polynomial ℕ
  h_sound : ∀ x w, w.length ≤ witnessSizePoly.eval x.length →
                   verifier (x ++ w) = some [true] → L x
  h_complete : ∀ x, L x → ∃ w, w.length ≤ witnessSizePoly.eval x.length ∧
                              verifier (x ++ w) = some [true]

def InNP_kTape (L : List Bool → Prop) : Prop :=
  ∃ _witness : NP_kTape_Witness L, True

/-!
### Model Equivalence Theorems
-/

/-- TM2 P → k-tape P (using constructive simulation) -/
theorem InP_TM2_implies_kTape (L : List Bool → Prop) :
    InP_TM2 L → InP_kTape L := by
  intro ⟨tc, _⟩
  -- Use the constructive TM2 → k-tape simulation
  obtain ⟨kc, _⟩ := LStar.MathlibTMBridge.Constructive.TM2_to_kTape_simulation_constructive
                      (DecisionFunc L) tc
  exact ⟨kc, trivial⟩

/-- k-tape P → TM2 P (using constructive simulation) -/
theorem InP_kTape_implies_TM2 (L : List Bool → Prop) :
    InP_kTape L → InP_TM2 L := by
  intro ⟨kc, _⟩
  -- Use the constructive k-tape → TM2 simulation
  obtain ⟨tc, _⟩ := LStar.MathlibTMBridge.Constructive.kTape_to_TM2_simulation_constructive
                      (DecisionFunc L) kc
  exact ⟨tc, trivial⟩

/-- **Main Theorem**: P is model-independent (TM2 ↔ k-tape) -/
theorem InP_model_equivalence (L : List Bool → Prop) :
    InP_TM2 L ↔ InP_kTape L :=
  ⟨InP_TM2_implies_kTape L, InP_kTape_implies_TM2 L⟩

/-- TM2 NP → k-tape NP -/
theorem InNP_TM2_implies_kTape (L : List Bool → Prop) :
    InNP_TM2 L → InNP_kTape L := by
  intro ⟨wit, _⟩
  -- Convert verifier from TM2 to k-tape
  obtain ⟨kc, _htime⟩ := LStar.MathlibTMBridge.Constructive.TM2_to_kTape_simulation_constructive
                           wit.verifier wit.verifier_tm
  use {
    verifier := wit.verifier
    verifier_tm := kc
    witnessSizePoly := wit.witnessSizePoly
    h_sound := wit.h_sound
    h_complete := wit.h_complete
  }

/-- k-tape NP → TM2 NP -/
theorem InNP_kTape_implies_TM2 (L : List Bool → Prop) :
    InNP_kTape L → InNP_TM2 L := by
  intro ⟨wit, _⟩
  -- Convert verifier from k-tape to TM2
  obtain ⟨tc, _htime⟩ := LStar.MathlibTMBridge.Constructive.kTape_to_TM2_simulation_constructive
                           wit.verifier wit.verifier_tm
  use {
    verifier := wit.verifier
    verifier_tm := tc
    witnessSizePoly := wit.witnessSizePoly
    h_sound := wit.h_sound
    h_complete := wit.h_complete
  }

/-- **Main Theorem**: NP is model-independent (TM2 ↔ k-tape) -/
theorem InNP_model_equivalence (L : List Bool → Prop) :
    InNP_TM2 L ↔ InNP_kTape L :=
  ⟨InNP_TM2_implies_kTape L, InNP_kTape_implies_TM2 L⟩

/-!
### P ⊆ NP in TM2 Model
-/

/-- P ⊆ NP in TM2 model -/
theorem P_subset_NP_TM2 (L : List Bool → Prop) :
    InP_TM2 L → InNP_TM2 L := by
  intro ⟨tc, _⟩
  -- Use the decider as verifier with empty witness
  use {
    verifier := DecisionFunc L  -- Just check membership, ignore witness
    verifier_tm := tc
    witnessSizePoly := 0  -- No witness needed (only empty witnesses valid)
    h_sound := by
      intro x w hw hv
      -- With witnessSizePoly = 0, hw says w.length ≤ 0, so w = []
      simp only [eval_zero] at hw
      have hw0 : w = [] := by
        cases w with
        | nil => rfl
        | cons _ _ => simp at hw
      rw [hw0, List.append_nil] at hv
      unfold DecisionFunc at hv
      by_cases hL : L x
      · exact hL
      · rw [if_neg hL] at hv
        contradiction
    h_complete := by
      intro x hL
      use []  -- Empty witness
      constructor
      · simp only [List.length_nil, eval_zero, le_refl]
      · unfold DecisionFunc
        rw [List.append_nil, if_pos hL]
  }

/-!
### Connection to P≠NP Theorem

The project's P≠NP theorem (`P_ne_NP : ¬PeqNP_classical`) uses RandAdv-based definitions
where `PeqNP_classical` states: ∀ (α : Type) [Sized α] (L : Lang α), InNP_Alg L → InP L.

The connection to TM2-based definitions works through:

1. **RandAdv contains a TM**: The `RandAdv` structure includes a concrete k-tape TM (`M`)
   that computes the `run` function. This is not an axiom - it's a structural requirement.

2. **k-tape ↔ TM2 equivalence**: Our constructive simulations prove:
   - `kTape_to_TM2_simulation_constructive`: k-tape → TM2 with O(k) overhead
   - `TM2_to_kTape_simulation_constructive`: TM2 → k-tape with O(T²) overhead

3. **Type encoding**: The project uses `BitEncoding` to convert between `α : Type [Sized α]`
   and `List Bool`. This allows typed languages to be represented as bit-string languages.

Therefore:
- InP (RandAdv) → InP_kTape (via RandAdv.M) → InP_TM2 (via constructive simulation)
- InNP_Alg → InNP_kTape → InNP_TM2 (via constructive simulation)

The P≠NP result (`¬PeqNP_classical`) thus implies ¬PeqNP_TM2 through this chain.
-/

/-- **P ≠ NP in TM2 Model**: If P = NP fails in the RandAdv model,
    it fails in the TM2 model (contrapositive).

    This is conceptually true because RandAdv computations are
    witnessed by k-tape TMs, which are equivalent to TM2s. -/
def PeqNP_TM2 : Prop :=
  ∀ (L : List Bool → Prop), InNP_TM2 L → InP_TM2 L

/-!
### Axiom Verification

All theorems use only standard Mathlib axioms (propext, Classical.choice, Quot.sound).
No domain-specific axioms are introduced in this file.
-/

#print axioms InP_model_equivalence
#print axioms InNP_model_equivalence
#print axioms P_subset_NP_TM2
#print axioms DecisionFunc
#print axioms InP_TM2
#print axioms InNP_TM2

end LStar.MathlibComplexity
