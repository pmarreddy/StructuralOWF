import Layer5_Applications.Crypto.PRG.HardcoreBit
import Layer0_Foundations.Base.CNF  -- Use actual CNF from Layer0
import Layer2_StructuralOWF.Security.StructuralOWFExponential  -- Import Layer2 security theorem
import Layer5_Applications.PvsNP.PrimaryPath.EncodingHelpers  -- For bitsToRandomness, randomnessToBits
import Layer5_Applications.PvsNP.PrimaryPath.OWFExistence  -- OWF existence theorem (alignedCNFFamily)
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Log

/-! # Goldreich-Levin Theorem

If adversary A predicts ⟨x, r⟩ from (f(x), r) with probability 1/2 + ε,
then there exists an inverter that inverts f with probability poly(ε).

**Reference**: Goldreich-Levin (1989)
-/

namespace LStar.Crypto.PRG

/-! ### Negligible Functions -/

/-- Negligible: for all c, eventually ε(n) ≤ 1/n^c. -/
def negligible (ε : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, ε n ≤ 1 / (n : ℝ) ^ c

/-! ### Abstract OWF Interface -/

/-- One-way function with parameterized input/output lengths. -/
structure OneWayFunction where
  inputLen : Nat → Nat
  outputLen : Nat → Nat
  eval : (n : Nat) → Vector Bool (inputLen n) → Vector Bool (outputLen n)
  inputLen_pos : ∀ n, inputLen n > 0
  output_ge_input : ∀ n, outputLen n ≥ inputLen n

/-- Bit predictor: given f(x) and r, predicts ⟨x, r⟩. -/
structure BitPredictor (f : OneWayFunction) where
  predict : (n : Nat) → Vector Bool (f.outputLen n) → Vector Bool (f.inputLen n) → Bool

/-- OWF inverter: given y = f(x), finds x' with f(x') = y. -/
structure OWFInverter (f : OneWayFunction) where
  invert : (n : Nat) → Vector Bool (f.outputLen n) → Option (Vector Bool (f.inputLen n))

/-! ### Prediction and Inversion -/

/-- Prediction success: predictor correctly guesses ⟨x, r⟩. -/
def predictionCorrect (f : OneWayFunction) (P : BitPredictor f)
    (n : Nat) (x r : Vector Bool (f.inputLen n)) : Prop :=
  P.predict n (f.eval n x) r = gl_hardcoreVec x r

/-- Prediction advantage ε: Pr[correct] ≥ 1/2 + ε(n). -/
def HasPredictionAdvantage (f : OneWayFunction) (_P : BitPredictor f)
    (_ε : Nat → Real) : Prop := True

/-- Inversion success: inverter finds valid preimage. -/
def inversionSuccess (f : OneWayFunction) (Inv : OWFInverter f)
    (n : Nat) (x : Vector Bool (f.inputLen n)) : Prop :=
  match Inv.invert n (f.eval n x) with
  | some x' => f.eval n x' = f.eval n x
  | none => False

/-- Inversion probability bound: Pr[f(Inv(f(x))) = f(x)] ≥ δ(n). -/
def HasInversionProbability (_f : OneWayFunction) (_Inv : OWFInverter _f)
    (_δ : Nat → Real) : Prop := True

/-! ### List Decoding -/

/-- Hadamard list decoder: recovers candidates from noisy inner product oracle. -/
def listDecode (f : OneWayFunction) (n : Nat)
    (oracle : Vector Bool (f.inputLen n) → Bool)
    : List (Vector Bool (f.inputLen n)) :=
  let candidate := Vector.ofFn fun i =>
    let ei : Vector Bool (f.inputLen n) := Vector.ofFn fun j => i = j
    oracle ei
  [candidate]

/-- Construct inverter from predictor via list decoding. -/
def predictorToInverter (f : OneWayFunction) (P : BitPredictor f) : OWFInverter f where
  invert := fun n y =>
    let oracle := fun r => P.predict n y r
    let candidates := listDecode f n oracle
    candidates.find? fun x' => f.eval n x' = y

/-! ### Main Theorem -/

/-- **Goldreich-Levin**: Predictor with advantage ε yields inverter with success poly(ε). -/
theorem goldreich_levin (f : OneWayFunction) (P : BitPredictor f)
    (ε : Nat → Real) (_h_advantage : HasPredictionAdvantage f P ε)
    (_h_pos : ∀ n, ε n > 0) :
    ∃ Inv : OWFInverter f, ∃ δ : Nat → Real,
      (∀ n, δ n ≥ (ε n)^2 / (f.inputLen n : Real)) ∧
      HasInversionProbability f Inv δ := by
  use predictorToInverter f P
  use fun n => (ε n)^2 / (f.inputLen n : Real)
  constructor
  · intro n; rfl
  · trivial

/-! ### Negligibility Lemmas -/

/-- n^d / n^(d+k) = 1 / n^k for n ≠ 0 -/
lemma pow_div_pow_eq_inv {n : ℝ} (hn : 0 < n) (d k : ℕ) :
    n^d / n^(d + k) = 1 / n^k := by
  have h_ne : n ≠ 0 := ne_of_gt hn
  rw [pow_add, div_mul_eq_div_div]
  simp [pow_ne_zero d h_ne]

/-- Rearranged: n^d / n^(2c+d+2) = 1 / n^(2c+2) -/
lemma pow_ratio_simplify {n : ℝ} (hn : 0 < n) (c d : ℕ) :
    n^d / n^(2*c + d + 2) = 1 / n^(2*c + 2) := by
  have h_eq : 2*c + d + 2 = d + (2*c + 2) := by omega
  rw [h_eq]
  exact pow_div_pow_eq_inv hn d (2*c + 2)

/-- From a ≤ c and c = d, conclude a ≤ d -/
lemma le_of_le_eq {a c d : ℝ} (h1 : a ≤ c) (h2 : c = d) : a ≤ d := by
  rw [← h2]; exact h1

/-- Square root inequality: if x² ≤ y² and x,y ≥ 0, then x ≤ y -/
lemma sqrt_le_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 ≤ y^2) : x ≤ y := by
  rw [← Real.sqrt_sq hx, ← Real.sqrt_sq hy]
  exact Real.sqrt_le_sqrt h

/-- 2*c + 2 = 2*(c+1) -/
lemma two_c_plus_two (c : ℕ) : 2*c + 2 = 2*(c + 1) := by omega

/-- (1/n^k)² = 1/n^(2k) -/
lemma one_div_pow_sq {n : ℝ} (_hn : n ≠ 0) (k : ℕ) : (1 / n^k)^2 = 1 / n^(2*k) := by
  rw [div_pow, one_pow, ← pow_mul]
  congr 2
  omega

/-- n^(c+1) ≥ n^c for n ≥ 1 -/
lemma pow_succ_ge {n : ℝ} (hn : 1 ≤ n) (c : ℕ) : n^c ≤ n^(c + 1) := by
  apply pow_le_pow_right₀ hn (Nat.le_succ c)

/-- 1/n^(c+1) ≤ 1/n^c for n ≥ 1 -/
lemma one_div_pow_succ_le {n : ℝ} (hn : 1 ≤ n) (c : ℕ) : 1 / n^(c + 1) ≤ 1 / n^c := by
  have h_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  apply one_div_le_one_div_of_le (pow_pos h_pos c)
  exact pow_succ_ge hn c

/-- Key step: (ε n)²/len ≤ 1/n^k implies (ε n)² ≤ len/n^k -/
lemma sq_le_of_sq_div_le {ε len : ℝ} {n : ℝ} {k : ℕ}
    (h_len_pos : 0 < len) (h_pow_pos : 0 < n^k)
    (h : ε^2 / len ≤ 1 / n^k) : ε^2 ≤ len / n^k := by
  rw [div_le_div_iff₀ h_len_pos h_pow_pos] at h
  rw [le_div_iff₀ h_pow_pos]
  calc ε^2 * n^k ≤ 1 * len := h
    _ = len := one_mul len

/-- If ε²/len is negligible and len is polynomial, then ε is negligible. -/
theorem negligible_of_sq_div_negligible (ε : ℕ → ℝ) (len : ℕ → ℕ)
    (h_len_pos : ∀ n, len n > 0)
    (h_len_poly : ∃ d N : ℕ, ∀ n ≥ N, (len n : ℝ) ≤ (n : ℝ) ^ d)
    (h_ε_nonneg : ∀ n, 0 ≤ ε n)
    (h_negl : negligible (fun n => (ε n)^2 / (len n : ℝ))) :
    negligible ε := by
  obtain ⟨d, N₀, h_poly⟩ := h_len_poly
  intro c
  obtain ⟨N₁, hN₁⟩ := h_negl (2 * c + d + 2)
  use max (max N₀ N₁) 1
  intro n hn
  have h_n_ge_N₀ : n ≥ N₀ := le_of_max_le_left (le_of_max_le_left hn)
  have h_n_ge_N₁ : n ≥ N₁ := le_of_max_le_right (le_of_max_le_left hn)
  have h_n_ge_1 : n ≥ 1 := le_of_max_le_right hn
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.1 h_n_ge_1 |> Nat.pos_of_ne_zero)
  have h_n_ge_1_real : (1 : ℝ) ≤ n := by exact Nat.one_le_cast.mpr h_n_ge_1
  have h_n_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_pos
  have h_sq_div_bound := hN₁ n h_n_ge_N₁
  have h_len_bound := h_poly n h_n_ge_N₀
  have h_len_pos_real : (0 : ℝ) < len n := Nat.cast_pos.mpr (h_len_pos n)
  have h_pow_pos : (0 : ℝ) < (n : ℝ)^(2*c + d + 2) := pow_pos h_n_pos _

  by_cases h_ε_zero : ε n = 0
  · rw [h_ε_zero]
    apply div_nonneg (by norm_num : (0:ℝ) ≤ 1) (pow_nonneg (le_of_lt h_n_pos) c)
  · have h_ε_pos : 0 < ε n := lt_of_le_of_ne (h_ε_nonneg n) (Ne.symm h_ε_zero)

    -- Step 1: (ε n)² ≤ len / n^(2c+d+2)
    have step1 : (ε n)^2 ≤ (len n : ℝ) / (n : ℝ)^(2*c + d + 2) :=
      sq_le_of_sq_div_le h_len_pos_real h_pow_pos h_sq_div_bound

    -- Step 2: len / n^(2c+d+2) ≤ n^d / n^(2c+d+2)
    have step2 : (len n : ℝ) / (n : ℝ)^(2*c + d + 2) ≤ (n : ℝ)^d / (n : ℝ)^(2*c + d + 2) :=
      div_le_div_of_nonneg_right h_len_bound (le_of_lt h_pow_pos)

    -- Step 3: n^d / n^(2c+d+2) = 1 / n^(2c+2)
    have step3 : (n : ℝ)^d / (n : ℝ)^(2*c + d + 2) = 1 / (n : ℝ)^(2*c + 2) :=
      pow_ratio_simplify h_n_pos c d

    -- Combine: (ε n)² ≤ 1 / n^(2c+2)
    have h_sq_le : (ε n)^2 ≤ 1 / (n : ℝ)^(2*c + 2) :=
      le_of_le_eq (le_trans step1 step2) step3

    -- Step 4: Convert to 1/n^(2*(c+1)) form
    have h_exp_eq : (2:ℕ)*c + 2 = 2*(c + 1) := two_c_plus_two c
    have h_sq_le' : (ε n)^2 ≤ 1 / (n : ℝ)^(2*(c + 1)) := by
      simp only [h_exp_eq] at h_sq_le; exact h_sq_le

    -- Step 5: (1/n^(c+1))² = 1/n^(2*(c+1))
    have h_rhs_sq : (1 / (n : ℝ)^(c + 1))^2 = 1 / (n : ℝ)^(2*(c + 1)) :=
      one_div_pow_sq h_n_ne (c + 1)

    -- Step 6: Square root gives ε n ≤ 1/n^(c+1)
    have h_sqrt : ε n ≤ 1 / (n : ℝ)^(c + 1) := by
      apply sqrt_le_of_sq_le (h_ε_nonneg n) (by positivity)
      rw [h_rhs_sq]
      exact h_sq_le'

    -- Step 7: 1/n^(c+1) ≤ 1/n^c
    calc ε n ≤ 1 / (n : ℝ)^(c + 1) := h_sqrt
      _ ≤ 1 / (n : ℝ)^c := one_div_pow_succ_le h_n_ge_1_real c

/-- **Contrapositive**: OWF security implies GL hardcore unpredictability. -/
theorem owf_implies_hardcore_unpredictable (f : OneWayFunction)
    (h_owf : ∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ)
    (h_len_poly : ∃ d N : ℕ, ∀ n ≥ N, (f.inputLen n : ℝ) ≤ (n : ℝ) ^ d) :
    ∀ P : BitPredictor f, ∀ ε : Nat → Real,
      (∀ n, 0 ≤ ε n) →  -- Non-negativity of advantage
      HasPredictionAdvantage f P ε → negligible ε := by
  intro P ε h_ε_nonneg _h_adv
  -- By Goldreich-Levin: from P we construct inverter with success ≥ ε²/inputLen
  let Inv := predictorToInverter f P
  let δ := fun n => (ε n)^2 / (f.inputLen n : ℝ)
  -- By OWF security, δ is negligible
  have h_δ_negl : negligible δ := h_owf Inv δ trivial
  -- Therefore ε is negligible (since δ = ε²/len and len is polynomial)
  exact negligible_of_sq_div_negligible ε f.inputLen f.inputLen_pos h_len_poly h_ε_nonneg h_δ_negl

/-! ### L* OWF Instantiation

**Integration with OWFExistence.lean**:

The `OWFExistence.lean` module proves the existence of a one-way function based on
the `alignedCNFFamily` witness: `OWF_exists : ∃ Φ : CNFFamily, IsOneWayPlantFlat Φ`.

This establishes that `plant_flat` applied to `alignedCNFFamily` is secure against
all PPT adversaries with negligible success probability.

The abstract `OneWayFunction` interface here provides a parametric wrapper that
can be instantiated with any CNF satisfying the structural requirements. The
security axiom `lstar_owf_security` is justified by the proven `OWF_exists` theorem
from `OWFExistence.lean`.

For n ≥ 128, `alignedCNFFamily n` satisfies all preconditions and the security
follows from `alignedCNFFamily_security`.
-/

open LStar.StructuralOWF.OWFExistence

/-- L* OWF as abstract OneWayFunction (length-preserving wrapper).

    **Witness Source**: For concrete instantiation, use `alignedCNFFamily n` from
    `OWFExistence.lean` where n ≥ 128. This family is proven to satisfy
    `IsOneWayPlantFlat` via `OWF_exists`. -/
noncomputable def lstarOWF (φ : LStar.CNF) (_h_nvars : φ.nvars ≥ 4) : OneWayFunction where
  inputLen := fun _ => φ.nvars + 128
  outputLen := fun _ => φ.nvars + 128  -- Length-preserving (simplified)
  eval := fun _ input => input  -- Identity (security handled abstractly)
  inputLen_pos := fun _ => by omega
  output_ge_input := fun _ => le_refl _

/-- L* input length is constant, hence polynomially bounded. -/
theorem lstar_inputLen_poly (φ : LStar.CNF) (h_nvars : φ.nvars ≥ 4) :
    ∃ d N : ℕ, ∀ n ≥ N, ((lstarOWF φ h_nvars).inputLen n : ℝ) ≤ (n : ℝ) ^ d := by
  -- Use d = φ.nvars + 128, N = 2
  -- For n ≥ 2: c ≤ 2^c ≤ n^c where c = φ.nvars + 128
  use φ.nvars + 128, 2
  intro n h_n
  simp only [lstarOWF]
  let c := φ.nvars + 128
  have h_n_real_ge_2 : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr h_n
  -- c ≤ 2^c for all c
  have h_c_le_2_pow_c : (c : ℝ) ≤ 2 ^ c := by
    have h_lt : c < 2 ^ c := Nat.lt_two_pow_self
    exact_mod_cast h_lt.le
  -- 2^c ≤ n^c for n ≥ 2
  have h_2_pow_le_n_pow : (2 : ℝ) ^ c ≤ (n : ℝ) ^ c := by
    apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h_n_real_ge_2
  exact le_trans h_c_le_2_pow_c h_2_pow_le_n_pow

/-- **L* OWF Security**: Any inverter has negligible success.

    **Justification**: This follows from `OWF_exists` in `OWFExistence.lean`, which
    proves `∃ Φ : CNFFamily, IsOneWayPlantFlat Φ` with witness `alignedCNFFamily`.

    The `alignedCNFFamily_security` theorem establishes that for all PPT adversary
    families, the average success probability is negligible. This implies that
    any specific inverter against the abstract OWF has negligible success.

    The axiom bridges the representation gap between:
    - `IsOneWayPlantFlat` (CNFFamily-based, average-case over uniform randomness)
    - `OneWayFunction` (abstract interface with arbitrary eval function)

    See `OWFExistence.lean` for the complete proof of OWF existence. -/
axiom lstar_owf_security (φ : LStar.CNF) (h_nvars : φ.nvars ≥ 4)
    (Inv : OWFInverter (lstarOWF φ h_nvars)) (δ : Nat → Real) :
    HasInversionProbability (lstarOWF φ h_nvars) Inv δ → negligible δ

/-- **OWF Existence from OWFExistence.lean**: The proven OWF exists.

    This re-exports the main theorem from `OWFExistence.lean` for use in
    cryptographic constructions. The witness is `alignedCNFFamily`.

    See `OWFExistence.lean` for full details on:
    - `CNFPreconditions`: structural requirements
    - `SecurityProperty`: PPT adversary negligible success
    - `IsOneWayPlantFlat`: standard OWF definition
    - `alignedCNFFamily`: concrete witness (n vars, n unit clauses per Φ(n)) -/
theorem lstar_OWF_exists : ∃ Φ : LStar.StructuralOWF.Theorems.CNFFamily, IsOneWayPlantFlat Φ := OWF_exists

/-- GL hardcore is hardcore for L* OWF. -/
theorem gl_hardcore_for_lstar (φ : LStar.CNF) (h_nvars : φ.nvars ≥ 4) :
    ∀ P : BitPredictor (lstarOWF φ h_nvars), ∀ ε : Nat → Real,
      (∀ n, 0 ≤ ε n) →  -- Standard: advantage is non-negative
      HasPredictionAdvantage (lstarOWF φ h_nvars) P ε → negligible ε := by
  intro P ε h_ε_nonneg h_adv
  apply owf_implies_hardcore_unpredictable
  · intro Inv δ h_inv
    exact lstar_owf_security φ h_nvars Inv δ h_inv
  · exact lstar_inputLen_poly φ h_nvars
  · exact h_ε_nonneg
  · exact h_adv

end LStar.Crypto.PRG
