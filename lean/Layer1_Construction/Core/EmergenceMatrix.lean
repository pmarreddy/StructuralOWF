import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Layer0_Foundations.Base.FiniteEncoding

/-! ## EmergenceMatrix: Certified Linear Independence Over GF(2) (A3 Foundation)

**Main Definition**: `EmergenceMatrix R n` - R×n matrix over ZMod 2 with certified full row rank.

**Mathematical Content**:
Emergence matrix E : GF(2)^n → GF(2)^R with rank certificate:
```lean
structure EmergenceMatrix (R n : Nat) where
  matrix : Matrix (Fin R) (Fin n) (ZMod 2)
  rank_eq : rowRank matrix = R  -- Rank certificate (constructive proof!)
```

**Emergence Computation**: For seed x ∈ {0,1}^n:
```
y = E · x  (matrix-vector mult over GF(2))
y_i = Σ_{j=0}^{n-1} E[i,j] · x[j]  (mod 2, for each row i)
```

**Full Rank Guarantee** (rowRank(E) = R):
R output bits are **maximal linearly independent** over GF(2):
- All 2^R output patterns achievable
- No output bit algebraically determined by others
- Result: R bits of genuine "degrees of freedom" (A3 emergence)

**Key Insight - A3 via Certified Rank**:
You CAN'T construct an EmergenceMatrix with rank < R—type checker demands proof!
Makes A3 **definitional** (enforced by types) rather than **axiomatic** (assumed property).

**Theorem: constructFullRank**:
Block identity matrix [I_R | 0_{R×(n-R)}] has full rank R:
```
For R=3, n=5:
⎡ 1 0 0 | 0 0 ⎤
⎢ 0 1 0 | 0 0 ⎥  rowRank = 3
⎣ 0 0 1 | 0 0 ⎦
```

**Proof**: Left block I_R is invertible → rank R (via right inverse technique + Mathlib).

**Why GF(2)?**: Achieves deterministic, provable independence without axioms:
- Linear independence = information-theoretic independence
- Rank proven via Mathlib (no custom axioms)
- Concrete construction: Block identity witness

**Trust Boundary**: All proofs use Mathlib linear algebra (no custom axioms).

**Paper**: §6 "A3 Emergence", §3.3 "Emergence Matrix Construction", Appendix A3 "Emergence via Rank".

See Layer1_Construction/Layer1_README.md for A3 property details and SCL integration.
-/

namespace LStar

open Matrix

abbrev EmergenceMat (R n : Nat) := Matrix (Fin R) (Fin n) (ZMod 2)

noncomputable def rowRank {R n} (M : EmergenceMat R n) : Nat :=
  Matrix.rank M

/-- An emergence matrix with certified full row rank `R`. -/
structure EmergenceMatrix (R n : Nat) where
  matrix : EmergenceMat R n
  rank_eq : rowRank matrix = R

namespace EmergenceMatrix

noncomputable section

open scoped Classical
open scoped BigOperators

/-- Apply an emergence matrix to a fixed-width seed, producing `R` Boolean
    emergent bits via multiplication over `ZMod 2` and mapping nonzero to `true`.
    Result encoded as Fin (2^R). -/
def apply {R n : Nat} (E : EmergenceMatrix R n) (x : LStar.Seed n) : LStar.Seed R :=
  -- Convert Seed (Fin) to bit function
  let xv : Fin n → (ZMod 2) := fun j => if (x.val >>> j.val) % 2 = 1 then 1 else 0
  let y : Fin R → (ZMod 2) := Matrix.mulVec E.matrix xv
  -- Pack result bits into Fin (2^R)
  let result_nat := (List.finRange R).foldr (fun i acc => acc * 2 + if y i ≠ 0 then 1 else 0) 0
  ⟨result_nat % (2^R), Nat.mod_lt result_nat (Nat.two_pow_pos R)⟩

-- Note: a convenient constructor for full-row-rank matrices (e.g. block identity)
-- can be provided in examples/tests without depending on fragile API lemmas.

end

end EmergenceMatrix

end LStar

/-!
## Explicit full-rank construction (block identity)

We provide a concrete `R×n` matrix over `ZMod 2` that contains the `R×R`
identity as the left block and zeros elsewhere. Over a field, such a
matrix has full row rank `R` whenever `R ≤ n`.

This section supplies the constructor `constructFullRank` that packages
this matrix with its rank certificate. The rank lemma can be proven by
exhibiting the non-vanishing `R×R` minor equal to `1` (the identity’s
determinant) and using `rank ≥ size_of_nonzero_minor` together with the
trivial `rank ≤ R` bound to conclude equality.
-/

namespace LStar

open Matrix

noncomputable section

open scoped Classical

/-- Left block identity `R×n` matrix: first `R` columns form `I_R`, rest zeros. -/
def leftIdentityBlock (R n : Nat) (_h : R ≤ n) : EmergenceMat R n :=
  fun i j => if hcol : (j.val < R) then (if (⟨j.val, hcol⟩ : Fin R) = i then (1 : ZMod 2) else 0) else 0

/-- Right-inverse of `leftIdentityBlock`: `n×R` matrix with `I_R` in first R rows, zeros elsewhere. -/
def rightInverseBlock (R n : Nat) (_h : R ≤ n) : Matrix (Fin n) (Fin R) (ZMod 2) :=
  fun i j => if hrow : (i.val < R) then (if (⟨i.val, hrow⟩ : Fin R) = j then (1 : ZMod 2) else 0) else 0

/-- The product `leftIdentityBlock · rightInverseBlock` equals the identity `I_R`. -/
theorem leftIdentityBlock_mul_rightInverse (R n : Nat) (h : R ≤ n) :
    leftIdentityBlock R n h * rightInverseBlock R n h = (1 : Matrix (Fin R) (Fin R) (ZMod 2)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.one_apply, leftIdentityBlock, rightInverseBlock]
  -- Goal: ∑ k, M[i,k] · N[k,j] = if i = j then 1 else 0
  -- Key insight: only k where i.val = k.val contributes (from M[i,k] structure)
  classical

  -- The sum has only one nonzero term: when k.val = i.val
  have hi_bound : i.val < R := i.isLt
  have hj_bound : j.val < R := j.isLt

  -- Construct the witness k: (Fin n) with k.val = i.val
  have hi_in_n : i.val < n := Nat.lt_of_lt_of_le hi_bound h
  let k_witness : Fin n := ⟨i.val, hi_in_n⟩

  -- Extract the single term from the sum
  have :
      ∑ k : Fin n,
          (if hcol : k.val < R then
              if (⟨k.val, hcol⟩ : Fin R) = i then (1 : ZMod 2) else 0
            else 0) *
            (if hrow : k.val < R then
              if (⟨k.val, hrow⟩ : Fin R) = j then (1 : ZMod 2) else 0
            else 0)
        =
        (if hcol : k_witness.val < R then
            if (⟨k_witness.val, hcol⟩ : Fin R) = i then (1 : ZMod 2) else 0
          else 0) *
          (if hrow : k_witness.val < R then
              if (⟨k_witness.val, hrow⟩ : Fin R) = j then (1 : ZMod 2) else 0
            else 0) := by
    refine Finset.sum_eq_single_of_mem k_witness ?hmem ?hzero
    · exact Finset.mem_univ _
    · intro k hk_mem hk_ne
      -- If k ≠ k_witness (i.e., k.val ≠ i.val), then M[i,k] = 0
      by_cases hk_lt : k.val < R
      · -- k.val < R, so we check if k = i
        have hk_ne_i : (⟨k.val, hk_lt⟩ : Fin R) ≠ i := by
          intro heq
          have : k.val = i.val := by simpa using congrArg Fin.val heq
          have : k = k_witness := Fin.ext this
          exact hk_ne this
        simp [hk_lt, hk_ne_i]
      · -- k.val ≥ R, so M[i,k] = 0
        simp [hk_lt]

  -- Simplify the extracted term
  rw [this]
  simp only [k_witness]
  -- Simplify Fin equality: ⟨i.val, _⟩ = i
  have hi_eq : (⟨i.val, hi_bound⟩ : Fin R) = i := Fin.ext rfl
  simp [hi_eq]

/-- Rank of the left block identity is `R` (field: `ZMod 2`). -/
theorem rank_leftIdentityBlock (R n : Nat) (h : R ≤ n) :
    rowRank (leftIdentityBlock R n h) = R := by
  -- Strategy: show rank M ≥ R and rank M ≤ R
  have h_upper : rowRank (leftIdentityBlock R n h) ≤ R := by
    -- R×n matrix has row rank ≤ number of rows
    simpa [rowRank, Fintype.card_fin] using
      (Matrix.rank_le_card_height (leftIdentityBlock R n h))

  have h_lower : R ≤ rowRank (leftIdentityBlock R n h) := by
    -- Use M·N = I_R and rank properties
    have h_mul :
        leftIdentityBlock R n h * rightInverseBlock R n h =
          (1 : Matrix (Fin R) (Fin R) (ZMod 2)) :=
      leftIdentityBlock_mul_rightInverse R n h

    -- rank(I_R) = R
    have h_rank_id : rowRank (1 : Matrix (Fin R) (Fin R) (ZMod 2)) = R := by
      simp [rowRank, Fintype.card_fin]

    -- rank(M·N) ≤ rank(M)
    have h_rank_mul_le : rowRank (leftIdentityBlock R n h * rightInverseBlock R n h) ≤
        rowRank (leftIdentityBlock R n h) := by
      simpa [rowRank] using
        (Matrix.rank_mul_le_left (leftIdentityBlock R n h) (rightInverseBlock R n h))

    -- Combine: R = rank(I_R) = rank(M·N) ≤ rank(M)
    calc R
      _ = rowRank (1 : Matrix (Fin R) (Fin R) (ZMod 2)) := h_rank_id.symm
      _ = rowRank (leftIdentityBlock R n h * rightInverseBlock R n h) := by rw [← h_mul]
      _ ≤ rowRank (leftIdentityBlock R n h) := h_rank_mul_le

  exact Nat.le_antisymm h_upper h_lower

/-- Construct a certified full-row-rank emergence matrix when `R ≤ n`. -/
def constructFullRank (R n : Nat) (h : R ≤ n) : EmergenceMatrix R n :=
  { matrix := leftIdentityBlock R n h
  , rank_eq := rank_leftIdentityBlock R n h }

/-- **SURJECTIVITY**: leftIdentityBlock is surjective as a linear map.

    For any target vector `t : Fin R → ZMod 2`, there exists an input
    vector `v : Fin n → ZMod 2` such that `(leftIdentityBlock R n h).mulVec v = t`.

    **Proof**: Construct v by padding t with zeros:
    - v[i] = t[i] for i < R
    - v[i] = 0 for i ≥ R
    Then leftIdentityBlock extracts the first R components, giving t. -/
theorem leftIdentityBlock_surjective (R n : Nat) (h : R ≤ n) :
    Function.Surjective (fun v : Fin n → ZMod 2 => (leftIdentityBlock R n h).mulVec v) := by
  intro t
  -- Construct the preimage: pad t with zeros
  let v : Fin n → ZMod 2 := fun i =>
    if hi : i.val < R then t ⟨i.val, hi⟩ else 0
  use v
  -- Prove (leftIdentityBlock R n h).mulVec v = t
  funext i
  simp only [Matrix.mulVec, leftIdentityBlock]
  -- Goal: (fun j => M[i,j]) ⬝ᵥ v = t[i], which is ∑ j, M[i,j] * v[j] = t[i]
  have hi_bound : i.val < R := i.isLt
  have hi_in_n : i.val < n := Nat.lt_of_lt_of_le hi_bound h

  -- The sum has only one nonzero term: when j.val = i.val
  -- Construct the witness j: (Fin n) with j.val = i.val
  let j_witness : Fin n := ⟨i.val, hi_in_n⟩

  -- Use the dotProduct definition: v ⬝ᵥ w = ∑ i, v i * w i
  show (fun j => if hcol : j.val < R then
                    if (⟨j.val, hcol⟩ : Fin R) = i then (1 : ZMod 2) else 0
                  else 0) ⬝ᵥ v = t i
  simp only [dotProduct]

  -- Extract the single term from the sum
  -- Define the function for clarity
  let f : Fin n → ZMod 2 := fun j =>
      (if hcol : j.val < R then
          if (⟨j.val, hcol⟩ : Fin R) = i then (1 : ZMod 2) else 0
        else 0) * v j
  have h_sum_eq : ∑ j : Fin n, f j = f j_witness := by
    refine Finset.sum_eq_single_of_mem j_witness (Finset.mem_univ _) ?hzero
    intro j _ hj_ne
    -- If j ≠ j_witness (i.e., j.val ≠ i.val), then M[i,j] = 0
    simp only [f]
    by_cases hj_lt : j.val < R
    · -- j.val < R, so we check if ⟨j.val, _⟩ = i
      have hj_ne_i : (⟨j.val, hj_lt⟩ : Fin R) ≠ i := by
        intro heq
        have hval : j.val = i.val := by simpa using congrArg Fin.val heq
        have : j = j_witness := Fin.ext hval
        exact hj_ne this
      simp [hj_lt, hj_ne_i]
    · -- j.val ≥ R, so M[i,j] = 0
      simp [hj_lt]
  simp only [f] at h_sum_eq

  rw [h_sum_eq]
  -- Now show v[j_witness] = t[i]
  simp only [v, j_witness]
  simp [hi_bound]

-- Axiom audit for key theorems (should list no custom axioms)
#print axioms LStar.rank_leftIdentityBlock
#print axioms LStar.constructFullRank
#print axioms LStar.leftIdentityBlock_surjective

end

end LStar
