import Layer5_Applications.PvsNP.PrimaryPath.OWFExistence

/-! # Uniform PPT Embedding (Option A - Refactored)

**Goal**: Mechanize the embedding from textbook uniform PPT adversaries to our
family-quantified SecurityProperty.

**The Problem**: Our `SecurityProperty` quantifies over families
`A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars`, but textbook OWF security
uses a single uniform PPT adversary (one TM for all n).

**Solution**: Define `UniformOWFAdversary Φ` as a family with uniformity proofs:
- Store `A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars` directly
- Require proof that TM and bounds (C, k) are constant across n
- Define `uniform_success_prob` using `avg_success_prob_n_exp` (the real experiment)

This makes `liftToFamily` trivial (just extract the family) and
`lift_success_prob_eq` definitional (both sides are the same by construction).

**Key Insight**: "Uniform" means the TM and bounds are constant; only the
type-level interpretation (decoding to `Randomness/Witness` for varying nvars) changes.

**Trust Boundary**: 0 new axioms (purely definitional embedding).
-/

namespace LStar.StructuralOWF.UniformEmbedding

open LStar
open LStar.Complexity
open LStar.StructuralOWF
open LStar.StructuralOWF.OWFExistence
open LStar.StructuralOWF.Theorems  -- for CNFFamily

/-! ## Part 1: Uniform Adversary Definition -/

/-- **Uniform PPT Adversary**: A family with constant TM and bounds.

    **Representation**: Store the family `A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars`
    directly, plus proofs that the underlying TM and polynomial bounds are constant across n.

    **Why HEq**: The TM type depends on parameters (stateCount/alphabetSize/tapeCount),
    so we use heterogeneous equality to express "same TM" across different n.

    **Textbook Correspondence**: This captures "single algorithm for all n" by requiring
    the TM to be literally the same; only the type-level interpretation varies.

    **HONESTY NOTE 1 - Uniformity by Structure**: This is "uniformity-by-structure"
    (a family plus proofs of same TM/bounds), NOT "a single TM taking 1^n as input"
    as a standalone type. It's equivalent in spirit, but we encode "single TM" as a
    property of a family rather than a primitive notion. Textbook uniform PPT
    adversaries satisfy this definition (same TM → uniform_M, same bounds → uniform_bounds).

    **HONESTY NOTE 2 - Strength of uniform_M**: The `HEq` constraint is very strong:
    it requires literally the same TM (same stateCount, alphabetSize, tapeCount, and
    transition function). If "same code but different state/alphabet encodings" were
    acceptable, one would weaken this to an equivalence/compilation relation. -/
structure UniformOWFAdversary (Φ : CNFFamily) where
  /-- The underlying adversary family. -/
  A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars
  /-- **Uniformity of TM**: Same Turing machine for all security parameters.
      Uses HEq because TM type depends on state/alphabet/tape counts. -/
  uniform_M : ∀ n m, HEq (A n).base.M (A m).base.M
  /-- **Uniformity of bounds**: Same polynomial constants (C, k) for all n. -/
  uniform_bounds : ∀ n m, (A n).base.C = (A m).base.C ∧ (A n).base.k = (A m).base.k

/-! ## Part 2: Success Probability (Real Experiment) -/

/-- **Uniform success probability**: Defined using the existing `avg_success_prob_n_exp`.

    This is NOT a placeholder - it's the real inversion experiment:
    - Sample random assignment r uniformly
    - Compute challenge y = plant_flat(Φ n, r)
    - Run adversary to get candidate preimage r'
    - Check if plant_flat(Φ n, r') = y
    - Average over coins

    By defining this in terms of `avg_success_prob_n_exp`, we ensure:
    1. The experiment is identical to what SecurityProperty uses
    2. `lift_success_prob_eq` becomes definitional -/
noncomputable def uniform_success_prob
    (Φ : CNFFamily) (prec : CNFPreconditions Φ)
    (U : UniformOWFAdversary Φ)
    (n : LStar.Base.SecurityParam 128) : ℝ :=
  avg_success_prob_n_exp 1 (by norm_num) rfl (Φ n.val)
    (Nat.le_trans (Nat.le_trans (by decide : 4 ≤ 128) n.property) (prec.wellformed n.val n.property))
    (prec.aligned n.val n.property)
    (U.A n.val).base

/-! ## Part 3: Textbook Security Definition -/

/-- **Textbook OWF Security**: For all uniform PPT adversaries,
    success probability is negligible.

    This is the standard textbook definition:
    "∀ uniform PPT A, Pr[A inverts f] ≤ negl(n)"

    Now using the REAL experiment (not a placeholder). -/
def TextbookOWFSecurity (Φ : CNFFamily) (prec : CNFPreconditions Φ) : Prop :=
  ∀ (U : UniformOWFAdversary Φ),
    negligible_parametric 128 (uniform_success_prob Φ prec U)

/-! ## Part 4: Trivial Lifting -/

/-- **Lift to family**: Trivially extract the underlying family.

    With our representation, "lifting" is just forgetting the uniformity proofs. -/
def liftToFamily (Φ : CNFFamily) (U : UniformOWFAdversary Φ) :
    (n : Nat) → StructuralOWFAdversary (Φ n).nvars :=
  U.A

/-- **Lifted family has constant bounds**: Follows directly from uniformity proof. -/
theorem lift_has_constant_bounds
    (Φ : CNFFamily) (U : UniformOWFAdversary Φ) :
    let A := liftToFamily Φ U
    ∀ n m, (A n).base.C = (A m).base.C ∧ (A n).base.k = (A m).base.k :=
  U.uniform_bounds

/-- **Success probabilities match**: Definitionally equal by construction.

    `uniform_success_prob` is defined using `avg_success_prob_n_exp` on `U.A`,
    and `liftToFamily` returns `U.A`, so this is `rfl`. -/
theorem lift_success_prob_eq
    (Φ : CNFFamily) (prec : CNFPreconditions Φ) (U : UniformOWFAdversary Φ)
    (n : LStar.Base.SecurityParam 128) :
    uniform_success_prob Φ prec U n =
      avg_success_prob_n_exp 1 (by norm_num) rfl (Φ n.val)
        (Nat.le_trans (Nat.le_trans (by decide : 4 ≤ 128) n.property) (prec.wellformed n.val n.property))
        (prec.aligned n.val n.property)
        (liftToFamily Φ U n.val).base :=
  rfl

/-! ## Part 5: Main Theorem -/

/-- **SecurityProperty implies TextbookOWFSecurity**.

    **Theorem**: Our family-quantified security implies textbook uniform PPT security.

    **Proof**:
    1. Given uniform adversary U, extract family A = U.A
    2. By U.uniform_bounds, A has constant bounds
    3. By constant_bounds_satisfy_constraint, A satisfies poly-bound constraint
    4. By h_sec (SecurityProperty), success for A is negligible
    5. By definition, uniform_success_prob uses the same experiment on A
    6. Therefore success for U is negligible

    The key simplification: steps 5-6 are now definitional (rfl). -/
theorem security_implies_textbook
    (Φ : CNFFamily)
    (prec : CNFPreconditions Φ)
    (h_sec : SecurityProperty Φ prec) :
    TextbookOWFSecurity Φ prec := by
  intro U
  -- Extract the family and its uniformity properties
  let A := liftToFamily Φ U
  have h_const := lift_has_constant_bounds Φ U

  -- Constant bounds satisfy the poly-bound constraint
  have h_poly : ∀ n, (A n).base.C ≤ (A 128).base.C ∧ (A n).base.k ≤ (A 128).base.k :=
    constant_bounds_satisfy_constraint Φ A h_const

  -- Apply SecurityProperty to get negligibility
  have h_negl := h_sec A h_poly

  -- The two success probabilities are definitionally equal
  -- uniform_success_prob is defined as avg_success_prob_n_exp on U.A = A
  exact h_negl

/-! ## Part 6: Combined Existence Theorem -/

/-- **OWF exists with textbook security**: There exists Φ with TextbookOWFSecurity.

    This is the final form matching standard cryptography textbooks:
    "There exists f such that ∀ uniform PPT A, Pr[A inverts f] ≤ negl(n)" -/
theorem OWF_exists_textbook :
    ∃ (Φ : CNFFamily) (prec : CNFPreconditions Φ), TextbookOWFSecurity Φ prec :=
  ⟨alignedCNFFamily, alignedCNFFamily_preconditions,
   security_implies_textbook alignedCNFFamily alignedCNFFamily_preconditions alignedCNFFamily_security⟩

/-! ## Axiom Audit -/

#print axioms UniformOWFAdversary
#print axioms uniform_success_prob
#print axioms TextbookOWFSecurity
#print axioms liftToFamily
#print axioms lift_has_constant_bounds
#print axioms lift_success_prob_eq
#print axioms security_implies_textbook
#print axioms OWF_exists_textbook

end LStar.StructuralOWF.UniformEmbedding
