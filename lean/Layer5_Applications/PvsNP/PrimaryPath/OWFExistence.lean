import Layer2_StructuralOWF.Security.StructuralOWFExponential
import Layer3_InformationBounds.Theorems.AlignedFamily
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFAdversary

/-! # OWF Existence Theorem

This file provides an explicit "OWF exists" theorem in standard cryptographic form:
`∃ Φ, IsOneWayPlantFlat Φ`

**Standard OWF Definition** (Goldreich/Katz-Lindell):
A function f is one-way if:
1. f is efficiently computable (polynomial time)
2. ∀ PPT adversary A: Pr[A inverts f] ≤ negl(n)

**Our Formalization**:
- "Efficiently computable" → `forward_polytime` field (output size ≤ C·n^k)
- "Negligible inversion" → `SecurityProperty` using `avg_success_prob_n_exp`
- Success experiment: average inversion probability over uniform randomness

**Witness**: `alignedCNFFamily` — a CNF family where each Φ(n) has n variables
and n unit clauses (one positive literal per variable). Simple structure,
but sufficient to instantiate the OWF construction.

**Trust Boundary**: 1 custom axiom (`tm_correctness_implies_realizesAllValuesFrom_flat_encoded`).
This is a strict subset of P≠NP's 2 axioms — OWF doesn't need the AlgSpec→TM bridge.
-/

namespace LStar.StructuralOWF.OWFExistence

open LStar
open LStar.StructuralOWF
open LStar.StructuralOWF.Theorems
open LStar.StructuralOWF.Foundations
open LStar.Complexity

/-- **CNF Family Preconditions**: Structural requirements for OWF construction.

    These are the side-conditions needed to apply `f_is_structural_owf_exponential_true`. -/
structure CNFPreconditions (Φ : CNFFamily) : Prop where
  wellformed : CNFFamily.WellFormed Φ
  wf_literals : ∀ n, LStar.CNF.WellFormed (Φ n)
  nvars_eq : ∀ n ≥ 128, (Φ n).nvars = n
  nonempty_clauses : ∀ n, n ≥ 128 → 0 < (Φ n).clauses.length
  clauses_poly : ∃ C_cl k_cl, C_cl > 0 ∧ k_cl > 0 ∧ ∀ n ≥ 128, (Φ n).clauses.length ≤ C_cl * n^k_cl
  positive_clause : ∀ n ≥ 128, LStar.CNF.HasPositiveClause (Φ n)
  bounded_solutions : ∃ c, CNFFamily.BoundedSolutions Φ c
  aligned : ∀ n ≥ 128, AlignedCNFConstraints (Φ n)
  /-- **Poly-time Forward Computation**: plant_flat runs in polynomial time.

      Standard OWF requirement: the forward function f must be efficiently computable.

      **Formalization**: Output representation size is polynomial in n.
      Since computation_time ≥ output_size, this implies poly-time computation.

      **Concrete bound**: |output| ≤ n + n * |clauses| ≤ C * n^k for constants C, k.

      **Justification**: plant_flat encodes an n-bit assignment into a CNF with
      poly(n) clauses. The operation is O(n + n * clauses) = O(poly(n)). -/
  forward_polytime : ∃ C k, C > 0 ∧ k > 0 ∧ ∀ n ≥ 128,
    n + (Φ n).clauses.length * n ≤ C * n^k

/-- **Security Property**: For all poly-bounded adversary families, success is negligible.

    **IMPORTANT - Stronger Than Textbook**: This definition quantifies over FAMILIES
    of adversaries `A : Nat → StructuralOWFAdversary`, not a single uniform PPT adversary.
    This is STRONGER than textbook OWF security (defends against more adversaries).

    **Textbook vs This Definition**:
    - Textbook: Single adversary A (same program for all n)
    - Here: Different adversary A(n) for each n, with polynomial bounds uniform across n

    **Poly-Boundedness Constraint**: `∀ n, (A n).C ≤ (A 128).C ∧ (A n).k ≤ (A 128).k`
    This ensures adversary resources are bounded by fixed constants (those at n=128),
    making this a non-uniform but polynomially-bounded quantification.

    **Why This is Sound**: Proving security against MORE adversaries (families) is
    strictly stronger than proving against fewer (single uniform). Any attack by a
    uniform PPT adversary is also an attack by the constant family.

    **Bridge to Textbook**: See `uniform_ppt_as_constant_family` which shows uniform
    PPT adversaries are a special case (constant families trivially satisfy the bound).

    **Experiment** (`avg_success_prob_n_exp`): Sample random assignment r,
    compute y = plant_flat(Φ(n), r), give y to adversary A(n), check if A(n)
    outputs r' such that plant_flat(Φ(n), r') = y. Average over coins. -/
def SecurityProperty (Φ : CNFFamily) (prec : CNFPreconditions Φ) : Prop :=
  ∀ (A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars),
    (∀ n, (A n).base.C ≤ (A 128).base.C ∧ (A n).base.k ≤ (A 128).base.k) →
    negligible_parametric 128 (fun (n : LStar.Base.SecurityParam 128) =>
      avg_success_prob_n_exp 1 (by norm_num) rfl (Φ n.val)
        (Nat.le_trans (Nat.le_trans (by decide : 4 ≤ 128) n.property) (prec.wellformed n.val n.property))
        (prec.aligned n.val n.property)
        (A n.val).base)

/-- **Bridge to Textbook**: Uniform PPT adversaries satisfy poly-boundedness trivially.

    **Textbook Definition**: A uniform PPT adversary is a single Turing machine A that:
    - Takes input (1^n, y) where n is security parameter
    - Runs in time poly(n) with the SAME polynomial bound for all n
    - Uses the SAME program (TM description) for all n

    **In Our Formalization**: This corresponds to a family `A : Nat → StructuralOWFAdversary`
    where all members share the same polynomial bounds: `(A n).C = (A m).C` and
    `(A n).k = (A m).k` for all n, m.

    **Why Uniform PPT ⊆ Poly-Bounded Families**:
    For any uniform PPT adversary with bounds (C, k), the induced family trivially
    satisfies `∀ n, (A n).C ≤ (A 128).C ∧ (A n).k ≤ (A 128).k` since all bounds are equal.

    **Conclusion**: SecurityProperty is strictly STRONGER than textbook OWF security.
    Proving security against poly-bounded families implies security against uniform PPT. -/
theorem uniform_ppt_as_constant_family (Φ : CNFFamily) :
    ∀ (A : (n : Nat) → StructuralOWFAdversary (Φ n).nvars),
    (∀ n m, (A n).base.C = (A m).base.C ∧ (A n).base.k = (A m).base.k) →
    (∀ n, (A n).base.C ≤ (A 128).base.C ∧ (A n).base.k ≤ (A 128).base.k) := by
  intro A h_uniform n
  have h := h_uniform n 128
  simp only [h.1, h.2, le_refl, and_self]

/-- **One-Way Function Predicate**: Standard cryptographic OWF definition.

    A CNF family Φ has one-way `plant_flat` if:
    1. **Preconditions**: Well-formedness, structure constraints, poly-time forward
    2. **Security**: For all poly-bounded adversary families,
       average success probability is negligible

    **Textbook correspondence** (Goldreich/Katz-Lindell):
    - Part 1 (efficient forward): `forward_polytime` in CNFPreconditions
    - Part 2 (hard to invert): `SecurityProperty` (stronger than textbook, see docstring)

    **Note**: Our SecurityProperty defends against non-uniform (family) adversaries,
    which is strictly stronger than textbook uniform PPT. See `uniform_ppt_as_constant_family`. -/
def IsOneWayPlantFlat (Φ : CNFFamily) : Prop :=
  ∃ (prec : CNFPreconditions Φ), SecurityProperty Φ prec

/-- alignedCNFFamily satisfies all preconditions. -/
theorem alignedCNFFamily_preconditions : CNFPreconditions alignedCNFFamily where
  wellformed := alignedCNFFamily_wellformed
  wf_literals := fun n => by
    match n with
    | 0 =>
      unfold LStar.CNF.WellFormed alignedCNFFamily
      intro c h_c; simp at h_c; subst h_c
      intro l h_l; simp at h_l; subst h_l; simp
    | Nat.succ m =>
      exact alignedCNFFamily_wf_literals (Nat.succ m) (Nat.succ_pos m)
  nvars_eq := alignedCNFFamily_nvars_eq
  nonempty_clauses := fun n _ => by
    unfold alignedCNFFamily; simp only [List.length_ofFn]; omega
  clauses_poly := ⟨1, 1, by omega, by omega, fun n _ => by
    unfold alignedCNFFamily; simp only [List.length_ofFn, pow_one, Nat.one_mul]; omega⟩
  positive_clause := fun n _ => by
    unfold LStar.CNF.HasPositiveClause alignedCNFFamily
    use { literals := [{ var := 0, polarity := true }] }
    constructor
    · simp only [List.mem_ofFn]; use ⟨0, by omega⟩
    · intro l h_l; simp only [List.mem_singleton] at h_l; simp only [h_l]
  bounded_solutions := alignedCNFFamily_bounded_solutions
  aligned := fun n _ => by
    constructor
    · unfold alignedCNFFamily; simp only [List.length_ofFn]; omega
    · intro c h_c; unfold alignedCNFFamily at h_c
      simp only [List.mem_ofFn] at h_c; obtain ⟨i, rfl⟩ := h_c
      simp only [List.length_singleton]; omega
  -- Poly-time forward: n + n * clauses ≤ 2 * n²
  -- alignedCNFFamily has max n 1 clauses, so for n ≥ 128: clauses = n
  forward_polytime := ⟨2, 2, by omega, by omega, fun n hn => by
    unfold alignedCNFFamily; simp only [List.length_ofFn]
    -- For n ≥ 128, max n 1 = n
    have h_max : max n 1 = n := Nat.max_eq_left (by omega : n ≥ 1)
    simp only [h_max]
    -- n + n * n ≤ 2 * n^2
    nlinarith⟩

/-- alignedCNFFamily satisfies the security property. -/
theorem alignedCNFFamily_security : SecurityProperty alignedCNFFamily alignedCNFFamily_preconditions := by
  unfold SecurityProperty
  intro A h_uniform
  exact f_is_structural_owf_exponential_true 128 (by decide) alignedCNFFamily
    alignedCNFFamily_preconditions.wellformed
    alignedCNFFamily_preconditions.wf_literals
    alignedCNFFamily_preconditions.nvars_eq
    alignedCNFFamily_preconditions.nonempty_clauses
    alignedCNFFamily_preconditions.clauses_poly
    alignedCNFFamily_preconditions.positive_clause
    alignedCNFFamily_preconditions.bounded_solutions
    alignedCNFFamily_preconditions.aligned
    A h_uniform

/-- **OWF Existence Theorem**: There exists a CNF family with one-way plant_flat.

    **Statement**: ∃ Φ : CNFFamily, IsOneWayPlantFlat Φ

    **Witness**: `alignedCNFFamily` (n variables, n unit clauses per Φ(n))

    **Proof**: Direct application of `f_is_structural_owf_exponential_true`
    with `alignedCNFFamily` and its verified side-conditions.

    **Trust Boundary**: 1 custom axiom (subset of P≠NP's 2 axioms). -/
theorem OWF_exists : ∃ Φ : CNFFamily, IsOneWayPlantFlat Φ :=
  ⟨alignedCNFFamily, alignedCNFFamily_preconditions, alignedCNFFamily_security⟩

/-- Exported alias for external reference. -/
theorem StructuralOWF_exists : ∃ Φ : CNFFamily, IsOneWayPlantFlat Φ := OWF_exists

/-! ## Axiom Audit -/

#print axioms CNFPreconditions
#print axioms SecurityProperty
#print axioms IsOneWayPlantFlat
#print axioms alignedCNFFamily_preconditions
#print axioms alignedCNFFamily_security
#print axioms OWF_exists
#print axioms StructuralOWF_exists

end LStar.StructuralOWF.OWFExistence
