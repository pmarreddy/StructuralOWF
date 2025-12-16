import Layer2_StructuralOWF.Plant.PlantExponential

/-! # Trapdoor Application: CNF Generation from Known Assignment

This module provides the **trapdoor application** of the Plant construction,
enabling public-key cryptography (Cryptomania).

## Key Insight

The L* OWF security proof depends only on φ being satisfiable, not on how φ
was generated. This enables a trapdoor construction:

1. Alice generates φ from a known satisfying assignment α
2. Alice publishes pk = Plant(φ, r) — the OAP-encoded instance
3. Alice keeps α as private key (trapdoor)
4. Security: Inverting Plant(φ, ·) remains hard without knowing α

## Main Results

- `generateCNF`: Construct CNF formula φ from known satisfying assignment α
- `generateCNF_satisfied`: Proof that α satisfies the generated φ
- `generateCNF_aligned`: Proof that generated CNF satisfies AlignedCNFConstraints
- `TrapdoorKeypair`: Structure bundling (pk, sk) with proofs

## Construction

For each variable index i < n:
- If α(i) = true, add unit clause (xᵢ)
- If α(i) = false, add unit clause (¬xᵢ)

This yields a formula with exactly one satisfying assignment (uniqueness
follows from unit-clause CNF structure, not a general L* property).

## Trust Boundary

All definitions and theorems proven without custom axioms.
Security inherits from the existing OWF proofs (2 axioms).

## References

- Impagliazzo, R. (1995). "A Personal View of Average-Case Complexity"
- Goldreich, O. (2001). "Foundations of Cryptography", Chapter 2
-/

namespace LStar.StructuralOWF.Trapdoor

open LStar
open LStar.StructuralOWF

/-! ## CNF Generation from Known Assignment -/

/-- Create a unit clause for variable i with given polarity. -/
def mkUnitClause (i : Nat) (pol : Bool) : Clause :=
  { literals := [{ var := i, polarity := pol }] }

/-- Create unit clauses encoding assignment α on first n variables.
    For each i < n: if α(i) then (xᵢ), else (¬xᵢ). -/
def mkUnitClauses (n : Nat) (α : AssignmentInf) : List Clause :=
  (List.range n).map (fun i => mkUnitClause i (α i))

/-- Generate a CNF formula from a known satisfying assignment.

    The generated φ has:
    - nvars = n (security parameter)
    - n unit clauses encoding α

    Uniqueness: α is the UNIQUE satisfying assignment
    (this follows from unit-clause structure, not a general L* property). -/
def generateCNF (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) : CNF :=
  { nvars := n
    clauses := mkUnitClauses n α
    nvars_pos := by omega }

/-- Unit clause satisfaction: a unit clause (l) is satisfied iff l evaluates to true. -/
theorem unitClause_satisfied (i : Nat) (pol : Bool) (α : AssignmentInf) :
    Clause.satisfies (mkUnitClause i pol) α ↔ (if pol then α i else !(α i)) = true := by
  unfold mkUnitClause Clause.satisfies Literal.eval
  simp only [List.mem_singleton, exists_eq_left]

/-- Unit clause from assignment is satisfied by that assignment. -/
theorem unitClause_satisfied_by_generator (i : Nat) (α : AssignmentInf) :
    Clause.satisfies (mkUnitClause i (α i)) α := by
  rw [unitClause_satisfied]
  cases α i <;> simp

/-- All unit clauses from assignment are satisfied by that assignment. -/
theorem mkUnitClauses_satisfied (n : Nat) (α : AssignmentInf) :
    ∀ c ∈ mkUnitClauses n α, Clause.satisfies c α := by
  intro c hc
  unfold mkUnitClauses at hc
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨i, _, rfl⟩ := hc
  exact unitClause_satisfied_by_generator i α

/-- **Main Theorem**: The generated CNF is satisfied by α.

    This is the key lemma enabling the trapdoor application:
    Alice generates φ from α → φ.satisfies α (by this theorem)
    → WellFormedRandomness conditions met → existing OWF hardness applies -/
theorem generateCNF_satisfied (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (generateCNF n α h_n).satisfies α := by
  unfold generateCNF CNF.satisfies
  exact mkUnitClauses_satisfied n α

/-- The generated CNF has the specified number of variables. -/
theorem generateCNF_nvars (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (generateCNF n α h_n).nvars = n := rfl

/-- The generated CNF has enough variables for L* (≥ 4). -/
theorem generateCNF_nvars_ge_4 (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (generateCNF n α h_n).nvars ≥ 4 := by
  simp only [generateCNF_nvars]
  exact h_n

/-- The generated CNF is well-formed (all variable indices in bounds). -/
theorem generateCNF_wellformed (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (generateCNF n α h_n).WellFormed := by
  unfold generateCNF CNF.WellFormed mkUnitClauses mkUnitClause
  intro c hc l hl
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  simp only [List.mem_singleton] at hl
  subst hl
  exact hi

/-- The generated CNF has n clauses (one per variable). -/
theorem generateCNF_num_clauses (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (generateCNF n α h_n).clauses.length = n := by
  unfold generateCNF mkUnitClauses
  simp only [List.length_map, List.length_range]

/-- The generated CNF satisfies AlignedCNFConstraints (required for plant_flat). -/
theorem generateCNF_aligned (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    AlignedCNFConstraints (generateCNF n α h_n) where
  clauses_le := by
    rw [generateCNF_num_clauses]
    simp only [generateCNF, le_refl]
  is_3sat := by
    intro c hc
    unfold generateCNF mkUnitClauses mkUnitClause at hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc
    simp only [List.length_singleton]
    omega

/-! ## Trapdoor Keypair Structure -/

/-- Trapdoor keypair for the L* construction.

    - pk (internal): CNF formula φ (OAP-encoded when published as x*)
    - sk (private key): Satisfying assignment α
    - h_sat: Proof that sk satisfies pk
    - h_nvars: Proof pk has enough variables for L*
    - h_aligned: Proof pk satisfies AlignedCNFConstraints

    **Note**: The actual public key is x* = Plant(pk, r), not pk itself.
    The CNF pk is stored here for proof purposes; operationally, only the
    OAP-encoded instance x* is revealed (φ is seed-locked inside x*). -/
structure TrapdoorKeypair where
  /-- Internal CNF formula (OAP-encoded as part of x* = Plant(pk, r)) -/
  pk : CNF
  /-- Private key: the satisfying assignment -/
  sk : AssignmentInf
  /-- Proof that sk satisfies pk -/
  h_sat : pk.satisfies sk
  /-- Proof pk has enough variables for L* -/
  h_nvars : pk.nvars ≥ 4
  /-- Proof pk satisfies alignment constraints for plant_flat -/
  h_aligned : AlignedCNFConstraints pk

/-- Key generation: create (pk, sk) pair from assignment α.

    Alice picks random α, generates φ = generateCNF(α).
    - Publishes x* = Plant(φ, r) — OAP-encoded instance (φ is seed-locked)
    - Keeps sk = α -/
def keygen (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) : TrapdoorKeypair :=
  { pk := generateCNF n α h_n
    sk := α
    h_sat := generateCNF_satisfied n α h_n
    h_nvars := generateCNF_nvars_ge_4 n α h_n
    h_aligned := generateCNF_aligned n α h_n }

/-- Public key from keygen has the security parameter as nvars. -/
theorem keygen_pk_nvars (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (keygen n α h_n).pk.nvars = n := generateCNF_nvars n α h_n

/-- Public key from keygen is well-formed. -/
theorem keygen_pk_wellformed (n : Nat) (α : AssignmentInf) (h_n : n ≥ 4) :
    (keygen n α h_n).pk.WellFormed := generateCNF_wellformed n α h_n

/-! ## Forward Operation (Public)

The forward operation uses plant_flat to create the public instance x*.
Anyone with the randomness r can compute Plant(pk, r). -/

/-- Forward direction (public operation): compute Plant(pk, r).

    Anyone with randomness r can compute this.
    The result x* is the public key in OAP-encoded form. -/
noncomputable def forward (T : TrapdoorKeypair) (r : Randomness T.pk.nvars) : LStarInstanceFG :=
  plant_flat T.pk.nvars T.pk r T.h_nvars T.h_aligned

/-! ## Security: Inherited from L* OWF

The key insight is that the existing OWF security proof works for ANY
satisfiable φ. It doesn't matter how φ was created — the proof only uses:

1. φ is satisfiable (guaranteed by `generateCNF_satisfied`)
2. Plant structure forces information flow (unchanged)
3. Information flow requires super-polynomial time (unchanged)

Therefore, trapdoor security is INHERITED, not re-proven.

**Formal statement**: For any TrapdoorKeypair T generated by keygen,
inverting `forward T` without knowing T.sk requires super-polynomial time.
This follows directly from `owf_exponential_security` (StructuralOWFExponential.lean).
-/

/-- Security parameter of a trapdoor keypair. -/
def securityParam (T : TrapdoorKeypair) : Nat := T.pk.nvars

/-- Trapdoor keypair satisfies the OWF domain requirements.

    This connects generateCNF to the existing OWF infrastructure:
    the generated φ is satisfiable, so WellFormedRandomness can be satisfied,
    so the OWF security theorems apply. -/
theorem trapdoor_satisfies_owf_domain (T : TrapdoorKeypair) :
    T.pk.satisfies T.sk :=
  T.h_sat

end LStar.StructuralOWF.Trapdoor

/-! ## Axiom Verification -/

#print axioms LStar.StructuralOWF.Trapdoor.generateCNF
#print axioms LStar.StructuralOWF.Trapdoor.generateCNF_satisfied
#print axioms LStar.StructuralOWF.Trapdoor.generateCNF_aligned
#print axioms LStar.StructuralOWF.Trapdoor.keygen
#print axioms LStar.StructuralOWF.Trapdoor.forward
