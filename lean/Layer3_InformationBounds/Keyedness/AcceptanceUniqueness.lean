import Layer3_InformationBounds.WorldCommit.CutWorlds
import Layer3_InformationBounds.ConstraintSystem.NormalForm
import Infrastructure.Witness.VerifiedWitness
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer2_StructuralOWF.Plant.PlantExponential
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig
import Layer3_InformationBounds.Decision.LStarNP
import Mathlib.Data.Finset.Card

/-! ## AcceptanceUniqueness: Utility Lemmas and Planted Instance Predicates

**Main Content**:
- DAG size bounds for planted instances
- World difference detection lemmas
- `IsPlantedWithWellFormedRandomness` predicate

**Witness Uniqueness (Flat Profile)**:
The witness uniqueness theorems have been migrated to the flat/exponential profile:
- `WorldCompatibleWithVerifiedWitness_flat` in PlantExponential.lean
- `HasWitnessUniqueness_flat` in PlantExponential.lean
- `strong_compatibility_implies_uniqueness_flat` in PlantExponential.lean (FULLY PROVEN)
- `planted_instances_have_uniqueness_flat` in PlantExponential.lean (FULLY PROVEN)

**Note**: The QP-profile versions have been removed as part of the QP-profile deprecation.
All critical theorems now use the flat profile which is fully proven without sorry.

**Trust Boundary**: Utility lemmas proven from A1-A5 (no axioms).

**Paper**: §9.3 "Acceptance Implies Uniqueness", Lemma C.2.ACC-logical
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF LStar.StructuralOWF.Decision
open NormalForm  -- For FeasibleUnderNF

/-! ## Worlds and Config Differences -/

/-- If two cut‑worlds are distinct, then they differ at some cut node. -/
theorem different_worlds_different_emergent
    (L : LStarInstanceFG)
    (C : Finset (Fin L.dag.n))
    (ω₁ ω₂ : CutWorld L C)
    (h_distinct : ω₁ ≠ ω₂) :
    ∃ (v : Fin L.dag.n) (h_in : v ∈ C), ω₁.assignment v h_in ≠ ω₂.assignment v h_in := by
  by_contra h_all_equal
  push_neg at h_all_equal
  -- If all assignments agree, worlds are equal by function extensionality
  have h_eq : ω₁ = ω₂ := by
    cases ω₁
    cases ω₂
    congr
    funext v h_in
    exact h_all_equal v h_in
  exact h_distinct h_eq

/-! ## Digest Monotonicity (1-bit Discriminator) -/

/-- Different parities → different observable digests.

    **Role**: DISCRIMINATOR propagation — parity difference implies digest difference.

    This is acceptable as 1-bit because:
    - fgDigestBit is the OBSERVABLE output (what algorithm sees)
    - Hardness comes from underlying R-bit configs via A2 injectivity
    - Parity witnesses config difference; A2 converts to seed difference -/
theorem digest_diff_of_parity_diff {n : Nat}
    (a b : Fin (2^n))
    (h : localParity a ≠ localParity b) : fgDigestBit a ≠ fgDigestBit b :=
  different_parity_different_digest a b h

/-! ## DAG Size Bounds -/

/-- **DAG size lower bound**: build3SATReductionDAG has at least 1 + nvars + nclauses vertices.

    **Purpose**: Structural property of the DAG construction.
    This is NOT a hypothesis - it's a provable fact about totalNodes.

    **Proof strategy**: DAG has 1 source + nvars variables + nclauses clauses + tree nodes.
    So dag.n = 1 + nvars + nclauses + reductionTreeSize nclauses ≥ 1 + nvars + nclauses. -/
lemma build3SATReductionDAG_size_bound (φ : CNF)
    : (Construction.build3SATReductionDAG φ).n ≥ 1 + φ.nvars + φ.clauses.length := by
  -- DAG has total = 1 + nvars + nclauses + reductionTreeSize vertices
  -- So dag.n = total ≥ 1 + nvars + nclauses (since reductionTreeSize ≥ 0)
  simp only [Construction.build3SATReductionDAG]
  -- After simplification, we have a record with n := total
  -- where total = 1 + nvars + nclauses + reductionTreeSize
  suffices 1 + φ.nvars + φ.clauses.length + Construction.reductionTreeSize φ.clauses.length
           ≥ 1 + φ.nvars + φ.clauses.length by exact this
  omega

/-- **Gate vertices are valid**: For planted instances with single gate (r.gateDigests.length = 1),
    the gate vertex at clause_start exists in the DAG.

    **Purpose**: Structural lemma (NOT hypothesis) - provable from DAG construction.

    **Proof**: clause_start = 1 + nvars, and dag.n ≥ 1 + nvars + nclauses.
    For non-empty formulas (nclauses > 0), clause_start < dag.n. -/
lemma clause_start_in_dag {φ : CNF} (h_nonempty : φ.clauses.length > 0)
    : 1 + φ.nvars < (Construction.build3SATReductionDAG φ).n := by
  have h_bound := build3SATReductionDAG_size_bound φ
  omega

/-- **Gate index validity**: For planted instances, gate vertices are within DAG bounds.

    **Purpose**: Structural lemma about gate vertex indices.
    This is NOT a hypothesis - it's provable from numGates ≤ nclauses constraint.

    **Proof**: vertex_idx = clause_start + gateIdx < clause_start + numGates
             ≤ clause_start + nclauses ≤ dag.n (by size_bound) -/
lemma gate_vertex_in_dag (φ : CNF) (numGates : Nat)
    (h_gates_valid : numGates ≤ φ.clauses.length)
    (gateIdx : Nat) (h_idx : gateIdx < numGates)
    : 1 + φ.nvars + gateIdx < (Construction.build3SATReductionDAG φ).n := by
  have h_bound := build3SATReductionDAG_size_bound φ
  omega

/-! ## Planted Instance Predicate -/

/-- Predicate: L is a planted instance with well-formed randomness.

    **Purpose**: Abstract characterization for planted instances.
    Uses WellFormedRandomness (QP-profile) for backwards compatibility.

    **Note**: For exponential profile proofs, use `IsPlantedWithWellFormedRandomness_flat`
    from PlantExponential.lean which uses `WellFormedRandomness_flat`.

    **Properties checked**:
    - Exists parameters (n, φ, r) with WellFormedRandomness
    - L equals plant_flat n φ r
    - φ has positive variables (φ.nvars > 0)
    - r has gate digests (r.gateDigests.length > 0)
-/
def IsPlantedWithWellFormedRandomness (L : LStarInstanceFG) : Prop :=
  ∃ (n : Nat) (φ : CNF) (r : Randomness φ.nvars) (h_nvars : φ.nvars ≥ 4) (h_aligned : AlignedCNFConstraints φ),
    WellFormedRandomness φ r ∧
    L = plant_flat n φ r h_nvars h_aligned ∧
    φ.nvars > 0 ∧
    r.gateDigests.length > 0

/-! ## List Helpers -/

/-- **List.all correctness**: If all elements satisfy predicate, then each element does.

    Standard lemma connecting List.all with universal quantification.
-/
lemma list_all_true_mem {α : Type*} (p : α → Bool) (l : List α) (h_all : l.all p = true) :
    ∀ x ∈ l, p x = true := by
  intro x h_mem
  -- Use List.all_eq_true from Mathlib which states: l.all p ↔ ∀ x ∈ l, p x
  rw [List.all_eq_true] at h_all
  exact h_all x h_mem

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms different_worlds_different_emergent
#print axioms digest_diff_of_parity_diff
#print axioms build3SATReductionDAG_size_bound
#print axioms clause_start_in_dag
#print axioms gate_vertex_in_dag
#print axioms IsPlantedWithWellFormedRandomness

end LStar.StructuralOWF.Foundations
