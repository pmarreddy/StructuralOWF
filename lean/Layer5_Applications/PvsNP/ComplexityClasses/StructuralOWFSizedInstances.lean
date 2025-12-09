import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes

/-! ## Sized Instances for OWF Types

Provides `Sized` typeclass instances for types used in OWF security proofs.

**Instances**:
- `LStarInstanceFG`: size = dag.n (number of DAG vertices)
- `Randomness`: size = assignment support + digest length + structural bits
- `Witness`: size = assignment support + proof count + digest bits + 1

**Trust Boundary**: Definitional instances with no axioms.
-/

namespace LStar.Complexity

open LStar.StructuralOWF.Foundations
open LStar.StructuralOWF

/-- Compute assignment support size (positions with true values).
    Bounded by 128 as upper estimate for finite support. -/
def assignment_support_size (assignment : Nat → Bool) : Nat :=
  (List.range 128).filter (fun i => assignment i = true) |>.length

/-- DAG size bounds: dag.n ≥ L.n for any LStarInstanceFG. -/
lemma dag_n_ge_nvars (L : LStarInstanceFG) : L.dag.n ≥ L.n :=
  L.dag_size_ge_n

/-- Sized instance for LStarInstanceFG.
    Size measure: number of vertices in the DAG. -/
instance : Sized LStarInstanceFG where
  size L := L.dag.n
  size_pos L := by
    have h_struct : L.dag.n ≥ L.n := L.dag_size_ge_n
    have h_n_pos : 0 < L.n := L.n_pos
    omega

/-- Sized instance for Randomness.
    Size measure: total encoding length. -/
instance : Sized Randomness where
  size r :=
    let assignment_size := assignment_support_size r.assignment
    let gate_digests_size := r.gateDigests.foldl (fun acc (_d : Vector Bool r.dgLen) => acc + r.dgLen) 0
    let structural_size := r.structuralBits.length
    assignment_size + gate_digests_size + structural_size
  size_pos r := by
    simp [assignment_support_size]
    have h_gate : r.gateDigests.foldl (fun acc (_d : Vector Bool r.dgLen) => acc + r.dgLen) 0 ≥ r.dgLen := by
      have h_single : r.gateDigests.length = 1 := r.h_single_gate
      obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp h_single
      simp [hd]
    have h_dgLen_pos : r.dgLen > 0 := r.h_dgLen_pos
    have h_struct : r.structuralBits.length ≥ 64 := r.h_sufficient_salts
    omega

/-- Sized instance for Witness.
    Size measure: total encoding length + 1 for positivity. -/
instance : Sized Witness where
  size w :=
    let assignment_size := assignment_support_size w.assignment
    let gate_proofs_size := w.gateProofs.foldl (fun acc _p => acc + 1) 0
    let digest_bits_size := w.digestBits.length
    assignment_size + gate_proofs_size + digest_bits_size + 1
  size_pos _w := by
    simp only [assignment_support_size]
    omega

#print axioms Sized

end LStar.Complexity
