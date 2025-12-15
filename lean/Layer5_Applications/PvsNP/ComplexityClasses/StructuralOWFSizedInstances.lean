import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes

/-! ## Sized Instances for OWF Types

Provides `Sized` typeclass instances for types used in OWF security proofs.

**Instances**:
- `LStarInstanceFG`: size = dag.n (number of DAG vertices)
- `Randomness nvars`: size = nvars (assignment bits) + digest length + structural bits
- `Witness nvars`: size = nvars (assignment bits) + proof count + digest bits + 1

Randomness and Witness are parametrized by nvars with finite assignment type
(Fin nvars → Bool). The size measure uses nvars directly.

**Trust Boundary**: Definitional instances with no axioms.
-/

namespace LStar.Complexity

open LStar.StructuralOWF.Foundations
open LStar.StructuralOWF

/-- Compute assignment support size (positions with true values).
    Bounded by 128 as upper estimate for finite support.
    Used for AssignmentInf (infinite) type. -/
def assignment_support_size (assignment : LStar.AssignmentInf) : Nat :=
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

/-- Sized instance for Randomness nvars.
    Size measure: nvars + digest length + structural bits.
    The nvars directly gives the assignment encoding length (finite assignment is nvars bits).
    Note: The size is always positive due to h_sufficient_salts (≥64 structural bits). -/
instance (nvars : Nat) : Sized (Randomness nvars) where
  size r :=
    nvars + r.gateDigests.foldl (fun acc (_d : Vector Bool r.dgLen) => acc + r.dgLen) 0 + r.structuralBits.length
  size_pos r := by
    have h_struct : r.structuralBits.length ≥ 64 := r.h_sufficient_salts
    omega

/-- Sized instance for Witness nvars.
    Size measure: nvars + proof count + digest bits + 1.
    The nvars directly gives the assignment encoding length (finite assignment is nvars bits).
    Note: The size is always positive due to the +1. -/
instance (nvars : Nat) : Sized (Witness nvars) where
  size w :=
    nvars + w.gateProofs.foldl (fun acc _p => acc + 1) 0 + w.digestBits.length + 1
  size_pos _w := by
    omega  -- +1 ensures positivity

#print axioms Sized

end LStar.Complexity
