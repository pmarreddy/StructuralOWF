import Layer2_StructuralOWF.Plant.PlantCore
import Layer2_StructuralOWF.Plant.PlantExponential
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig

/-! # NP Relation for L* Zero-Knowledge

R(⟨φ, x*⟩, r) holds iff r ∈ D(φ) and plant(φ, r) = x*.

**Reference**: Paper §9.1
-/

namespace LStar.ZK

open LStar
open LStar.StructuralOWF
open LStar.StructuralOWF.Foundations

/-- Public statement: (φ, x*). -/
structure Statement where
  φ : CNF
  h_nvars : φ.nvars ≥ 4
  h_aligned : AlignedCNFConstraints φ
  x : LStarInstanceFG

/-- Witness: randomness r parametrized by nvars.
    Track A Refactor: Witness is now tied to a specific nvars. -/
structure ZKWitness (nvars : Nat) where
  r : Randomness nvars

/-- R(⟨φ, x*⟩, r) := WellFormedRandomness(φ, r) ∧ plant(φ, r) = x*. -/
def NPRelation (stmt : Statement) (w : ZKWitness stmt.φ.nvars) : Prop :=
  WellFormedRandomness stmt.φ w.r ∧
  plant_flat 1 stmt.φ w.r stmt.h_nvars stmt.h_aligned = stmt.x

end LStar.ZK
