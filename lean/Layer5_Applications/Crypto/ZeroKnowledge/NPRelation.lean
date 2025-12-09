import Layer2_StructuralOWF.Plant.PlantCore
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
  x : LStarInstanceFG

/-- Witness: randomness r. -/
structure ZKWitness where
  r : Randomness
  h_dgLen : (φ : CNF) → r.dgLen = (Nat.log 2 φ.nvars) ^ 2

/-- R(⟨φ, x*⟩, r) := WellFormedRandomness(φ, r) ∧ plant(φ, r) = x*. -/
def NPRelation (stmt : Statement) (w : ZKWitness) : Prop :=
  WellFormedRandomness stmt.φ w.r ∧
  plant_n 1 stmt.φ w.r stmt.h_nvars (w.h_dgLen stmt.φ) = stmt.x

end LStar.ZK
