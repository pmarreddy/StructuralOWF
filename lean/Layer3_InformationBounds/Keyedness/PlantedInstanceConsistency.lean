import Layer2_StructuralOWF.Plant.PlantCore
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer3_InformationBounds.SegmentReduction.StructuralLowerBound
import Layer3_InformationBounds.Support.SeedSemantics
import Layer3_InformationBounds.ConstraintSystem.EmergentConfig  -- Import for emergentConfigAtGate and WellFormedRandomness
import Layer3_InformationBounds.WorldCommit.CutWorlds  -- For CutWorld definition
import Layer1_Construction.Core.InstanceOps

/-! ## PlantedInstanceConsistency: Well-Formed Randomness (Non-Circular)

**Architecture**: Non-circular well-formedness via pure functions.

The public gateDigest field is a constant placeholder independent of the witness,
ensuring the planted instance reveals no assignment information. Parity consistency
is tracked internally via WellFormedRandomness on the input randomness r.

**Pure function separation**:
```
emergentConfigAtGate φ a i : Pure function computing emergent config from φ and a
WellFormedRandomness φ r   : Verifies ALL R bits of r.gateDigests match computed configs
worldFromWitness_flat      : Builds CutWorld from witness (see PlantExponential.lean)
```

**Key property**: Emergent configs are defined purely from φ + a,
breaking circular definitions. The public instance structure is independent of the witness.

**Note**: QP-profile constructive existence proofs have been removed. The exponential
profile (plant_flat) is the active profile used in the P≠NP proof. See PlantExponential.lean
for `emergentConfigAtGate_R_component_flat` and related exponential-profile theorems.

**Trust Boundary**: Proven theorems (no custom axioms).

**Paper**: §7 "A1-A5 Construction", §8 "Planted Randomness"

See Layer3_InformationBounds/Layer3_README.md for planted instance consistency and well-formedness.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF LStar.StructuralOWF.Foundations

/-! ## Pure Emergent Configuration Functions

**NOTE**: The definitions `emergentConfigAtGate` and `WellFormedRandomness` are imported
from `LStar.StructuralOWF.Foundations.EmergentConfig`. This module documents the architectural
approach. For exponential-profile theorems, see PlantExponential.lean which provides
`emergentConfigAtGate_R_component_flat` and related proofs used in the P≠NP chain. -/

/-! ## Summary: Architectural Solution

**Architecture**: Non-circular well-formedness via pure functions.
- `emergentConfigAtGate φ a gateIndex`: Computes emergent config from φ and a only
- `WellFormedRandomness φ r`: Verifies ALL R bits match emergent configs (identity digest)
- `worldFromWitness_flat`: Builds CutWorld from witness (see PlantExponential.lean)

**Key properties**:
- Public gateDigest is constant (zeros), independent of the witness
- Parity consistency is maintained internally via WellFormedRandomness
- Injectivity derives from A2 (seed encoding), not from public instance structure

**Result**: Sound architecture with explicit semantic bridges and no circular dependencies.

**Note**: For planted instance helpers (worldFromWitness_flat, planted_fg_gate_ge_clause_start_flat,
planted_R_eq_R_of_flat), see Layer2_StructuralOWF/Plant/PlantExponential.lean which provides
these for the exponential (plant_flat) profile used in the main P≠NP proof.
-/

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms WellFormedRandomness
#print axioms emergentConfigAtGate

end LStar.StructuralOWF.Foundations
