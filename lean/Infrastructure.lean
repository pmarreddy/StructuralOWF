/-! # Infrastructure

Exports cross-cutting infrastructure modules: Witness algorithms and time bound interfaces.

**Witness algorithm models**:
- WitnessAlgorithm: Abstract algorithm interface (general model)
- Active chain: TMAdapterExponential uses direct TM → WitnessFinder construction
- Alternative: WitnessFinderConcrete (two-layer architecture, not in active chain)
-/

-- Witness algorithms
import Infrastructure.Witness.WitnessAlgorithm
-- import Infrastructure.Witness.Alternative.WitnessFinderConcrete  -- Alternative path (not in active chain, has 2 sorries)
import Infrastructure.Witness.VerifiedWitness
import Infrastructure.Witness.AlgorithmSeparation
import Infrastructure.Witness.CorrectnessImpliesExhaustive
import Infrastructure.Witness.WitnessFinderBridge
import Infrastructure.Witness.WitnessFinderSoundnessBridge

