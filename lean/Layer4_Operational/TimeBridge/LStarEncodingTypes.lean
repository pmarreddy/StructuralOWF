import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer4_Operational.TuringMachine.TuringMachineSemantics

/-! ## LStarEncodingTypes: L*-TM Encoding Structure Definitions

**Purpose**: Defines the encoding structure types for L*-TM correspondence.

**Why this file**: These definitions are used in both:
- `StructuralOWFAdversary` (Layer5) - as structure fields
- `WC1Bridge` (Layer4) - in theorems and proofs

To avoid circular imports (TMAxioms → StructuralOWFAdversary → WC1Bridge),
these type definitions are extracted here.

**Types Defined**:
- `WorstCaseCorrectOnLStar`: TM outputs correct config for ALL plantings
- `ReplantingSimulation`: Replanting coherence property

See Layer4_Operational/TimeBridge/WC1Bridge.lean for usage.
-/

namespace LStar.StructuralOWF.Foundations

open LStar.StructuralOWF

/-- **WorstCaseCorrectOnLStar**: TM outputs correct config for ALL plantings.

    This property asserts that a Turing Machine M correctly identifies the planted
    emergent configuration at vertex v for ANY planting in the valid range.

    **Parameters**:
    - L: An L* instance with Frontier Gate
    - M: Turing Machine
    - v: Vertex in L's DAG
    - extractConfigAtV: Function to extract emergent config from TM state
    - initForPlanting: Function to create initial TM state from planted config
    - haltTime: Time at which TM halts

    **Property**: For all cfg : Fin (2^(L.R v)):
      let finalState := step^[haltTime] (initForPlanting cfg)
      extractConfigAtV finalState = cfg

    i.e., after haltTime steps, the TM's output matches what was planted.
-/
def WorstCaseCorrectOnLStar
    {k : Nat} {states alphabet : Type}
    [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    (L : LStarInstanceFG)
    (M : TuringMachine k states alphabet)
    (v : Fin L.dag.n)
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    (haltTime : Nat)
    : Prop :=
  -- For ANY valid planted config cfg at vertex v
  ∀ (cfg : Fin (2^(L.R v))),
    -- The TM's final extracted config at v equals cfg
    -- (i.e., TM correctly identifies which config was planted)
    let finalState := (TMConfig.step (M := M))^[haltTime] (initForPlanting cfg)
    extractConfigAtV finalState = cfg

/-- **ReplantingSimulation**: Replanting coherence property.

    This property asserts that the encoding is coherent: what the TM observes
    matches what was planted, enabling deterministic replay.

    **Property**: For all cfg_planted and t:
      let state_t := step^[t] (initForPlanting cfg_planted)
      let c := extractConfigAtV state_t
      step^[t] (initForPlanting c) = state_t

    i.e., if TM extracts config c at time t, then running with c planted
    reaches the exact same state.

    **Why this matters**: This property enables the time lower bound proof.
    If the TM could distinguish between plantings before actually computing
    the emergent config, it would violate this simulation property.
-/
def ReplantingSimulation
    {k : Nat} {states alphabet : Type}
    [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    (L : LStarInstanceFG)
    (M : TuringMachine k states alphabet)
    (v : Fin L.dag.n)
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    : Prop :=
  -- For any planting cfg_planted and any step t:
  -- If TM extracts config c at step t, then running with c planted reaches same state
  ∀ (cfg_planted : Fin (2^(L.R v))) (t : Nat),
    let state_t := (TMConfig.step (M := M))^[t] (initForPlanting cfg_planted)
    let c := extractConfigAtV state_t
    (TMConfig.step (M := M))^[t] (initForPlanting c) = state_t

-- Axiom audits
#print axioms WorstCaseCorrectOnLStar
#print axioms ReplantingSimulation

end LStar.StructuralOWF.Foundations
