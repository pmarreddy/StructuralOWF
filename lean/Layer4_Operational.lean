/-! # Layer 4: Operational Semantics

Exports all Layer 4 modules: Turing machine execution and time bound bridges.
-/

-- TuringMachine foundations
import Layer4_Operational.TuringMachine.TMAxioms
import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer4_Operational.TuringMachine.TMEncoderDefs

-- Time bridges (TM execution → information bounds)
import Layer4_Operational.TimeBridge.TMAdapterExponential  -- Exponential profile

-- Execution semantics
import Layer4_Operational.ExecutionSemantics.ExecSemantics
import Layer4_Operational.ExecutionSemantics.ExecutionSemantics
