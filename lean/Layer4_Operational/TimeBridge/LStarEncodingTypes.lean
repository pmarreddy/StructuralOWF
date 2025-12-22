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
- `SameObservationSameState`: Same extracted config → same TM state

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

/-- **SameObservationSameState**: Same extracted config → same TM state.

    **INTUITION**: The TM only knows what it has computed. Its state is determined
    by what it has extracted, not by what was "secretly" planted.

    **WHY IT MATTERS**: If two planted configs produce the same extracted config
    at step t, they're in the same TM state. This limits distinguishing power:
    the TM can only distinguish configs it has actually observed.

    **FORMAL PROPERTY**: For all cfg_planted and t:
      let state_t := step^[t] (initForPlanting cfg_planted)
      let c := extractConfigAtV state_t
      step^[t] (initForPlanting c) = state_t

    i.e., if TM extracts config c at time t, then running with c planted
    reaches the exact same state.
-/
def SameObservationSameState
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

/-! ## Halt Preservation Properties

For WorstCaseCorrectOnLStar to extend to larger times (monotonicity), we need:
1. TM doesn't modify tape 0 after halting
2. extractConfigAtV only depends on tape 0
-/

/-- **HaltPreservesTape0**: TM writes the same symbol to tape 0 when in halt state.

    This property ensures that once halted, the TM doesn't modify tape 0's content.
    Combined with extractConfigAtV reading only from tape 0, this enables
    WorstCaseCorrectOnLStar to extend to times beyond the halt time.

    **Property**: When in a halt state, the symbol written to tape 0 equals the current symbol.
    (Effectively a no-op for tape 0 content) -/
def HaltPreservesTape0
    {k : Nat} {states alphabet : Type}
    [NeZero k]
    (M : TuringMachine k states alphabet) : Prop :=
  ∀ (s : states) (syms : Fin k → alphabet),
    s ∈ M.halt → (M.δ s syms).2.1 ⟨0, NeZero.pos k⟩ = syms ⟨0, NeZero.pos k⟩

/-- **ExtractReadsOnlyTape0**: extractConfigAtV only depends on tape 0 content.

    This property ensures that if two TM configurations have the same tape 0,
    then extractConfigAtV returns the same value for both.

    **Purpose**: Combined with HaltPreservesTape0, enables proving that
    extractConfigAtV is stable after the TM halts. -/
def ExtractReadsOnlyTape0
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {L : LStarInstanceFG}
    {M : TuringMachine k states alphabet}
    {v : Fin L.dag.n}
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v))) : Prop :=
  ∀ (cfg₁ cfg₂ : TMConfig M),
    cfg₁.tapes ⟨0, NeZero.pos k⟩ = cfg₂.tapes ⟨0, NeZero.pos k⟩ →
    extractConfigAtV cfg₁ = extractConfigAtV cfg₂

/-- Tape 0 content at a position is unchanged by step when position ≠ head and in halt state. -/
theorem tape0_other_pos_unchanged_step
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {M : TuringMachine k states alphabet}
    (cfg : TMConfig M)
    (pos : Nat)
    (h_neq : pos ≠ cfg.heads ⟨0, NeZero.pos k⟩) :
    (TMConfig.step cfg).tapes ⟨0, NeZero.pos k⟩ pos = cfg.tapes ⟨0, NeZero.pos k⟩ pos := by
  simp only [TMConfig.step, TMConfig.write, Function.update]
  split_ifs with h
  · exact absurd h h_neq
  · rfl

/-- Tape 0 content at head position is unchanged after step when in halt state with HaltPreservesTape0. -/
theorem tape0_head_pos_unchanged_step
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {M : TuringMachine k states alphabet}
    (h_preserve : HaltPreservesTape0 M)
    (cfg : TMConfig M)
    (h_halt : cfg.state ∈ M.halt) :
    (TMConfig.step cfg).tapes ⟨0, NeZero.pos k⟩ (cfg.heads ⟨0, NeZero.pos k⟩) =
    cfg.tapes ⟨0, NeZero.pos k⟩ (cfg.heads ⟨0, NeZero.pos k⟩) := by
  simp only [TMConfig.step, TMConfig.write, Function.update]
  exact h_preserve cfg.state (fun i => cfg.tapes i (cfg.heads i)) h_halt

/-- **Tape 0 is unchanged after one step when in halt state with HaltPreservesTape0.** -/
theorem tape0_unchanged_step
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {M : TuringMachine k states alphabet}
    (h_preserve : HaltPreservesTape0 M)
    (cfg : TMConfig M)
    (h_halt : cfg.state ∈ M.halt) :
    (TMConfig.step cfg).tapes ⟨0, NeZero.pos k⟩ = cfg.tapes ⟨0, NeZero.pos k⟩ := by
  ext pos
  by_cases h_eq : pos = cfg.heads ⟨0, NeZero.pos k⟩
  · rw [h_eq]
    exact tape0_head_pos_unchanged_step h_preserve cfg h_halt
  · exact tape0_other_pos_unchanged_step cfg pos h_eq

/-- **Tape 0 is unchanged after n steps when starting in halt state with HaltPreservesTape0.** -/
theorem tape0_unchanged_iterate
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {M : TuringMachine k states alphabet}
    (h_preserve : HaltPreservesTape0 M)
    (cfg : TMConfig M)
    (h_halt : cfg.state ∈ M.halt)
    (n : Nat) :
    ((TMConfig.step)^[n] cfg).tapes ⟨0, NeZero.pos k⟩ = cfg.tapes ⟨0, NeZero.pos k⟩ := by
  induction n with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    have h_halt_n : ((TMConfig.step)^[n] cfg).state ∈ M.halt :=
      halt_persists M cfg n h_halt
    rw [tape0_unchanged_step h_preserve ((TMConfig.step)^[n] cfg) h_halt_n, ih]

/-- **extractConfigAtV is stable after halting**: Same value at times t1 and t2 ≥ t1 when TM halts at t1. -/
theorem extractConfigAtV_stable_after_halt
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {L : LStarInstanceFG}
    {M : TuringMachine k states alphabet}
    {v : Fin L.dag.n}
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    (h_preserve : HaltPreservesTape0 M)
    (h_extract_tape0 : ExtractReadsOnlyTape0 extractConfigAtV)
    (cfg : Fin (2^(L.R v)))
    (t1 t2 : Nat)
    (h_halt : ((TMConfig.step)^[t1] (initForPlanting cfg)).state ∈ M.halt)
    (h_t2_ge : t2 ≥ t1) :
    extractConfigAtV ((TMConfig.step)^[t2] (initForPlanting cfg)) =
    extractConfigAtV ((TMConfig.step)^[t1] (initForPlanting cfg)) := by
  -- Decompose t2 = (t2 - t1) + t1 so iterate_add_apply gives us step^[t2-t1] (step^[t1] x)
  have h_decomp : t2 = (t2 - t1) + t1 := (Nat.sub_add_cancel h_t2_ge).symm
  rw [h_decomp, Function.iterate_add_apply]
  -- After t1 steps, the TM is in halt state
  let cfg_t1 := (TMConfig.step)^[t1] (initForPlanting cfg)
  -- Running (t2 - t1) more steps doesn't change tape 0
  have h_tape0_eq : ((TMConfig.step)^[t2 - t1] cfg_t1).tapes ⟨0, NeZero.pos k⟩ =
                    cfg_t1.tapes ⟨0, NeZero.pos k⟩ :=
    tape0_unchanged_iterate h_preserve cfg_t1 h_halt (t2 - t1)
  -- Since extract only reads tape 0, the result is the same
  exact h_extract_tape0 _ _ h_tape0_eq

/-- **WorstCaseCorrectOnLStar Monotonicity**: Extends correctness to larger times.

    If WorstCaseCorrectOnLStar holds at time t1 and the TM halts at t1,
    then it holds at any time t2 ≥ t1, provided:
    1. TM doesn't modify tape 0 after halting (HaltPreservesTape0)
    2. extractConfigAtV only reads tape 0 (ExtractReadsOnlyTape0)

    **Key insight**: Once halted, extractConfigAtV gives the same result,
    so correctness at t1 implies correctness at t2.
-/
theorem WorstCaseCorrectOnLStar_monotone
    {k : Nat} {states alphabet : Type}
    [NeZero k] [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    {L : LStarInstanceFG}
    {M : TuringMachine k states alphabet}
    {v : Fin L.dag.n}
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    (t1 t2 : Nat)
    (h_wc : WorstCaseCorrectOnLStar L M v extractConfigAtV initForPlanting t1)
    (h_halts : ∀ cfg, ((TMConfig.step)^[t1] (initForPlanting cfg)).state ∈ M.halt)
    (h_preserve : HaltPreservesTape0 M)
    (h_extract_tape0 : ExtractReadsOnlyTape0 extractConfigAtV)
    (h_t2_ge : t2 ≥ t1) :
    WorstCaseCorrectOnLStar L M v extractConfigAtV initForPlanting t2 := by
  intro cfg
  -- By stability, extract at t2 equals extract at t1
  have h_stable := extractConfigAtV_stable_after_halt extractConfigAtV initForPlanting
    h_preserve h_extract_tape0 cfg t1 t2 (h_halts cfg) h_t2_ge
  -- By WorstCaseCorrectOnLStar at t1, extract at t1 equals cfg
  have h_wc_t1 := h_wc cfg
  -- Combine: extract at t2 = extract at t1 = cfg
  simp only at h_wc_t1 h_stable ⊢
  rw [h_stable, h_wc_t1]

-- Axiom audits
#print axioms WorstCaseCorrectOnLStar
#print axioms SameObservationSameState
#print axioms HaltPreservesTape0
#print axioms ExtractReadsOnlyTape0
#print axioms tape0_unchanged_step
#print axioms tape0_unchanged_iterate
#print axioms extractConfigAtV_stable_after_halt
#print axioms WorstCaseCorrectOnLStar_monotone

end LStar.StructuralOWF.Foundations
