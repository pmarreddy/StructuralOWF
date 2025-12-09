import Infrastructure.Witness.WitnessAlgorithm
import Layer3_InformationBounds.Keyedness.LaneDefinitions

/-! ## SemanticNormalForm: SNF Instrumentation Wrapper (Axiom-Free)

**Purpose**: Lightweight wrapper modeling Appendix I "Semantic Normal Form" instrumentation.

**Design** (§7, Appendix I): SNF as identity on WitnessFinder with preservation lemmas—preserves behavior, makes monotonicity immediate for observable quantities (time, states_visited, correctness), preserves lane classification.

**Minimal approach**: SNF = identity + preservation lemmas. Future extensions can attach ledgers/counters without changing clients.

**Key lemmas**:
- snfWrap: Identity function (snfWrap W = W)
- Preservation: snf_time_eq, snf_states_eq, snf_stateTrace_eq, snf_output_eq
- Lane invariance: snf_restart_iff, snf_single_run_iff

**Trust boundary**: 3 axiom audits - all proven (identity + simp lemmas)

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF

/-! ## SNF Wrapper -/

/-- SNF instrumentation of a witness finder. At the current abstraction level,
    SNF does not change the computation; it only conceptually records extra
    semantic information. Hence we model it as the identity. -/
@[simp]
def snfWrap {L : LStarInstanceFG} (W : WitnessFinder L) : WitnessFinder L := W

/-! ## Preservation Lemmas -/

@[simp] theorem snf_time_eq {L} (W : WitnessFinder L) : (snfWrap W).time = W.time := rfl
@[simp] theorem snf_states_eq {L} (W : WitnessFinder L) : (snfWrap W).states_visited = W.states_visited := rfl
@[simp] theorem snf_stateTrace_eq {L} (W : WitnessFinder L) :
    (snfWrap W).stateTrace = W.stateTrace := rfl
@[simp] theorem snf_trace_card_eq {L} (W : WitnessFinder L) :
    WitnessFinder.visitedStates (snfWrap W) = WitnessFinder.visitedStates W := rfl
@[simp] theorem snf_output_eq {L} (W : WitnessFinder L) : (snfWrap W).output = W.output := rfl

theorem snf_time_ge_iff {L} (W : WitnessFinder L) (t : Nat) : (snfWrap W).time ≥ t ↔ W.time ≥ t := by
  simp

theorem snf_states_ge_iff {L} (W : WitnessFinder L) (v : Nat) : (snfWrap W).states_visited ≥ v ↔ W.states_visited ≥ v := by
  simp

/-! ## Lane Invariance -/

theorem InRestartLane_snf_iff {L} (W : WitnessFinder L) (lambda : Nat) :
  InRestartLane (snfWrap W) lambda ↔ InRestartLane W lambda := by
  unfold InRestartLane
  constructor
  · intro h
    rcases h with ⟨n, hn2, htime⟩
    exact ⟨n, hn2, by simpa [snf_time_eq] using htime⟩
  · intro h
    rcases h with ⟨n, hn2, htime⟩
    exact ⟨n, hn2, by simpa [snf_time_eq] using htime⟩

theorem InSingleRunLane_snf_iff {L} (W : WitnessFinder L) (lambda : Nat) :
  InSingleRunLane (snfWrap W) lambda ↔ InSingleRunLane W lambda := by
  unfold InSingleRunLane
  simp only [InRestartLane_snf_iff]

/-! ## WLOG Lemmas

The following lemmas justify analyzing `snfWrap W` instead of `W` in proofs
that depend on time or lane classification: SNF preserves both. -/

theorem wlog_time_from_snf {L} (W : WitnessFinder L) {t : Nat}
  (h : (snfWrap W).time ≥ t) : W.time ≥ t := by
  simpa [snf_time_eq] using h

theorem wlog_restart_from_snf {L} (W : WitnessFinder L) {lambda : Nat}
  (h : InRestartLane (snfWrap W) lambda) : InRestartLane W lambda :=
  (InRestartLane_snf_iff W lambda).mp h

theorem wlog_single_from_snf {L} (W : WitnessFinder L) {lambda : Nat}
  (h : InSingleRunLane (snfWrap W) lambda) : InSingleRunLane W lambda :=
  (InSingleRunLane_snf_iff W lambda).mp h

/-! ## Axiom Verification

These definitions and lemmas use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms snfWrap
#print axioms snf_time_eq
#print axioms InRestartLane_snf_iff
#print axioms InSingleRunLane_snf_iff

end LStar.StructuralOWF.Foundations
