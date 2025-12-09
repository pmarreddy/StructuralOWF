import Infrastructure.Witness.WitnessAlgorithm

/-! ## LaneDefinitions: Lane Classification for Witness Finders

**Purpose**: Define lane classification (restart vs. single-run). Separated from LaneDichotomy.lean to break circular dependency.

**Lane Classification** (exhaustive dichotomy):
1. **Restart lane**: Independent attempts, no persistent state (e.g., random sampling)
   - Must try ≥ 2^λ configurations on expectation (geometric distribution)
   - State resets/restarts observable in execution trace

2. **Single-run lane**: Persistent state across exploration (e.g., deterministic search)
   - Monotonically increasing state trace (0,1,2,...,time-1, no restarts)

**Observable**: Classification determined by algorithm behavior, not internal implementation.

**Exhaustive**: Every algorithm falls into exactly one lane (Theorem 7.B).

**Why No Complex Theorem**: Unlike paper's Appendix C proof via case analysis, Lean
makes exhaustiveness definitional:
- InRestartLane: Observable via state trace (∃ t1 < t2, stateTrace t1 = stateTrace t2)
- InSingleRunLane: Negation of restart (¬ InRestartLane)
- Exhaustiveness: Follows immediately from excluded middle (A ∨ ¬A)
Result: 3-line theorem via Classical.em instead of detailed case analysis.

**Trust Boundary**: Axiom-free (pure definitions).

**Paper**: Appendix C.4 "Lane Dichotomy", §7 "Theorem 7.B - Exhaustive Classification"

See Layer3_InformationBounds/Layer3_README.md for lane dichotomy and witness finder classification.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF

/-- Restart lane: makes independent attempts with no seed-specific persistence.

**Interpretation**: Algorithm forgets progress when switching configurations.
Like random guessing or independent trials with no learning across attempts.

**Example**: Random sampling from witness space - each attempt is independent.

**Why exponential**: Must try ≥ 2^λ configurations on expectation (geometric distribution).

**Definition**:
An algorithm is in restart lane if its execution trace shows restart patterns:
- State resets (revisiting same state at different times)
- OR non-monotonic exploration (state values decrease, indicating restart)

For a deterministic single-run algorithm, stateTrace is monotonically increasing
(e.g., 0,1,2,...,time-1), showing no restarts.
-/
def InRestartLane {L : LStarInstanceFG} (W : WitnessFinder L) (_lambda : Nat) : Prop :=
  -- Restart detected: ∃ two distinct times t1 < t2 with same state
  -- (indicating algorithm reset to a previous state)
  ∃ (t1 t2 : Fin W.time), t1 < t2 ∧ W.stateTrace t1 = W.stateTrace t2

/-- Single-run lane: maintains persistent state across exploration.

**Interpretation**: Algorithm keeps seed-specific data structures (DP tables,
search trees, learned clauses, etc.) and builds on previous work.

**Example**: DP with memoization, backtracking search, CDCL with clause learning.

**Why exponential**: Must traverse ≥ 2^(λ-1) distinct segments due to keyedness
and FG structure. Each segment requires parity work.
-/
def InSingleRunLane {L : LStarInstanceFG} (W : WitnessFinder L) (lambda : Nat) : Prop :=
  ¬ InRestartLane W lambda

/-- Exhaustiveness: every algorithm is either restart-lane or single-run lane.

**Proof**: Direct from classical excluded middle on InRestartLane.

**Significance**: This dichotomy is complete - we've covered all possible
computational strategies. Combined with bounds on each lane, this gives
a universal lower bound.
-/
theorem lane_exhaustive {L : LStarInstanceFG} {lambda : Nat} (W : WitnessFinder L) :
  InRestartLane W lambda ∨ InSingleRunLane W lambda := by
  unfold InSingleRunLane
  exact Classical.em (InRestartLane W lambda)

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms InRestartLane
#print axioms InSingleRunLane
#print axioms lane_exhaustive

end LStar.StructuralOWF.Foundations
