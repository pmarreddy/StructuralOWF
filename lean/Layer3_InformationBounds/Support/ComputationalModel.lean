import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs

/-! ## ComputationalModel: Machine Parameters & Work Coefficient

**Purpose**: Explicit model of machine parameters (tapes, alphabet) → per-operation work coefficient for parity-cost bounds.

**Key structures** (§7, Appendix D):
- TapeModel: Minimal tape/alphabet model (tapes ≥ 1, alphabetSize ≥ 2)
- workPerOp: Work coefficient α = 1/(tapes * log₂(alphabet)) as rational
- alphaFromModel: Convert to ℝ for bounds (default matches α = 1/64)

**Design**: Factors out hardcoded constant into parametric definition with sensible defaults.

**Main results**: TapeModel.standard (k-tape byte model), workPerOp (rational work coeff), defaultAlpha (α ≈ 1/64)

**Trust boundary**: 5 axiom audits - all proven

See Layer3_InformationBounds/Layer3_README.md §Support Infrastructure.
-/

namespace LStar.StructuralOWF.Foundations

/-! ## Tape / Alphabet Model -/

/-- Minimal tape/alphbet model for Turing-style cost accounting. -/
structure TapeModel where
  /-- Number of work tapes (positive). -/ 
  tapes : Nat
  /-- Alphabet size (at least binary). -/
  alphabetSize : Nat
  /-- Positivity witness for tapes. -/
  tapes_pos : 0 < tapes
  /-- Lower bound on alphabet size (avoid log2 = 0). -/
  alphabet_ge_two : 2 ≤ alphabetSize

namespace TapeModel

/-- A standard `k`-tape model over a byte alphabet. -/
def standard (k : Nat) (hk : 0 < k) : TapeModel :=
  { tapes := k
    alphabetSize := 256
    tapes_pos := hk
    alphabet_ge_two := by decide }

end TapeModel

/-! ## Work Per Operation -/

/-- Work coefficient per designated parity operation.

`workPerOp = 1 / (tapes * log₂(alphabet))` as a rational number.

Notes:
- The denominator is positive under `tapes_pos` and `alphabet_ge_two`.
- This abstracts the constant used in per-segment parity-cost bounds. -/
def workPerOp (model : TapeModel) : Rat :=
  1 / ((model.tapes * Nat.log2 model.alphabetSize : Nat) : Rat)

/-- Alias for the per-operation coefficient. -/
abbrev alphaFromModel (model : TapeModel) : Rat := workPerOp model

/-- A default model matching the legacy constant α = 1/64.

Choose 8 tapes and 256-symbol alphabet ⇒ tapes * log₂(alphabet) = 8 * 8 = 64. -/
def defaultTapeModel : TapeModel := TapeModel.standard 8 (by decide)

/-- Default work coefficient `α = 1/64` (via `defaultTapeModel`). -/
def defaultAlpha : Rat := alphaFromModel defaultTapeModel

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms TapeModel
#print axioms workPerOp
#print axioms alphaFromModel
#print axioms defaultTapeModel
#print axioms defaultAlpha

end LStar.StructuralOWF.Foundations

