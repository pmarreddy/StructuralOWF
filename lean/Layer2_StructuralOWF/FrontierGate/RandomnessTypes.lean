import Layer0_Foundations.Base.CNF
import Layer0_Foundations.Base.BoundedSecurityParam  -- For Nat.log_two_four_eq_two
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log

/-! ## RandomnessTypes: Randomness Structure for OWF Construction

This module defines the randomness input type for the planting function f: r ↦ x*.

**Structure**: The randomness r ∈ {0,1}^m decomposes as:
- `nvars`: Number of variables (the n parameter)
- `dgLen`: Digest length parameter (scales with security profile)
- `assignment`: Boolean assignment to n variables (FINITE: Fin nvars → Bool)
- `gateDigests`: FG digest values (single dgLen-bit digest)
- `structuralBits`: Cryptographic salts (≥64 bits)

**Track A Refactor (Bitstring Encoding)**:
Assignment is now `LStar.Assignment nvars = Fin nvars → Bool` (finite!), not `Nat → Bool`.
This is required for proper complexity-theoretic formalization where witnesses must be
finite bit strings that can be encoded in {0,1}^poly(n).

**Security Profile** (Exponential):
- dgLen can be any constant ≥ 64 (the main P≠NP proof uses dgLen = 64)
- Security comes from R = n (the flat R-profile), NOT from dgLen
- `expDigestLen = n` is the theoretical maximum, not required

**Architectural Constraint**: Single FG gate (gateDigests.length = 1) required by
the fg_emergence_bound invariant Σ_{v∈C} R_v ≤ R_fg.

**Trust Boundary**: Pure type definitions with no axioms.

**Reference**: §4.1 "Randomness Structure", §4.3 "Single-Gate Architecture".
-/
namespace LStar.StructuralOWF

-- Re-export the finite Assignment type from CNF.lean
-- Assignment n = Fin n → Bool (finite, encodable as n bits)
-- AssignmentInf = Nat → Bool (infinite, for internal evaluation)

/-- Randomness structure for the planting function f: r ↦ x*.

Represents r ∈ {0,1}^m with security constraints enforced at the type level.
The parametric nvars and dgLen enable different CNF sizes and security profiles.

**Track A**: Now parametrized by nvars, with finite assignment type. -/
structure Randomness (nvars : Nat) where
  /-- Digest length parameter, scaling with security profile. -/
  dgLen : Nat

  /-- Positivity constraint ensuring meaningful parity computation. -/
  h_dgLen_pos : dgLen > 0

  /-- Satisfying assignment for the embedded 3-SAT formula.
      FINITE: exactly nvars bits, encodable as {0,1}^nvars. -/
  assignment : LStar.Assignment nvars

  /-- Gate digests: list of dgLen-bit vectors (constrained to length 1). -/
  gateDigests : List (Vector Bool dgLen)

  /-- Cryptographic salts for enumeration barrier.
      Random bits wired into FG designated addresses, forcing 2^64 enumeration. -/
  structuralBits : List Bool

  /-- Salt length constraint: ≥64 bits for 2^64 enumeration barrier. -/
  h_sufficient_salts : structuralBits.length ≥ 64

  /-- Single gate constraint required by fg_emergence_bound invariant. -/
  h_single_gate : gateDigests.length = 1

/-- Convert finite assignment in Randomness to infinite for evaluation. -/
def Randomness.assignmentInf {nvars : Nat} (r : Randomness nvars) : LStar.AssignmentInf :=
  r.assignment.extend

/-- Exponential profile digest length: n (theoretical maximum).

    NOTE: The main P≠NP proof uses dgLen = 64, not n. This is sufficient because:
    - Exponential security comes from R = n (the flat R-profile), not dgLen
    - Any dgLen ≥ 64 provides adequate collision resistance
    - Fixed dgLen = 64 simplifies witness type to `Bits (n + 128)`

    This function exists for theoretical completeness and potential future use. -/
def expDigestLen (nvars : Nat) : Nat := nvars

/-- Exponential digest length is positive for n ≥ 1. -/
theorem expDigestLen_pos (nvars : Nat) (h : nvars ≥ 1) : expDigestLen nvars > 0 := by
  unfold expDigestLen
  omega

/-- Gate proof item: position and value for FG verification.

    Each GateProofItem encodes one bit of a gate's digest:
    - `gateVertex`: Which FG gate (vertex index in DAG)
    - `position`: Which bit position within the dgLen-bit digest
    - `value`: The bit value (true/false)

    For **single-gate instances** (h_single_gate), there is exactly one FG gate,
    so all items have the same `gateVertex`. The `digestBits` field provides
    the same information more compactly. -/
structure GateProofItem where
  gateVertex : Nat
  position : Nat
  value : Bool

/-- Witness for L* verification: W = (assignment, gateProofs, digestBits).

    **Track A Refactor**: Now parametrized by `nvars` with FINITE assignment type.
    This is required for proper complexity-theoretic formalization where witnesses
    must be finite bit strings in {0,1}^poly(n).

    **What each field is**:
    - `assignment`: The satisfying assignment α for the CNF formula φ (FINITE: nvars bits)
    - `gateProofs`: Per-bit gate proof items (which gate, which position, what value)
    - `digestBits`: The dgLen-bit digest value for the FG gate(s)

    **Paper vs Code terminology**:
    - Paper's "w" = `assignment`
    - Paper's "G_τ" = path enumeration {(P, S(P))} — in code, path is implicit (single gate)
    - Paper's "Dig_τ[P]" = 1-bit parity per path P
    - Code's `digestBits` = full dgLen-bit digest (more than paper's per-path parity)

    **Single-gate simplification** (h_single_gate: gateDigests.length = 1):

    The L* construction uses exactly ONE FrontierGate. This simplifies everything:

    1. **Only one path P exists** — no need to enumerate paths
    2. **`gateProofs` can be `[]`** — the verifier knows there's one gate
    3. **`digestBits` = the dgLen-bit digest** — verifier recomputes and compares

    The verifier doesn't need `gateProofs` to know which gate to check — there's
    only one gate, and its structure is in the instance x*.

    **Why `gateProofs := []` is valid**: With one gate, the "path enumeration"
    G_τ is trivial. The verifier:
    1. Knows there's exactly one FG gate (from instance structure)
    2. Recomputes the dgLen-bit digest from the assignment
    3. Compares against `digestBits`

    No explicit path list needed. The `gateProofs` field exists for potential
    multi-gate extensions but is unused in current single-gate proofs.

    See: Paper §10.4.1, Appendix C.1.1 -/
structure Witness (nvars : Nat) where
  /-- Satisfying assignment α for the CNF formula φ.
      FINITE: exactly nvars bits, encodable as {0,1}^nvars. -/
  assignment : LStar.Assignment nvars

  /-- Per-bit gate proof items. For single-gate instances, can be `[]` because
      the path structure is implicit (only one FG gate exists). -/
  gateProofs : List GateProofItem

  /-- The dgLen-bit digest value for verification. For single-gate instances,
      this is the full digest that the verifier recomputes and compares. -/
  digestBits : List Bool

/-- Convert finite assignment in Witness to infinite for evaluation. -/
def Witness.assignmentInf {nvars : Nat} (w : Witness nvars) : LStar.AssignmentInf :=
  w.assignment.extend

end LStar.StructuralOWF

#print axioms LStar.StructuralOWF.Randomness
#print axioms LStar.StructuralOWF.Witness
