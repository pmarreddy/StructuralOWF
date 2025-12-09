import Layer0_Foundations.Base.CNF
import Layer0_Foundations.Base.BoundedSecurityParam  -- For Nat.log_two_four_eq_two
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log

/-! ## RandomnessTypes: Randomness Structure for OWF Construction

This module defines the randomness input type for the planting function f: r ↦ x*.

**Structure**: The randomness r ∈ {0,1}^m decomposes as:
- `dgLen`: Digest length parameter (scales with security profile)
- `assignment`: Boolean assignment to n variables
- `gateDigests`: FG digest values (single dgLen-bit digest)
- `structuralBits`: Cryptographic salts (≥64 bits)

**Security Profiles**:
- QP-Sharp: dgLen = (log₂ n)² yields quasi-polynomial bounds
  - dgLen MUST scale because R = (log₂ n)² requires matching digest size
- Exponential: dgLen can be any constant ≥ 64 (e.g., 64) for exponential bounds
  - Security comes from R = n, NOT from dgLen
  - The main P≠NP proof uses dgLen = 64 (sufficient, simpler witness type)
  - `expDigestLen = n` is the theoretical maximum, not required

**Architectural Constraint**: Single FG gate (gateDigests.length = 1) required by
the fg_emergence_bound invariant Σ_{v∈C} R_v ≤ R_fg.

**Trust Boundary**: Pure type definitions with no axioms.

**Reference**: §4.1 "Randomness Structure", §4.3 "Single-Gate Architecture".
-/
namespace LStar.StructuralOWF

/-- Boolean assignment mapping variable indices to truth values. -/
abbrev Assignment := Nat → Bool

/-- Randomness structure for the planting function f: r ↦ x*.

Represents r ∈ {0,1}^m with security constraints enforced at the type level.
The parametric digest length dgLen enables different security profiles. -/
structure Randomness where
  /-- Digest length parameter, scaling with security profile. -/
  dgLen : Nat

  /-- Positivity constraint ensuring meaningful parity computation. -/
  h_dgLen_pos : dgLen > 0

  /-- Satisfying assignment for the embedded 3-SAT formula. -/
  assignment : Assignment

  /-- Gate digests: list of dgLen-bit vectors (constrained to length 1). -/
  gateDigests : List (Vector Bool dgLen)

  /-- Cryptographic salts for enumeration barrier.
      Random bits wired into FG designated addresses, forcing 2^64 enumeration. -/
  structuralBits : List Bool

  /-- Salt length constraint: ≥64 bits for 2^64 enumeration barrier. -/
  h_sufficient_salts : structuralBits.length ≥ 64

  /-- Single gate constraint required by fg_emergence_bound invariant. -/
  h_single_gate : gateDigests.length = 1

/-- QP-Sharp profile digest length: (log₂ n)². -/
def qpDigestLen (nvars : Nat) : Nat :=
  let log_n := Nat.log 2 nvars
  log_n * log_n

/-- Exponential profile digest length: n (theoretical maximum).

    NOTE: The main P≠NP proof uses dgLen = 64, not n. This is sufficient because:
    - Exponential security comes from R = n (the flat R-profile), not dgLen
    - Any dgLen ≥ 64 provides adequate collision resistance
    - Fixed dgLen = 64 simplifies witness type to `Bits (n + 128)`

    This function exists for theoretical completeness and potential future use. -/
def expDigestLen (nvars : Nat) : Nat := nvars

/-- QP digest length equals (log₂ n)². -/
@[simp] theorem qpDigestLen_eq_log_squared (nvars : Nat) :
    qpDigestLen nvars = (Nat.log 2 nvars) ^ 2 := by
  unfold qpDigestLen
  rw [Nat.pow_two]

/-- QP digest length is positive for n ≥ 4. -/
theorem qpDigestLen_pos (nvars : Nat) (h : nvars ≥ 4) : qpDigestLen nvars > 0 := by
  unfold qpDigestLen
  have h_log : Nat.log 2 nvars ≥ 2 := by
    calc Nat.log 2 nvars ≥ Nat.log 2 4 := Nat.log_mono_right h
      _ = 2 := Nat.log_two_four_eq_two
  calc Nat.log 2 nvars * Nat.log 2 nvars
      ≥ 2 * 2 := Nat.mul_le_mul h_log h_log
    _ = 4 := by rfl
    _ > 0 := by decide

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

    **What each field is**:
    - `assignment`: The satisfying assignment α for the CNF formula φ
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
structure Witness where
  /-- Satisfying assignment α for the CNF formula φ. -/
  assignment : Assignment

  /-- Per-bit gate proof items. For single-gate instances, can be `[]` because
      the path structure is implicit (only one FG gate exists). -/
  gateProofs : List GateProofItem

  /-- The dgLen-bit digest value for verification. For single-gate instances,
      this is the full digest that the verifier recomputes and compares. -/
  digestBits : List Bool

end LStar.StructuralOWF

#print axioms LStar.StructuralOWF.Randomness
#print axioms LStar.StructuralOWF.Witness
