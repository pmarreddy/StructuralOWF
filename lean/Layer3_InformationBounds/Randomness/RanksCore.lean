import Layer0_Foundations.Base.CNF
import Layer0_Foundations.Base.BoundedSecurityParam  -- For Nat.log_two_four_eq_two
import Mathlib.Data.Nat.Log

/-! ## RanksCore: Core Rank Function Infrastructure

**Main Definitions**:
- `EmergenceProfile` - Enum for profile selection (exponential used)
- `computeR` - Profile-parametric R computation
- `R_of` - Base rank function (R = (log₂ n)² formula, kept for reference)
- `is_fg_gate` - FG gate position predicate

**Why extracted**: Breaks circular dependencies (PlantCore ↔ Foundations). Pure rank computation
used by Plant.lean, SeedSemantics.lean, EmergentConfig.lean.

**FG Placement**: Gates at clause layer (positions [clause_start, clause_start + numGates)).
- FG gates: R_v > 0 (emergence requirement)
- Non-FG nodes: R_v = 0 (sources, variables, non-FG clauses, reduction tree)

**Trust Boundary**: Axiom-free (pure function definitions).

**Used by**: PlantCore.lean, SeedSemantics.lean, RanksExponential.lean

Note: The exponential profile (R = n) is defined in RanksExponential.lean and is the
active profile used in the P≠NP proof.
-/

namespace LStar.StructuralOWF.Foundations

/-! ## Emergence Profile

The emergence profile determines how R (emergence rank) is computed at FG gates.
This affects both the hardness bound and the digest size.

- **QP (Quasi-Polynomial)**: R = (log₂ n)², giving 2^R = n^(log n) hardness
- **Exponential**: R = n, giving 2^R = 2^n hardness

The profile is used throughout the codebase to ensure consistent R computation
in planting, decoding, and verification. -/

/-- Emergence profile for FG gates.

    Determines how R (emergence rank) is computed:
    - `qp`: R = (log₂ nvars)² - quasi-polynomial hardness
    - `exponential`: R = nvars - exponential hardness

    **Usage**: Pass to `computeR` to get profile-specific R value.
    **Consistency**: Must match between planting and verification. -/
inductive EmergenceProfile
  | qp          -- R = (log₂ n)², bound = n^(log n)
  | exponential -- R = n, bound = 2^n
  deriving DecidableEq, Repr

/-- Compute R (emergence rank) for a given profile and nvars.

    This is the **single source of truth** for R computation.
    All code that needs R at FG gates should use this function.

    **QP Profile**: R = (log₂ nvars)²
    - Gives quasi-polynomial hardness: 2^R = nvars^(log nvars)
    - Used in QP-sharp security proofs

    **Exponential Profile**: R = nvars
    - Gives exponential hardness: 2^R = 2^nvars
    - Used in exponential security proofs (stronger but less standard)

    **Note**: For non-FG vertices, R = 0 regardless of profile. This function
    computes R for FG gates only; use `R_of` or `R_of_flat` for full DAG. -/
def computeR (profile : EmergenceProfile) (nvars : Nat) : Nat :=
  match profile with
  | .qp => (Nat.log 2 nvars) ^ 2
  | .exponential => nvars

/-- QP profile gives (log₂ n)². -/
theorem computeR_qp (nvars : Nat) : computeR .qp nvars = (Nat.log 2 nvars) ^ 2 := rfl

/-- Exponential profile gives n. -/
theorem computeR_exponential (nvars : Nat) : computeR .exponential nvars = nvars := rfl

#print axioms computeR

/-- **Emergence rank R_v for planted instances** (extracted from Plant.lean).

    **Purpose**: Computes how many emergent bits each node v requires.

    **Parameterization**: Now takes numGates explicitly to match randomness structure.
    - For planted instances: numGates = r.gateDigests.length
    - For pure structure: numGates can be any valid count

    **FG Placement Strategy**: Gates placed at CLAUSE layer (NOT source!)
    - FG gates occupy positions [clause_start, clause_start + numGates)
    - Ensures R_v > 0 only at actual gate nodes (not sources/variables)
    - Each FG gate gets R_v = (log₂ nvars)² for QP-sharp hardness

    **Returns**:
    - (log₂ nvars)² for FG gate nodes (QP-sharp configuration space)
    - 0 for all other nodes (sources, variables, non-FG clauses, reduction tree)

    **Correctness**: Must satisfy:
    - FG gates have R_v > 0 (emergence requirement)
    - Non-FG nodes have R_v = 0 (no emergence)
    - Matches planted instance R field exactly (type consistency)

    **Usage**: Used consistently in:
    - plant_flat (PlantExponential.lean)
    - lstarStructureFromCNF
    - emergentConfigAtGate (via lstarStructureFromCNF)

    This eliminates type mismatches by ensuring R values are computed identically! -/
def R_of (φ : CNF) (numGates : Nat) (v : Nat) : Nat :=
  let nvars := φ.nvars
  let nclauses := φ.clauses.length
  let clause_start := 1 + nvars
  let clause_end := clause_start + nclauses
  let fg_start := clause_start  -- FG gates start at first clause
  let fg_end := min (fg_start + numGates) clause_end  -- Don't exceed clause range

  if (fg_start ≤ v) ∧ (v < fg_end)
  then (Nat.log 2 φ.nvars) ^ 2  -- QP-sharp FG gates at clauses
  else 0  -- Non-FG nodes: source, variables, non-FG clauses, reduction tree

/-! ## R Positivity Lemmas -/

/-- For nvars ≥ 4, log₂(nvars) ≥ 2, so (log₂ nvars)² ≥ 4 > 0. -/
lemma log_sq_pos_of_nvars_ge_4 (nvars : Nat) (h : nvars ≥ 4) : (Nat.log 2 nvars) ^ 2 > 0 := by
  have h_log_ge_2 : Nat.log 2 nvars ≥ 2 := by
    -- log₂ 4 = 2, and log is monotonic
    have h_log4 : Nat.log 2 4 = 2 := Nat.log_two_four_eq_two
    calc Nat.log 2 nvars ≥ Nat.log 2 4 := Nat.log_mono_right h
      _ = 2 := h_log4
  -- (log₂ nvars)² ≥ 2² = 4 > 0
  have h_sq_ge_4 : (Nat.log 2 nvars) ^ 2 ≥ 4 := by
    have h1 : (Nat.log 2 nvars) ^ 2 ≥ 2 ^ 2 := Nat.pow_le_pow_left h_log_ge_2 2
    simp only [Nat.pow_two] at h1 ⊢
    omega
  omega

/-- R_of returns positive value at FG gates when nvars ≥ 4.

    **Key lemma**: For planted instances with h_nvars : φ.nvars ≥ 4, FG gates have R > 0.
    This is crucial for proving totalRBits > 0. -/
theorem R_of_pos_at_fg_gate (φ : CNF) (numGates : Nat) (v : Nat)
    (h_nvars : φ.nvars ≥ 4)
    (h_fg : (1 + φ.nvars ≤ v) ∧ (v < min (1 + φ.nvars + numGates) (1 + φ.nvars + φ.clauses.length)))
    : R_of φ numGates v > 0 := by
  unfold R_of
  simp only [h_fg, ↓reduceIte]
  -- Goal: (Nat.log 2 φ.nvars) ^ 2 > 0
  exact log_sq_pos_of_nvars_ge_4 φ.nvars h_nvars

/-! ## Axiom Verification

This definition uses only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms R_of

end LStar.StructuralOWF.Foundations
