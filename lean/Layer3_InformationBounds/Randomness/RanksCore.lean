import Layer0_Foundations.Base.CNF

/-! ## RanksCore: Core Rank Function Infrastructure

**Main Definitions**:
- `EmergenceProfile` - Enum for profile selection (`.exponential` only)
- `computeR` - Profile-parametric R computation at FG gates

**Why extracted**: Breaks circular dependencies (PlantCore ↔ Foundations). Pure rank computation
used by Plant.lean, SeedSemantics.lean, EmergentConfig.lean.

**FG Placement**: Gates at clause layer (positions [clause_start, clause_start + numGates)).
- FG gates: R_v > 0 (emergence requirement)
- Non-FG nodes: R_v = 0 (sources, variables, non-FG clauses, reduction tree)

**Trust Boundary**: Axiom-free (pure function definitions).

**Used by**: PlantCore.lean, SeedSemantics.lean, RanksExponential.lean

**Note**: The exponential profile (R = n) is the only active profile. The full
R_of_flat function is in RanksExponential.lean and is used throughout the P≠NP proof.
-/

namespace LStar.StructuralOWF.Foundations

/-! ## Emergence Profile

The emergence profile determines how R (emergence rank) is computed at FG gates.
This affects both the hardness bound and the digest size.

- **Exponential**: R = n, giving 2^R = 2^n hardness (ACTIVE profile for P≠NP)

The profile is used throughout the codebase to ensure consistent R computation
in planting, decoding, and verification. -/

/-- Emergence profile for FG gates.

    Determines how R (emergence rank) is computed:
    - `exponential`: R = nvars - exponential hardness (ACTIVE profile for P≠NP)

    **Usage**: Pass to `computeR` to get profile-specific R value. -/
inductive EmergenceProfile
  | exponential -- R = n, bound = 2^n [ACTIVE]
  deriving DecidableEq, Repr

/-- Compute R (emergence rank) for a given profile and nvars.

    This is the **single source of truth** for R computation at FG gates.
    All code that needs R at FG gates should use this function.

    **Exponential Profile**: R = nvars
    - Gives exponential hardness: 2^R = 2^nvars
    - Used in P≠NP proof

    **Note**: For non-FG vertices, R = 0 regardless of profile. This function
    computes R for FG gates only; use `R_of_flat` for full DAG computation. -/
def computeR (profile : EmergenceProfile) (nvars : Nat) : Nat :=
  match profile with
  | .exponential => nvars

/-- Exponential profile gives n (the active profile used in P≠NP proof). -/
theorem computeR_exponential (nvars : Nat) : computeR .exponential nvars = nvars := rfl

#print axioms computeR

end LStar.StructuralOWF.Foundations
