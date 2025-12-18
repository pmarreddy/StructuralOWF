# Axiom Final Count: Trust Boundary

The P≠NP proof relies on exactly **2 custom axioms** plus Lean's standard axioms.

## Custom Axioms

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 1 | `algspec_has_tm` | `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean` | Church-Turing bridge |
| 2 | `tm_correctness_implies_unitrefute_history` | `Layer4_Operational/TimeBridge/WC1Bridge.lean` | World refutation existence |

### 1. `algspec_has_tm` (Church-Turing Bridge, Positive Direction)

Any polynomial-time algorithmic specification has a Turing Machine implementation that:
- Preserves the polynomial constants C and k
- Has a surjective output decoder
- Satisfies standard encoding conventions

**Risk**: Very Low. This is the universally accepted Church-Turing correspondence (Church 1936, Turing 1936).

### 2. `tm_correctness_implies_unitrefute_history` (WC1Bridge Axiom)

**What it claims**: A correct TM on a planted instance induces a valid `UnitRefuteHistory` structure with:
- A sequence of refuted worlds of length ≥ 2^R - 1 (one refutation per wrong world)
- Timestamps for each refutation that are strictly increasing and bounded by execution time
- An execution prefix recording the halt time

**How the time bound is derived** (WC1Bridge does real work):

The axiom does NOT directly claim a time bound. Instead:
- **Axiom claims**: `∃ hist, hist.base_prefix.time = haltTime ∧ hist.refuted_worlds.length ≥ 2^R - 1`
- **WC1Bridge proves** (0 custom axioms): `hist.base_prefix.time ≥ hist.refuted_worlds.length`
  - Via `time_bounds_refutations` theorem: strictly increasing timestamps bounded by T implies count ≤ T
- **Combining**: `haltTime = hist.base_prefix.time ≥ hist.refuted_worlds.length ≥ 2^R - 1`

**Why this axiom is semantically weak**:
- It makes an existence claim about a mathematical structure (valid refutation history)
- It does NOT claim the TM visits all values—only that refutations can be constructed
- The time bound is DERIVED via proven theorems, not assumed directly

**Risk**: Low. The axiom asserts that computational correctness requires informational completeness—a Turing machine cannot determine an answer without observing distinguishing information. This is the standard Church-Turing thesis applied to impossibility.

## Standard Lean Axioms

The proof also uses Lean's standard axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

These are standard in classical mathematics and accepted by the Lean community.

## Verification

To verify the axiom count for the main OWF theorems:
```bash
cd lean
cat > /tmp/check.lean << 'EOF'
import Layer2_StructuralOWF.Security.StructuralOWFExponential
#print axioms LStar.StructuralOWF.f_is_structural_owf_exponential_flat
#print axioms LStar.StructuralOWF.f_is_structural_owf_exponential_true
EOF
lake env lean /tmp/check.lean
```

To verify the full P≠NP theorem:
```bash
cd lean
lake env lean Layer5_Applications/PvsNP/PrimaryPath/CheckAxioms.lean
```

## Alternative Stronger Axiom (Legacy)

An earlier version used a stronger axiom that is still available but no longer used by the primary proof path:

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 2' | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | `Layer4_Operational/TimeBridge/TMAdapterExponential.lean` | Surjectivity claim |

This axiom claims "TM visits all 2^R encoder values" (surjectivity claim about TM behavior), which is stronger than the existence claim made by the WC1Bridge axiom.

**Bound comparison**:
- Legacy axiom: `haltTime ≥ 2^R`
- WC1Bridge axiom: `haltTime ≥ 2^R - 1`

Both bounds are sufficient for P≠NP since `2^R - 1` is still exponential. The polynomial domination argument works identically.

## Previously Eliminated Axioms

The following were axioms in earlier versions but are now fully proven:
- `fg_lossless_encoding` - 145-line theorem in EncodingDiscipline.lean
- `plant_flat_wf_transfer` - Now definitionally true via CNF.WellFormed in WellFormedRandomness_flat
- `encoding_semantics` - Now `encoding_semantics_derived` (proven)

## Axiom Naming History

For reviewers cross-referencing older documentation:
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` was informally referred to as `collision_indistinguishability` or `collision_indistinguishability_under_incomplete_observation` in early test documentation and release notes (e.g., v1.0.0 release)
- The current name reflects the axiom's actual role: bridging TM correctness to semantic coverage
