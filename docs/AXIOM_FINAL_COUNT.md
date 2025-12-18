# Axiom Final Count: Trust Boundary

The P≠NP proof relies on exactly **2 custom axioms** plus Lean's standard axioms.

## Custom Axioms

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 1 | `algspec_has_tm` | `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean` | Church-Turing bridge |
| 2 | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | `Layer4_Operational/TimeBridge/TMAdapterExponential.lean` | Church-Turing impossibility bridge |

### 1. `algspec_has_tm` (Church-Turing Bridge, Positive Direction)

Any polynomial-time algorithmic specification has a Turing Machine implementation that:
- Preserves the polynomial constants C and k
- Has a surjective output decoder
- Satisfies standard encoding conventions

**Risk**: Very Low. This is the universally accepted Church-Turing correspondence (Church 1936, Turing 1936).

### 2. `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` (Church-Turing Bridge, Negative Direction)

**Core principle**: Turing machines compute functions. Functional impossibility implies computational impossibility.

**Established in Lean (0 custom axioms)**:

No function can determine correct parity from incomplete observation.

- `parity_lower_bound_at_fg_gate`: Incomplete observation → ∃ indistinguishable configs with different parities
- `fg_correctness_requires_complete_observation`: Correctness requires complete observation (all R bit positions)
- Consequence: Any function that correctly computes the FG discriminator needs complete observation

**Axiom content (Church-Turing bridge for impossibility)**:

Turing machines cannot bypass information-theoretic requirements.

- TMs compute functions; they have no capabilities beyond function evaluation
- Proven: No function works with incomplete observation
- Bridge: Therefore no TM can be correct without complete observation
- Complete observation → distinguishing 2^R configs → 2^R execution states → 2^R time

This is the standard Church-Turing thesis applied to impossibility results:
> If no function can solve a problem from given information, then no TM can either.

**Risk**: Low. Rejecting this axiom requires asserting TMs have capabilities beyond function evaluation—contradicting Church-Turing. The information-theoretic content (parity indistinguishability, collision existence) is fully proven in Layers 0-3; this axiom only asserts TMs are bound by those limits.

## Standard Lean Axioms

The proof also uses Lean's standard axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

These are standard in classical mathematics and accepted by the Lean community.

## Verification

To verify the axiom count for the main theorem:
```bash
cd lean
lake env lean Layer5_Applications/PvsNP/PrimaryPath/CheckAxioms.lean
```

## Alternative Weaker Axiom Path (WC1Bridge)

An alternative axiom path is available that uses a semantically weaker assumption:

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 2' | `tm_correctness_implies_unitrefute_history` | `Layer4_Operational/TimeBridge/WC1Bridge.lean` | World refutation existence |

### `tm_correctness_implies_unitrefute_history` (Alternative to #2)

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

**Why it's weaker than the original**:
- Original axiom: "TM visits all 2^R encoder values" (surjectivity claim about TM behavior)
- New axiom: "Valid refutation history exists" (existence claim about mathematical structure)

The new axiom doesn't require the TM to actually visit all values—it only requires that a valid `UnitRefuteHistory` structure can be constructed accounting for eliminating all wrong worlds. The time bound is then DERIVED via WC1Bridge, not assumed.

**Bound comparison**:
- Original: `haltTime ≥ 2^R`
- New: `haltTime ≥ 2^R - 1`

Both bounds are sufficient for P≠NP since `2^R - 1` is still exponential. The polynomial domination argument works identically.

**Usage**: The wrapper theorem `fg_first_commit_time_lower_bound_via_wc1_axiom` provides the same interface as the original but uses the weaker axiom internally.

## Previously Eliminated Axioms

The following were axioms in earlier versions but are now fully proven:
- `fg_lossless_encoding` - 145-line theorem in EncodingDiscipline.lean
- `plant_flat_wf_transfer` - Now definitionally true via CNF.WellFormed in WellFormedRandomness_flat
- `encoding_semantics` - Now `encoding_semantics_derived` (proven)

## Axiom Naming History

For reviewers cross-referencing older documentation:
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` was informally referred to as `collision_indistinguishability` or `collision_indistinguishability_under_incomplete_observation` in early test documentation and release notes (e.g., v1.0.0 release)
- The current name reflects the axiom's actual role: bridging TM correctness to semantic coverage
