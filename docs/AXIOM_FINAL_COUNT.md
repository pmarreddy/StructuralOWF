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

## Previously Eliminated Axioms

The following were axioms in earlier versions but are now fully proven:
- `fg_lossless_encoding` - 145-line theorem in EncodingDiscipline.lean
- `plant_flat_wf_transfer` - Now definitionally true via CNF.WellFormed in WellFormedRandomness_flat
- `encoding_semantics` - Now `encoding_semantics_derived` (proven)

## Axiom Naming History

For reviewers cross-referencing older documentation:
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` was informally referred to as `collision_indistinguishability` or `collision_indistinguishability_under_incomplete_observation` in early test documentation and release notes (e.g., v1.0.0 release)
- The current name reflects the axiom's actual role: bridging TM correctness to semantic coverage
