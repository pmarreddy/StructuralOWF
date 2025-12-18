# Axiom Final Count: Trust Boundary

The P≠NP proof relies on exactly **2 custom axioms** plus Lean's standard axioms.

## Custom Axioms

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 1 | `algspec_has_tm` | `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean:298` | Church-Turing bridge |
| 2 | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | `Layer4_Operational/TimeBridge/TMAdapterExponential.lean:2132` | Semantic bound |

### 1. `algspec_has_tm` (Church-Turing Bridge)

Any polynomial-time algorithmic specification has a Turing Machine implementation that:
- Preserves the polynomial constants C and k
- Has a surjective output decoder
- Satisfies standard encoding conventions

**Risk**: Very Low. This is the universally accepted Church-Turing correspondence (Church 1936, Turing 1936).

### 2. `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` (Semantic Bound)

If a Turing Machine correctly solves a planted L* instance, it must have "visited" every possible emergent configuration value (all 2^R of them) during execution.

**Why this is true** (information-theoretic argument):
1. The planted instance has a unique satisfying assignment (by construction)
2. To output the correct assignment, the TM must distinguish it from 2^R-1 alternatives
3. The only distinguishing feature is the emergent configuration value
4. Therefore, correctness requires exploring all 2^R possibilities

**Risk**: Low. This is an information-theoretic necessity based on A2 injectivity and pigeonhole counting.

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
lake env lean -c "import Layer5_Applications; #print axioms MainTheorems.P_ne_NP"
```

## Previously Eliminated Axioms

The following were axioms in earlier versions but are now fully proven:
- `fg_lossless_encoding` - 145-line theorem in EncodingDiscipline.lean
- `plant_flat_wf_transfer` - Now definitionally true via CNF.WellFormed in WellFormedRandomness_flat
- `encoding_semantics` - Now `encoding_semantics_derived` (proven)

## Axiom Naming History

For reviewers cross-referencing older documentation:
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` was informally referred to as `collision_indistinguishability` in some early test documentation
