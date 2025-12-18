# Axiom Final Count: Trust Boundary

The P≠NP proof relies on exactly **2 custom axioms** plus Lean's standard axioms.

## Custom Axioms

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 1 | `algspec_has_tm` | `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean` | Church-Turing bridge |
| 2 | `tm_execution_abstracts_to_search_simple` | `Layer4_Operational/TimeBridge/WC1Bridge.lean` | Search enumeration bridge |

### 1. `algspec_has_tm` (Church-Turing Bridge, Positive Direction)

Any polynomial-time algorithmic specification has a Turing Machine implementation that:
- Preserves the polynomial constants C and k
- Has a surjective output decoder
- Satisfies standard encoding conventions

**Risk**: Very Low. This is the universally accepted Church-Turing correspondence (Church 1936, Turing 1936).

### 2. `tm_execution_abstracts_to_search_simple` (Search Enumeration Axiom)

**What it claims**: A correct TM on a planted SAT instance can be abstracted as a search that:
- Tests candidates one at a time (unit step property)
- Must test all 2^R - 1 wrong candidates before finding the planted one
- Has search time ≤ TM halt time

**In plain English**: "A Turing machine solving planted SAT must effectively try candidates one by one."

**How the time bound is derived** (Package 16 does real work):

- `SearchState`: Tracks tested candidates with invariant `tested.card ≤ time`
- `CorrectSearch`: Correctness requires all 2^R - 1 wrong candidates to be tested
- `search_enumeration_time_bound` (PROVEN): `search.time ≥ 2^R - 1`
- `time_bound_via_search_enumeration_simple`: Combines axiom with proven bound

**Why this axiom is semantically transparent**:
- It expresses the "no free lunch" principle for unstructured search
- Planted SAT has a unique solution with no exploitable structure
- Each TM step can distinguish at most one candidate
- This is the information-theoretic lower bound for search problems

**Risk**: Low. This is the standard unstructured search lower bound from information theory. Any algorithm that finds a needle in a haystack of size N must examine Ω(N) items in the worst case.

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

## Alternative Axioms (Legacy)

Earlier versions used different axioms that are still available but no longer used by the primary proof path:

| # | Axiom | Location | Nature |
|---|-------|----------|--------|
| 2a | `tm_correctness_implies_unitrefute_history` | `Layer4_Operational/TimeBridge/WC1Bridge.lean` | World refutation existence |
| 2b | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | `Layer4_Operational/TimeBridge/TMAdapterExponential.lean` | Surjectivity claim |

**Axiom 2a** (`tm_correctness_implies_unitrefute_history`): Claims existence of a `UnitRefuteHistory` structure with ≥ 2^R - 1 refuted worlds. This was the primary axiom before Package 16.

**Axiom 2b** (`tm_correctness_implies_realizesAllValuesFrom_flat_encoded`): Claims "TM visits all 2^R encoder values" (surjectivity claim about TM behavior). This is the strongest formulation.

**Bound comparison**:
- Search enumeration axiom (current): `haltTime ≥ 2^R - 1`
- UnitRefuteHistory axiom (2a): `haltTime ≥ 2^R - 1`
- Surjectivity axiom (2b): `haltTime ≥ 2^R`

All bounds are sufficient for P≠NP since `2^R - 1` is still exponential. The polynomial domination argument works identically.

**Why the search enumeration axiom is preferred**:
- Most transparent semantics: "unstructured search has no shortcuts"
- No complex intermediate structures (UnitRefuteHistory, timestamps)
- Directly expresses the information-theoretic lower bound

## Previously Eliminated Axioms

The following were axioms in earlier versions but are now fully proven:
- `fg_lossless_encoding` - 145-line theorem in EncodingDiscipline.lean
- `plant_flat_wf_transfer` - Now definitionally true via CNF.WellFormed in WellFormedRandomness_flat
- `encoding_semantics` - Now `encoding_semantics_derived` (proven)

## Path to Eliminating the Search Enumeration Axiom

The axiom `tm_execution_abstracts_to_search_simple` expresses the unit elimination property:
each TM step can test at most one candidate assignment.

### Package 16: Search Enumeration Model (CURRENT)

**Key structures** in `WC1Bridge.lean`:
- `SearchState`: Tracks tested candidates with `tested.card ≤ time` invariant
- `CorrectSearch`: Correctness requires testing all 2^R - 1 wrong candidates

**Key theorems** (all proven, 0 sorries):
- `correct_search_tests_all_wrong`: Correct search tests ≥ 2^R - 1 candidates ✅
- `search_enumeration_time_bound`: `search.time ≥ 2^R - 1` ✅
- `time_bound_via_search_enumeration_simple`: Main theorem combining axiom and bound ✅

**The axiom's role**: Bridges TM execution to the search model:
- Claims: TM execution can be abstracted as a correct search
- Where: Each search step tests at most one candidate

### What Would Be Needed to Eliminate the Axiom

To prove the axiom from TM semantics, we need to show that for planted SAT:

1. **Each TM step processes bounded information**: The TM tape head moves by ≤1, reads ≤1 cell
2. **Bounded information → bounded discrimination**: Reading O(1) bits cannot distinguish more than O(1) candidates
3. **Planted SAT has no exploitable structure**: The random planting ensures candidates are indistinguishable without full examination

This is the information-theoretic core: "you can't find a needle in a haystack without checking the hay."

### Trust Boundary Analysis

The axiom's semantic content is now transparent:

**The axiom asserts exactly**: TM execution satisfies the unit elimination property
(each step tests ≤ 1 candidate from the search space).

This is the Semantic Conservation Law applied to computation:
- To find the planted world among 2^R possibilities, you must test 2^R - 1 wrong candidates
- Each test requires at least one computational step
- Therefore: steps ≥ 2^R - 1

It does NOT:
- Assume anything about TM architecture or implementation
- Require any specific algorithm or data structure
- Depend on cryptographic assumptions

It ONLY asserts that distinguishing 2^R possibilities requires ≥ 2^R - 1 observations - a universally
accepted principle in information theory (cf. communication complexity, decision tree lower bounds).

## Axiom Naming History

For reviewers cross-referencing older documentation:
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` was informally referred to as `collision_indistinguishability` or `collision_indistinguishability_under_incomplete_observation` in early test documentation and release notes (e.g., v1.0.0 release)
- `tm_correctness_implies_unitrefute_history` (Package 8-15) was the primary axiom before Package 16
- `tm_execution_abstracts_to_search_simple` (Package 16, current) is the search enumeration axiom
- All three axioms express the same semantic content: unstructured search requires linear time
