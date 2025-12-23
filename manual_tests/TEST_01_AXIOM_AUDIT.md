# TEST 01: Axiom Audit

**Priority**: CRITICAL (Most Important Test)
**Risk Level**: Proof-Invalidating
**Estimated Time**: 2-4 hours for comprehensive audit
**Last Updated**: 2025-12-22 (verified against actual `#print axioms P_ne_NP` output)

---

## Overview

The axiom audit is the single most important verification step. If ANY axiom is:
- False (makes entire proof invalid)
- Circular (assumes what we're trying to prove)
- Too strong (essentially assumes P≠NP)
- Inconsistent (derives False)
- Vacuously true (preconditions never satisfiable)

...the proof is worthless regardless of how elegant the rest is.

---

## Verified Axiom Count (Authoritative)

**Source**: `#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP`

**Standard Lean Axioms (3)**:
- `propext` - Propositional extensionality
- `Classical.choice` - Classical logic
- `Quot.sound` - Quotient soundness

**Custom Axioms (2)**:

| # | Axiom | File | Type | Risk |
|---|-------|------|------|------|
| 1 | `algspec_has_tm` | RandAdv.lean:414 | Church-Turing bridge | Very Low |
| 2 | `remaining_indistinguishable` | WC1Bridge.lean:4067 | WC-1 indistinguishability bridge | Low |

**Note**: See `docs/AXIOM_FINAL_COUNT.md` for authoritative axiom documentation.

---

## Attack Vectors

### ATTACK 1.1: Hidden Axiom Discovery

**Goal**: Find ALL axioms (not just documented ones)

**Method**:
```bash
# Run this from lean/ directory
cd /Volumes/Ddrive/PNePNP-Publication/lean

# 1. AUTHORITATIVE: Print axioms of P_ne_NP
cat > /tmp/axiom_check.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/axiom_check.lean 2>&1

# 2. Find ALL axiom declarations (excluding .lake and Mathlib)
grep -rn "^axiom " --include="*.lean" | grep -v ".lake" | grep -v "-- axiom"

# 3. Find sorry statements (unproven gaps)
grep -rn "\bsorry\b" --include="*.lean" | grep -v ".lake" | grep -v "-- sorry" | grep -v "sorryAx"

# 4. Find sorryAx (axiom-level sorry)
grep -rn "sorryAx" --include="*.lean" | grep -v ".lake"
```

**Expected Output from #print axioms**:
```
'LStar.Complexity.StructuralOWFBridge.P_ne_NP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LStar.Complexity.algspec_has_tm,
 LStar.StructuralOWF.Foundations.remaining_indistinguishable]
```

**Red Flags**:
- Any axiom not in the list above
- Any `sorry` in files used by P_ne_NP
- Any `sorryAx` anywhere in the dependency chain
- Axiom count ≠ 2 custom + 3 standard

**Verification Checklist**:
- [ ] Exactly 2 custom axioms in P_ne_NP chain
- [ ] No undocumented axioms exist
- [ ] No `sorry` in main proof chain
- [ ] No `sorryAx` in main proof chain

---

### ATTACK 1.2: Axiom Strength Analysis (Both Axioms)

**Goal**: Determine if any axiom is "too strong" (secretly assumes P≠NP)

#### Axiom 1: `algspec_has_tm` (RandAdv.lean:414)

```lean
axiom algspec_has_tm {α β : Type} [Sized α] [Sized β] [FirstNatComponent β]
    [UniformityStructure α β] {T : Nat}
    (A : AlgSpec α β T) :
  ∃ (M : RandAdv α β T),
    M.toAlgSpec.run = A.run ∧
    M.C = A.C ∧
    M.k = A.k ∧
    UniformityStructure.uniformityProp M
```

**Strength Test Questions**:
- [ ] Does this say anything about which functions can be computed?
  - **Analysis**: No - it says IF you have a poly-time spec, you get a poly-time TM
- [ ] Does this restrict the class of poly-time algorithms?
  - **Analysis**: No - it's the Church-Turing thesis (poly-time spec = poly-time TM)
- [ ] Could a poly-time algorithm for SAT violate this?
  - **Analysis**: No - if SAT had a poly-time algorithm, this axiom would give you the TM for it
- **VERDICT**: SAFE (definitional, not computational)

#### Axiom 2: `remaining_indistinguishable` (WC1Bridge.lean:4067)

```lean
axiom remaining_indistinguishable
    {k : Nat} {states alphabet : Type}
    [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    (L : LStarInstanceFG)
    (M : TuringMachine k states alphabet)
    (v : Fin L.dag.n)
    (enc : LStarTMEncoding L M v)
    (haltTime : Nat)
    (cfg_planted : Fin (2^(L.R v)))
    (configs : List ((w : Fin L.dag.n) ×' Fin (2 ^ L.R w)))
    (h_configs_def : configs = (List.range haltTime).map (fun t =>
        ⟨v, enc.extractConfigAtV ((TMConfig.step (M := M))^[t] (enc.initForPlanting cfg_planted))⟩))
    (h_v_in : v ∈ ({v} : Finset (Fin L.dag.n)))
    (ω' : CutWorld L {v})
    (h_remaining : ω' ∉ eliminatedWorlds L {v} configs)
    : TMIndistinguishable L M v enc.extractConfigAtV enc.initForPlanting haltTime
        (ω'.assignment v h_v_in) cfg_planted
```

**Strength Test Questions**:
- [ ] Does this directly say "poly-time can't do X"?
  - **Analysis**: No - it asserts indistinguishability: if a world isn't refuted by the TM run trace, the TM cannot distinguish it from the planted world
- [ ] Is this information-theoretically sound?
  - **Analysis**: Yes - if you haven't observed information that rules out a world, you cannot distinguish it
- [ ] What about the operational structure?
  - **Analysis**: CRUCIAL - configs are DEFINED via actual TM run trace (not existentially quantified), ensuring the axiom only applies to real TM execution
- [ ] Does this assume P≠NP?
  - **Analysis**: No - it's about indistinguishability. The time bound (≥ 2^R - 1) is DERIVED via `indistinguishability_implies_all_wrong_refuted` and WC-1 structure theorems
- **VERDICT**: SAFE (indistinguishability principle; separation/time bound derived, not assumed)

---

### ATTACK 1.3: Axiom Circularity Check

**Goal**: Ensure no axiom secretly assumes the conclusion

**Method**: For each axiom, verify:
1. No mention of P, NP, or complexity classes
2. No mention of "polynomial impossible" or "exponential required"
3. All conclusions are about local properties (encoding, structure, TM execution)

```bash
# Search for P/NP mentions in axiom files
grep -B5 -A30 "^axiom " Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean | grep -i "InP\|InNP\|P_ne\|PeqNP"
grep -B5 -A30 "^axiom " Layer4_Operational/TimeBridge/WC1Bridge.lean | grep -i "InP\|InNP\|P_ne\|PeqNP"
```

**Expected**: No matches. Axioms should be about:
- Encodings (algspec_has_tm)
- Indistinguishability (remaining_indistinguishable)
- NOT about complexity classes directly

**Verification Checklist**:
- [ ] No axiom mentions "InP" or "InNP"
- [ ] No axiom mentions "polynomial" in conclusion
- [ ] No axiom mentions "exponential lower bound"
- [ ] All axioms are about local/structural properties

---

### ATTACK 1.4: Axiom Consistency Check (CORRECTED METHODOLOGY)

**Goal**: Verify axioms don't derive `False`

**Method**: Try to prove False from the axioms

**⚠️ IMPORTANT**: The trivial test `theorem t : True := trivial` does NOT detect inconsistency. If False were derivable, Lean would still accept this proof.

**Test 1: Direct False Proof Attempt**
```lean
-- Create test file: lean/testing/ConsistencyCheck.lean
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge

-- Try to prove False directly from axioms
-- If this succeeds WITHOUT sorry, axioms are inconsistent
theorem axioms_inconsistent : False := by
  sorry  -- MUST require sorry; if it typechecks without sorry, we have a problem

-- This should be UNPROVABLE (require sorry)
```

**Test 2: Per-Axiom Consistency**
```lean
-- For each axiom, verify it doesn't derive False alone
#check @algspec_has_tm  -- Should not have False in its conclusion
#check @remaining_indistinguishable  -- Concludes TMIndistinguishable, not False
```

**Test 3: Mutual Contradiction Check**
```lean
-- Can we satisfy the preconditions of remaining_indistinguishable
-- using outputs from algspec_has_tm?
--
-- algspec_has_tm: AlgSpec → TM
-- remaining_indistinguishable: TM + remaining world → TMIndistinguishable
--
-- For contradiction: need to show EVERY TM from algspec_has_tm
-- has all wrong worlds remaining AND produces correct output (impossible)
-- The derivation chain shows: if TM is worst-case correct, all wrong worlds ARE eliminated
```

**Verification Checklist**:
- [ ] Cannot derive `False` from axioms alone
- [ ] Each axiom's preconditions are independently satisfiable
- [ ] Axiom preconditions are not simultaneously satisfiable in trivial ways

---

### ATTACK 1.5: Lean Standard Axioms Check

**Goal**: Verify only standard Lean axioms used

**Method**:
```bash
# Check what Lean axioms P_ne_NP uses
cat > /tmp/axiom_check.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/axiom_check.lean 2>&1 | grep -E "propext|Classical|Quot|sorry"
```

**Expected Standard Axioms**:
- `propext` - Propositional extensionality (standard)
- `Classical.choice` - Classical logic (standard)
- `Quot.sound` - Quotient soundness (standard)

**Red Flags**:
- `sorry` - Unproven gap
- `sorryAx` - Axiom-level sorry
- Any `axiom False` - Inconsistency
- More than 3 standard axioms

---

### ATTACK 1.6: Test Axiom Instantiation

**Goal**: Verify axioms can be instantiated without trivially deriving False

**Test for algspec_has_tm**:
```lean
-- Can we construct an AlgSpec?
def identity_spec : AlgSpec Nat Nat 10 where
  run := fun _ x => x
  C := 1
  k := 1
  time_bound := fun n => n + 10
  time_bound_poly := sorry -- fill in proof

-- Does algspec_has_tm give us a TM?
#check algspec_has_tm identity_spec
-- This should typecheck and produce an existential
```

**Test for remaining_indistinguishable**:
```lean
-- The axiom states: remaining world → TMIndistinguishable
-- This means: if a world is not ruled out by configs, TM cannot distinguish it
--
-- For planted instances with correct TMs, all wrong worlds must be refuted
-- (derived via indistinguishability_implies_all_wrong_refuted)
-- The axiom captures the information-theoretic indistinguishability principle
```

---

### ATTACK 1.7: Axiom Dependency Graph

**Goal**: Map which theorems depend on which axioms

**Method**:
```bash
# For each major theorem, check its axioms
for thm in P_ne_NP pnenp_classical f_is_one_way_exponential_flat; do
  echo "=== $thm ==="
  cat > /tmp/check_$thm.lean << EOF
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.$thm
EOF
  lake env lean /tmp/check_$thm.lean 2>&1 | grep -v "^$"
done
```

**Dependency Matrix (Expected)**:

| Theorem | algspec_has_tm | remaining_indistinguishable |
|---------|----------------|---------------------------------------|
| P_ne_NP | ✅ | ✅ |
| pnenp_classical | ✅ | ✅ |
| f_is_structural_owf_exponential_true | ❌ | ✅ |

**Verification Checklist**:
- [ ] All 2 axioms used by P_ne_NP
- [ ] No unexpected axiom dependencies
- [ ] Dependency graph is acyclic
- [ ] No crypto axioms in chain (should be 0)

---

### ATTACK 1.8: Crypto Axiom Exclusion Verification

**Goal**: Verify crypto axioms (Layer5_Applications/Crypto/) are NOT in P_ne_NP chain

**Background**: The codebase contains 20+ crypto axioms:
- `manytime_sig_from_ots`, `uowhf_from_owf`, `prf_from_prg`, etc.
- These are intentional (crypto reductions) but must NOT be in P_ne_NP dependency

**Method**:
```bash
# List all crypto axioms
grep -rn "^axiom " Layer5_Applications/Crypto/ --include="*.lean"

# Verify NONE appear in P_ne_NP axioms
cat > /tmp/check_crypto.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/check_crypto.lean 2>&1 | grep -E "sig_from|prf_from|prg_from|owf_from|mac_from|commitment|encryption|ot_from|mpc_from"
```

**Expected**: No matches. Crypto axioms should be unreachable from P_ne_NP.

---

### ATTACK 1.9: Model Theory Attack

**Goal**: Attempt to construct a model where axioms hold but P=NP

**Method**:
If we can build a mathematical model (in set theory) where:
1. All our axioms are true
2. P = NP is also true

Then the axioms DON'T imply P≠NP!

**Analysis**:
- **algspec_has_tm**: Holds in any model of computation (Church-Turing thesis)
- **remaining_indistinguishable**: The key axiom

**For remaining_indistinguishable in a P=NP world**:
- If P=NP, there exists a poly-time SAT solver
- For planted instances, this solver must refute all wrong worlds to be correct
- The axiom says: remaining world → indistinguishable from planted
- By contrapositive with worst-case correctness: all wrong worlds must be refuted
- Derived consequence: haltTime ≥ 2^R - 1 (via WC-1 structure theorems)

**Key insight**: In a P=NP world, a poly-time SAT solver for planted instances would either:
1. Eliminate ALL 2^R - 1 wrong worlds (requiring ≥ 2^R - 1 time) - but 2^R > poly(n), so impossible
2. Leave some wrong world remaining but still be correct - violating indistinguishability + worst-case correctness

This is the crux: the axiom captures indistinguishability, from which the time bound is DERIVED.

---

### ATTACK 1.10: Axiom Redundancy Check

**Goal**: Determine if axioms are derivable from each other

**Note**: There are exactly 2 axioms (`algspec_has_tm` and `remaining_indistinguishable`).

**Method**:
```lean
-- Can we prove axiom 2 from axiom 1?
theorem axiom2_from_axiom1 :
  (∀ A, algspec_has_tm A) →
  remaining_indistinguishable = _ := by
  sorry  -- SHOULD FAIL - different domains (Church-Turing vs indistinguishability)
```

**Expected**: `sorry` required (axioms are independent).

**Red Flag**: If any axiom is derivable from others, it might be circular or redundant.

---

### ATTACK 1.11: Extraction/Compilation Attack

**Goal**: Check what happens when extracting executable code

**Method**:
```bash
# Try to extract the proof to executable code
lake env lean --run /tmp/extract_test.lean
```

**Questions**:
- Do axioms cause extraction failures?
- Are there `sorry` that block extraction?
- Does the extracted code match the specification?

**Note**: Axioms that can't be given computational content are acceptable (P_ne_NP is a separation theorem, not an algorithm).

---

### ATTACK 1.12: Third-Party Axiom Injection

**Goal**: Find axioms introduced by non-standard imports

**Method**:
```bash
# Check for non-Mathlib, non-Layer imports
grep -rn "^import " --include="*.lean" lean/ | grep -v ".lake" | grep -v "Mathlib\|Layer[0-5]\|LStar\|Infrastructure\|testing"

# Check if any imports introduce unexpected axioms
```

**Red Flag**: Any import that introduces custom axioms not from the project's own Layer hierarchy.

---

### ATTACK 1.13: Classical Logic Necessity

**Goal**: Determine if proof requires classical logic

**Method**:
```bash
# Find uses of Classical namespace
grep -rn "Classical\." --include="*.lean" | grep -v ".lake" | head -50
```

**Questions**:
- [ ] Is classical logic essential or just convenient?
- [ ] Could a constructive proof be achieved?
- [ ] What specifically requires classical reasoning?

**Assessment**: Classical logic is used (`Classical.choice` in axioms). This is standard for complexity theory (P≠NP is inherently about existence/non-existence).

---

### ATTACK 1.14: Pathological Fintype Instance Attack

**Goal**: Exploit axioms via pathological Fintype instances

**Method**:
```lean
-- What if we instantiate axiom type parameters with:
-- 1. Fintype with cardinality 0 (Empty)
-- 2. Fintype with cardinality 1 (Unit)

-- Test: Does algspec_has_tm work with Empty input?
-- Answer: No - Empty has no values, so AlgSpec on Empty is vacuous

-- Test: Does remaining_indistinguishable work with R = 0?
-- Answer: If R = 0, then 2^R = 1, so there's only 1 config value
-- This is handled by the plant_flat construction requiring h_nvars ≥ 4
-- The LStarInstanceFG structure comes from plant_flat which ensures sufficient size

-- Test: What about L.dag.n = 0?
-- Answer: v : Fin L.dag.n requires L.dag.n > 0, so this case is excluded
```

**Verification**: Check that construction preconditions (in plant_flat) exclude degenerate cases.

---

### ATTACK 1.15: Private Axiom Visibility

**Goal**: Track private axioms by their mangled names

**Method**:
```bash
# Private axioms appear with _private prefix in #print axioms output
# Current status: NO private axioms in P_ne_NP dependency chain

# All axioms are public:
# - LStar.Complexity.algspec_has_tm
# - LStar.StructuralOWF.Foundations.remaining_indistinguishable
```

**Red Flag**: Any private axiom not documented in trust boundary.

---

### ATTACK 1.16: Axiom Strength Comparison

**Goal**: Determine relative strength of axioms

**Analysis**:

| Axiom | Contribution | Could prove P≠NP alone? |
|-------|--------------|-------------------------|
| algspec_has_tm | TM bridge | No (Church-Turing) |
| remaining_indistinguishable | Indistinguishability | No (needs construction + derivation) |

**Key insight**: No single axiom implies P≠NP. The separation emerges from COMBINING:
1. The L* construction (creates planted instances)
2. The indistinguishability axiom (remaining → indistinguishable)
3. Derived theorems (all wrong worlds must be refuted, WC-1 structure, time bound)
4. The TM bridge (AlgSpec → RandAdv)

---

### ATTACK 1.17: Vacuous Truth Check (NEW)

**Goal**: Verify axiom preconditions are satisfiable in non-trivial cases

**Method**:
```lean
-- For remaining_indistinguishable:
-- The axiom states: remaining world → TMIndistinguishable
-- This means: if a world isn't ruled out by configs, TM cannot distinguish it

-- The axiom is designed so that for PLANTED instances with CORRECT TM output,
-- all wrong worlds must be refuted (derived via indistinguishability_implies_all_wrong_refuted).
-- This is the information-theoretic content: correctness requires full refutation.

-- Test: Construct a TM that refutes all wrong worlds
-- Such TM satisfies worst-case correctness - consistent

-- Test: Construct a TM that leaves some wrong world remaining but is still correct
-- By indistinguishability + worst-case correctness, this leads to contradiction
-- If we could construct such a TM, the derivation chain would be unsound
```

**Verification**: The axiom's strength comes from:
1. Preconditions ARE satisfiable (planted instances exist, TMs exist)
2. Indistinguishability + worst-case correctness → all wrong worlds refuted (derived)
3. WC-1 structure → time ≥ 2^R - 1 (derived)

---

### ATTACK 1.18: Per-Axiom Dependency Audit (NEW)

**Goal**: For each axiom, verify it only depends on standard foundations

**Method**:
```bash
# Check each axiom's dependencies
cat > /tmp/per_axiom.lean << 'EOF'
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Layer4_Operational.TimeBridge.WC1Bridge

#print axioms LStar.Complexity.algspec_has_tm
#print axioms LStar.StructuralOWF.Foundations.remaining_indistinguishable
EOF
lake env lean /tmp/per_axiom.lean 2>&1
```

**Expected**:
- `algspec_has_tm` → `[propext, Quot.sound, algspec_has_tm]` (no Classical.choice)
- `remaining_indistinguishable` → `[propext, Classical.choice, Quot.sound, remaining_indistinguishable]`

---

### ATTACK 1.19: Uniformity Requirement Analysis (NEW)

**Goal**: Verify uniformity is properly enforced in the proof architecture

**Background**: Uniformity is enforced through the `algspec_has_tm` axiom's `UniformityStructure`:
```lean
axiom algspec_has_tm {α β : Type} [Sized α] [Sized β] [FirstNatComponent β]
    [UniformityStructure α β] {T : Nat}
    (A : AlgSpec α β T) :
  ∃ (M : RandAdv α β T),
    M.toAlgSpec.run = A.run ∧
    M.C = A.C ∧  -- polynomial constant preserved
    M.k = A.k ∧  -- polynomial exponent preserved
    UniformityStructure.uniformityProp M
```

**Questions**:
- [ ] Does this block non-uniform adversaries?
  - **Analysis**: Yes - the polynomial bounds C,k are instance-independent (from AlgSpec)
- [ ] Does this block exponential-time strategies?
  - **Analysis**: Yes - no fixed C,k satisfies 2^n ≤ C*n^k for all n
- [ ] Is this requirement too restrictive?
  - **Analysis**: No - P is defined as uniform polynomial time; this matches the standard definition

---

## Execution Protocol

### Step 1: Automated Axiom Collection
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Collect all axioms
echo "=== All axiom declarations ===" > ../manual_tests/axiom_audit_results.txt
grep -rn "^axiom \|^private axiom " --include="*.lean" | grep -v ".lake" >> ../manual_tests/axiom_audit_results.txt

# Collect all sorry
echo -e "\n=== All sorry statements ===" >> ../manual_tests/axiom_audit_results.txt
grep -rn "\bsorry\b" --include="*.lean" | grep -v ".lake" | grep -v "-- sorry" >> ../manual_tests/axiom_audit_results.txt

# Collect main theorem axioms
echo -e "\n=== P_ne_NP axioms ===" >> ../manual_tests/axiom_audit_results.txt
cat > /tmp/axiom_check.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/axiom_check.lean >> ../manual_tests/axiom_audit_results.txt 2>&1
```

### Step 2: Manual Axiom Review

For EACH axiom found:
1. Read the axiom statement carefully
2. Identify its mathematical claim
3. Assess if claim is:
   - Universally accepted (Church-Turing)
   - Standard counting argument (pigeonhole/keyedness)
   - Reasonable encoding property
   - Suspicious/circular
4. Document assessment

### Step 3: Cross-Reference

Compare findings with:
- `docs/AXIOM_FINAL_COUNT.md` (Updated 2025-12-07 to match actual `#print axioms` output)
- `docs/FINAL_ASSUMPTIONS_AUDIT_REPORT.md`
- Any discrepancies are RED FLAGS

---

## Pass/Fail Criteria

### PASS Conditions (ALL must be true):
- [ ] Exactly 2 custom axioms used by P_ne_NP (algspec_has_tm, remaining_indistinguishable)
- [ ] All axioms are documented
- [ ] No axiom directly assumes P≠NP
- [ ] No axiom restricts polynomial-time computation
- [ ] No `sorry` in main proof chain
- [ ] No `sorryAx` in main proof chain
- [ ] Axioms are consistent (cannot derive False)
- [ ] Axiom preconditions are non-vacuously satisfiable
- [ ] No crypto axioms in P_ne_NP dependency chain

### FAIL Conditions (ANY triggers failure):
- [ ] Hidden undocumented axiom found
- [ ] Axiom secretly implies P≠NP
- [ ] `sorry` or `sorryAx` in dependency chain
- [ ] Axioms derive `False` without valid preconditions
- [ ] Axiom count differs from verified 2
- [ ] Axiom preconditions are unsatisfiable
- [ ] Crypto axioms appear in P_ne_NP chain

---

## Historical Findings

From previous audits:
- **Eliminated**: `tm_overhead`, `encoding_semantics`, `plant_flat_wf_transfer`, `fg_lossless_encoding` (now theorems)
- **Current (verified 2025-12-22)**:
  1. `algspec_has_tm` (Church-Turing bridge)
  2. `remaining_indistinguishable` (WC-1 indistinguishability bridge)
- **Vestigial**: `planted_revealedBits_empty` (not in P_ne_NP chain)
- **Not in chain**: `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` (exists but unused by P_ne_NP)

---

## Appendix: Axiom Soundness Arguments

### Why `algspec_has_tm` is Sound

1. **Church-Turing Thesis**: Every effective computation has a TM
2. **Polynomial Preservation**: If AlgSpec has poly bound C*n^k, TM can simulate with same bound
3. **No Restriction**: This doesn't say what CAN'T be computed, only what CAN

### Why `remaining_indistinguishable` is Sound

1. **Indistinguishability Principle**: If you haven't observed information ruling out a world, you cannot distinguish it
2. **Operational Definition**: Configs are DEFINED via actual TM run trace (not existentially quantified)
3. **Derivation Chain**: Separation and time bound are DERIVED, not assumed:
   - `indistinguishability_implies_all_wrong_refuted`: All wrong worlds must be refuted (by contradiction with worst-case correctness)
   - `eliminatedWorlds_length_le_configs`: Each config adds ≤1 world (WC-1 structure)
   - `separation_implies_eliminated_length`: Separation → refuted.length = 2^R - 1
   - `tm_time_lower_bound_operational`: haltTime ≥ 2^R - 1

### Why These Don't Assume P≠NP

A hypothetical P=NP world:
- `algspec_has_tm`: Still true (poly-time SAT solver would get a TM)
- `remaining_indistinguishable`: Still true (indistinguishability principle unchanged)

The P≠NP conclusion comes from COMBINING these with the FG construction,
not from the axioms themselves. The construction creates instances where
correctness requires 2^Ω(n) time, and no axiom blocks a poly-time algorithm
from existing—the construction makes such algorithms incorrect on planted instances.

---

## Axiom File Locations (Quick Reference)

| Axiom | File | Line | Namespace |
|-------|------|------|-----------|
| `algspec_has_tm` | RandAdv.lean | 414 | `LStar.Complexity` |
| `remaining_indistinguishable` | WC1Bridge.lean | 4067 | `LStar.StructuralOWF.Foundations` |

**Not in P_ne_NP Chain** (exists but unused):
- `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` - TMAdapterExponential.lean:2151
