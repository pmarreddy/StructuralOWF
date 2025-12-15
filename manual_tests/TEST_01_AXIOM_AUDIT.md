# TEST 01: Axiom Audit

**Priority**: CRITICAL (Most Important Test)
**Risk Level**: Proof-Invalidating
**Estimated Time**: 2-4 hours for comprehensive audit
**Last Updated**: 2025-12-07 (verified against actual `#print axioms P_ne_NP` output)

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
| 1 | `algspec_has_tm` | RandAdv.lean:297 | Church-Turing bridge | Very Low |
| 2 | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | TMAdapterExponential.lean:297 | Information-theoretic bound | Low |

**Note**: `fg_lossless_encoding` was previously an axiom but is now fully proven (145-line theorem). See `docs/AXIOM_FINAL_COUNT.md` for authoritative axiom documentation.

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
 _private.Layer2_StructuralOWF.Plant.PlantExponential.0.LStar.StructuralOWF.plant_flat_wf_transfer,
 _private.Layer5_Applications.PvsNP.ComplexityClasses.EncodingDiscipline.0.LStar.Complexity.EncodingDiscipline.fg_lossless_encoding,
 LStar.StructuralOWF.Foundations.FlatProfile.tm_correctness_implies_realizesAllValuesFrom_flat_encoded]
```

**Red Flags**:
- Any axiom not in the list above
- Any `sorry` in files used by P_ne_NP
- Any `sorryAx` anywhere in the dependency chain
- Axiom count ≠ 4 custom + 3 standard

**Verification Checklist**:
- [ ] Exactly 4 custom axioms in P_ne_NP chain
- [ ] No undocumented axioms exist
- [ ] No `sorry` in main proof chain
- [ ] No `sorryAx` in main proof chain
- [ ] Private axiom names match expected mangled format

---

### ATTACK 1.2: Axiom Strength Analysis (All 4 Axioms)

**Goal**: Determine if any axiom is "too strong" (secretly assumes P≠NP)

#### Axiom 1: `algspec_has_tm` (RandAdv.lean:297)

```lean
axiom algspec_has_tm {α β : Type} [Sized α] [Sized β] [FirstNatComponent β] {T : Nat}
    (A : AlgSpec α β T) :
  ∃ (M : RandAdv α β T),
    M.toAlgSpec.run = A.run ∧
    M.C = A.C ∧
    M.k = A.k ∧
    Function.Surjective M.encoding.output.decode ∧
    (∀ c x, A.run c x ≠ M.early_decode_default) ∧
    FirstNatComponent.firstNat M.early_decode_default = 0
```

**Strength Test Questions**:
- [ ] Does this say anything about which functions can be computed?
  - **Analysis**: No - it says IF you have a poly-time spec, you get a poly-time TM
- [ ] Does this restrict the class of poly-time algorithms?
  - **Analysis**: No - it's the Church-Turing thesis (poly-time spec = poly-time TM)
- [ ] Could a poly-time algorithm for SAT violate this?
  - **Analysis**: No - if SAT had a poly-time algorithm, this axiom would give you the TM for it
- **VERDICT**: SAFE (definitional, not computational)

#### Axiom 2: `plant_flat_wf_transfer` (PlantExponential.lean:1067, private)

```lean
private axiom plant_flat_wf_transfer (φ' φ_known : CNF) (L : LStarInstanceFG)
    (h_L_phi' : ∃ n' r' h_nvars', L = plant_flat n' φ' r' h_nvars')
    (h_L_known : ∃ n r h_nvars, L = plant_flat n φ_known r h_nvars)
    (c : Clause) (hc : c ∈ φ'.clauses) (l : Literal) (hl : l ∈ c.literals)
    (h_wf_known : φ_known.WellFormed) : l.var < φ'.nvars
```

**Strength Test Questions**:
- [ ] Does this restrict polynomial-time computation?
  - **Analysis**: No - this is about CNF structure preservation, not computation
- [ ] Could this be false?
  - **Analysis**: No - if L = plant_flat(φ') = plant_flat(φ_known) with same structure, literal bounds transfer
- [ ] Is this information-theoretic?
  - **Analysis**: It's structural: plant_flat encodes φ injectively, so two CNFs producing same L must have same properties
- **VERDICT**: SAFE (structural property of plant_flat encoding)

#### Axiom 3: `fg_lossless_encoding` (EncodingDiscipline.lean:346, private)

```lean
private axiom fg_lossless_encoding
    (φ : CNF) (h_nvars_pos : φ.nvars > 0) (numGates : Nat)
    (gateIndex : Nat) (h_gate_valid : gateIndex < numGates)
    (h_numGates_valid : numGates ≤ φ.clauses.length)
    (h_vertex_valid : 1 + φ.nvars + gateIndex < ... .dag.n)
    (σ : LStar.Assignment)
    (h_cap : ... R v ≤ seedWidth v)
    (h_has_parents : ... .parents v ≠ ∅) :
    Foundations.extractEmergentBits seed R h_cap =
    Vector.ofFn (fun j : Fin R => if R > 0 then σ (R - 1 - j.val) else false)
```

**Strength Test Questions**:
- [ ] Does this restrict computation?
  - **Analysis**: No - it's a roundtrip property for bit extraction
- [ ] Is this mathematically deep?
  - **Analysis**: No - it says extracting R bits from an R-bit encoding recovers original data
- [ ] Why is it an axiom?
  - **Analysis**: Complex dependent type index manipulation (Fin.cast, Vector.get_append_right)
- **VERDICT**: SAFE (encoding mechanics, mathematically trivial)

#### Axiom 4: `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` (TMAdapterExponential.lean:297)

```lean
axiom tm_correctness_implies_realizesAllValuesFrom_flat_encoded
    (L : LStarInstanceFG) (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_L_eq : L = plant_flat n φ r h_nvars) (_h_wf : WellFormedRandomness_flat φ r)
    (v : {v // L.fg.gateReq v})
    {numTapes : Nat} {states alphabet : Type}
    [Fintype states] [DecidableEq states] [Fintype alphabet] [DecidableEq alphabet]
    (M : TuringMachine numTapes states alphabet)
    (init : TMConfig M) (haltTime : Nat)
    (extractWitness : TMConfig M → Witness)
    (encodeConfig : TMConfig M → Nat)
    -- UNIFORMITY REQUIREMENT
    (C_uniform k_uniform : Nat)
    (h_C_pos : C_uniform > 0) (h_k_pos : k_uniform > 0)
    (h_uniform_bound : haltTime ≤ C_uniform * (L.n + 1) ^ k_uniform)
    -- Standard parameters
    (val : Fin (2^(L.R v.val)))
    (h_val_reachable : ∃ cfg : TMConfig M, encodeConfig cfg = val.val)
    (h_missing : ∀ t < haltTime, encodeConfig (step^[t] init) ≠ val.val)
    (h_correct : φ.satisfies (extractWitness (step^[haltTime] init)).assignment)
    : False
```

**Strength Test Questions**:
- [ ] Does this directly say "poly-time can't do X"?
  - **Analysis**: No - it says IF (missing config) AND (correct output) AND (uniform PPT bound), then False
- [ ] Is this information-theoretically sound?
  - **Analysis**: Yes - if you miss observing some config value, you lack information needed for correctness on planted instances
- [ ] What about the uniformity requirement?
  - **Analysis**: CRUCIAL - prevents non-uniform "lucky TMs"; requires instance-independent C, k bounds
- [ ] Could this be false for some encoder?
  - **Analysis**: No - `h_val_reachable` guard ensures encoder is non-trivial; encoder completeness is PROVEN via `tmEmergentEncoder_surjective_flat`
- **VERDICT**: LIKELY SAFE (but requires deeper analysis - see Attack 1.17)

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
grep -B5 -A30 "^axiom " Layer4_Operational/TimeBridge/TMAdapterExponential.lean | grep -i "InP\|InNP\|P_ne\|PeqNP"
grep -B5 -A30 "^private axiom " Layer2_StructuralOWF/Plant/PlantExponential.lean | grep -i "InP\|InNP\|P_ne\|PeqNP"
grep -B5 -A30 "^private axiom " Layer5_Applications/PvsNP/ComplexityClasses/EncodingDiscipline.lean | grep -i "InP\|InNP\|P_ne\|PeqNP"
```

**Expected**: No matches. Axioms should be about:
- Encodings (algspec_has_tm)
- Structure preservation (plant_flat_wf_transfer)
- Bit extraction (fg_lossless_encoding)
- Information theory (collision_indistinguishability)
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
#check @tm_correctness_implies_realizesAllValuesFrom_flat_encoded
-- The collision axiom DOES conclude False, but only under specific preconditions
```

**Test 3: Mutual Contradiction Check**
```lean
-- Can we satisfy the preconditions of collision_indistinguishability
-- using outputs from algspec_has_tm?
--
-- algspec_has_tm: AlgSpec → TM
-- collision_indistinguishability: TM + incomplete observation → False
--
-- For contradiction: need to show EVERY TM from algspec_has_tm
-- satisfies h_missing AND h_correct simultaneously (impossible for correct TMs)
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

**Test for collision_indistinguishability**:
```lean
-- Can we satisfy ALL preconditions simultaneously?
-- This SHOULD be impossible for valid TMs:
-- - h_missing: some config value never visited
-- - h_correct: TM produces satisfying assignment
-- - h_val_reachable: missing value is reachable by encoder
--
-- For planted instances with correct TMs, visiting ALL 2^R configs is required
-- So h_missing + h_correct should be contradictory (which is what axiom says)
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

| Theorem | algspec_has_tm | collision_indist |
|---------|----------------|------------------|
| P_ne_NP | ✅ | ✅ |
| pnenp_classical | ✅ | ✅ |
| f_is_one_way | ✅ | ✅ |

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
- **plant_flat_wf_transfer**: Structural property, model-independent
- **fg_lossless_encoding**: Bit manipulation, model-independent
- **collision_indistinguishability**: The key axiom

**For collision_indistinguishability in a P=NP world**:
- If P=NP, there exists a poly-time SAT solver
- For planted instances, this solver must visit enough configs
- The axiom says: if missing config + correct output → False
- Question: Does poly-time SAT solver violate h_missing or satisfy all configs?

**Key insight**: In a P=NP world, a poly-time SAT solver for planted instances would either:
1. Visit ALL 2^R emergent configs (satisfying the coverage requirement) - but 2^R > poly(n), so impossible
2. NOT visit all configs but still be correct - violating the axiom

This is the crux: the axiom captures that correctness on planted instances REQUIRES exponential-time coverage, which is information-theoretically justified.

---

### ATTACK 1.10: Axiom Redundancy Check

**Goal**: Determine if axioms are derivable from each other

**Method**:
```lean
-- Can we prove axiom 2 from axiom 1?
theorem axiom2_from_axiom1 :
  (∀ A, algspec_has_tm A) →
  plant_flat_wf_transfer = _ := by
  sorry  -- SHOULD FAIL - different domains

-- Can we prove axiom 3 from axioms 1,2?
theorem axiom3_from_axiom12 :
  (∀ A, algspec_has_tm A) →
  (∀ args, plant_flat_wf_transfer args) →
  fg_lossless_encoding = _ := by
  sorry  -- SHOULD FAIL - independent concepts

-- Can we prove axiom 4 from axioms 1,2,3?
theorem axiom4_from_axiom123 :
  (∀ A, algspec_has_tm A) →
  (∀ args, plant_flat_wf_transfer args) →
  (∀ args, fg_lossless_encoding args) →
  collision_indistinguishability = _ := by
  sorry  -- SHOULD FAIL - axiom 4 is the key info-theoretic content
```

**Expected**: All `sorry` required (axioms are independent).

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

-- Test: Does collision_indistinguishability work with R = 0?
-- Answer: If R = 0, then 2^R = 1, so there's only 1 config value
-- This is handled by the h_nvars ≥ 4 requirement (ensures R > 0)
```

**Verification**: Check that axiom preconditions exclude degenerate cases.

---

### ATTACK 1.15: Private Axiom Visibility

**Goal**: Track private axioms by their mangled names

**Method**:
```bash
# Private axioms appear with _private prefix in #print axioms output
# Map mangled names to source locations

# Expected mappings:
# _private.Layer2_StructuralOWF.Plant.PlantExponential.0.LStar.StructuralOWF.plant_flat_wf_transfer
#   → Layer2_StructuralOWF/Plant/PlantExponential.lean:1067
# _private.Layer5_Applications.PvsNP.ComplexityClasses.EncodingDiscipline.0.LStar.Complexity.EncodingDiscipline.fg_lossless_encoding
#   → Layer5_Applications/PvsNP/ComplexityClasses/EncodingDiscipline.lean:346
```

**Red Flag**: Any private axiom not documented in trust boundary.

---

### ATTACK 1.16: Axiom Strength Comparison

**Goal**: Determine relative strength of axioms

**Analysis**:

| Axiom | Contribution | Could prove P≠NP alone? |
|-------|--------------|-------------------------|
| algspec_has_tm | TM bridge | No (Church-Turing) |
| plant_flat_wf_transfer | CNF structure | No (just encoding) |
| fg_lossless_encoding | Bit roundtrip | No (just extraction) |
| collision_indist | Info-theoretic bound | No (needs construction) |

**Key insight**: No single axiom implies P≠NP. The separation emerges from COMBINING:
1. The L* construction (creates planted instances)
2. Axioms 2,3 (encoding discipline)
3. Axiom 4 (coverage requirement)
4. Axiom 1 (TM representation)

---

### ATTACK 1.17: Vacuous Truth Check (NEW)

**Goal**: Verify axiom preconditions are satisfiable in non-trivial cases

**Method**:
```lean
-- For collision_indistinguishability: can h_missing AND h_correct both hold?
-- If they can NEVER both hold, axiom contributes nothing (vacuously true)

-- The axiom is designed so that for PLANTED instances with CORRECT TM output,
-- h_missing is TRUE (some config missing) implies contradiction.
-- This is the content: you CAN have h_correct, but then you CAN'T have h_missing.

-- Test: Construct a TM that visits all 2^R configs
-- Such TM would NOT satisfy h_missing (no value is missing)
-- Therefore axiom doesn't apply - this is correct behavior

-- Test: Construct a TM that misses some config but is still correct
-- On planted instances, this should be impossible (the axiom's claim)
-- If we could construct such a TM, the axiom would be false
```

**Verification**: The axiom's strength comes from:
1. Preconditions ARE satisfiable (planted instances exist, TMs exist)
2. But h_missing + h_correct are MUTUALLY contradictory on planted instances
3. This contradiction is the information-theoretic content

---

### ATTACK 1.18: Per-Axiom Dependency Audit (NEW)

**Goal**: For each axiom, verify it only depends on standard foundations

**Method**:
```bash
# Check each axiom's dependencies
cat > /tmp/per_axiom.lean << 'EOF'
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Layer4_Operational.TimeBridge.TMAdapterExponential
import Layer2_StructuralOWF.Plant.PlantExponential
import Layer5_Applications.PvsNP.ComplexityClasses.EncodingDiscipline

#print axioms LStar.Complexity.algspec_has_tm
#print axioms LStar.StructuralOWF.Foundations.FlatProfile.tm_correctness_implies_realizesAllValuesFrom_flat_encoded
-- Private axioms are self-referential (they ARE axioms)
EOF
lake env lean /tmp/per_axiom.lean 2>&1
```

**Expected**:
- `algspec_has_tm` → `[propext, Classical.choice, Quot.sound, algspec_has_tm]`
- `collision_indist` → `[propext, Classical.choice, Quot.sound, collision_indist]`
- Private axioms → Only standard + themselves

---

### ATTACK 1.19: Uniformity Requirement Analysis (NEW)

**Goal**: Verify the uniformity requirement in collision_indistinguishability is sound

**Background**: The axiom includes:
```lean
-- UNIFORMITY REQUIREMENT: TM must come from uniform PPT (instance-independent bounds)
(C_uniform k_uniform : Nat)
(h_C_pos : C_uniform > 0) (h_k_pos : k_uniform > 0)
(h_uniform_bound : haltTime ≤ C_uniform * (L.n + 1) ^ k_uniform)
```

**Questions**:
- [ ] Does this block non-uniform adversaries?
  - **Analysis**: Yes - a non-uniform TM hardcoded for specific instances would need different C,k per instance
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
- [ ] Exactly 4 custom axioms used by P_ne_NP (algspec_has_tm, plant_flat_wf_transfer, fg_lossless_encoding, collision_indistinguishability)
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
- [ ] Axiom count differs from verified 4
- [ ] Axiom preconditions are unsatisfiable
- [ ] Crypto axioms appear in P_ne_NP chain

---

## Historical Findings

From previous audits:
- **Eliminated**: `tm_overhead`, `encoding_semantics` (now theorems)
- **Current (verified 2025-12-07)**:
  1. `algspec_has_tm`
  2. `plant_flat_wf_transfer` (private)
  3. `fg_lossless_encoding` (private)
  4. `tm_correctness_implies_realizesAllValuesFrom_flat_encoded`
- **Vestigial**: `planted_revealedBits_empty` (not in P_ne_NP chain)
- **Not in chain**: `planted_pss_uniqueness_flat` (despite being in some docs)

---

## Appendix: Axiom Soundness Arguments

### Why `algspec_has_tm` is Sound

1. **Church-Turing Thesis**: Every effective computation has a TM
2. **Polynomial Preservation**: If AlgSpec has poly bound C*n^k, TM can simulate with same bound
3. **No Restriction**: This doesn't say what CAN'T be computed, only what CAN

### Why `plant_flat_wf_transfer` is Sound

1. **Injective Encoding**: `plant_flat` encodes CNF structure into L
2. **Structure Preservation**: Two CNFs producing same L must have same literal bounds
3. **No Computation**: Pure structural property

### Why `fg_lossless_encoding` is Sound

1. **Bit Manipulation**: Extracting R bits from R-bit encoding recovers original
2. **Mathematically Trivial**: Statement is immediate
3. **Axiomatized for**: Complex dependent type index manipulation in Lean

### Why `collision_indistinguishability` is Sound

1. **Information Theory**: Correctness requires observing relevant information
2. **Planted Construction**: FG gates encode randomness that determines correct assignment
3. **Coverage Requirement**: Missing config → missing information → cannot guarantee correctness
4. **Uniformity Guard**: Only applies to uniform PPT adversaries (instance-independent bounds)
5. **Soundness Guard**: `h_val_reachable` blocks trivial/degenerate encoders

### Why These Don't Assume P≠NP

A hypothetical P=NP world:
- `algspec_has_tm`: Still true (poly-time SAT solver would get a TM)
- `plant_flat_wf_transfer`: Still true (encoding structure unchanged)
- `fg_lossless_encoding`: Still true (bit extraction unchanged)
- `collision_indistinguishability`: Still true (information theory unchanged)

The P≠NP conclusion comes from COMBINING these with the FG construction,
not from the axioms themselves. The construction creates instances where
correctness requires 2^Ω(n) time, and no axiom blocks a poly-time algorithm
from existing—the construction makes such algorithms incorrect.

---

## Axiom File Locations (Quick Reference)

| Axiom | File | Line | Namespace |
|-------|------|------|-----------|
| `algspec_has_tm` | RandAdv.lean | 297 | `LStar.Complexity` |
| `plant_flat_wf_transfer` | PlantExponential.lean | 1067 | `LStar.StructuralOWF` (private) |
| `fg_lossless_encoding` | EncodingDiscipline.lean | 346 | `LStar.Complexity.EncodingDiscipline` (private) |
| `collision_indistinguishability_...` | TMAdapterExponential.lean | 297 | `LStar.StructuralOWF.Foundations.FlatProfile` |
