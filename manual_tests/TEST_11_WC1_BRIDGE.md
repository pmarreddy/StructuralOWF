# TEST 11: WC-1 Bridge Integration

**Priority**: CRITICAL
**Risk Level**: Proof-Invalidating
**Estimated Time**: 4-6 hours for comprehensive audit
**Branch**: wc1-bridge-integration
**Last Updated**: 2025-12-22

---

## Overview

The WC-1 Bridge introduces a new axiom architecture replacing the previous
`tm_correctness_implies_realizesAllValuesFrom_flat_encoded` axiom with a weaker,
more semantic `not_refuted_implies_indistinguishable` axiom.

**Key Changes in This Branch**:
1. New axiom: `not_refuted_implies_indistinguishable` (indistinguishability bridge)
2. Unified `algspec_has_tm` with `UniformityStructure` typeclass
3. `SameObservationSameState` property (renamed from ReplantingSimulation)
4. `WorstCaseCorrectOnLStar` property for TM correctness
5. `LStarTMEncoding` structure for L*-TM correspondence
6. Time bound derivation via WC-1 protocol (2^R - 1 steps)

**Trust Boundary**: 2 axioms total
- `algspec_has_tm`: Church-Turing bridge with uniformity
- `not_refuted_implies_indistinguishable`: Indistinguishability bridge

---

## Axiom Architecture Comparison

| Aspect | Main Branch | WC-1 Bridge Branch |
|--------|-------------|-------------------|
| Primary axiom | `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` | `not_refuted_implies_indistinguishable` |
| Time bound | 2^R (asserted) | 2^R - 1 (derived from WC-1 counting) |
| Semantic content | "Correct TM visits all values" | "Unrefuted worlds are indistinguishable" |
| Separation proof | Part of axiom | Derived via contradiction |
| Church-Turing | `algspec_has_tm` | `algspec_has_tm` + `UniformityStructure` |

---

## Attack Vectors

### ATTACK 11.1: Axiom Strength Analysis

**Goal**: Verify `not_refuted_implies_indistinguishable` doesn't secretly assume P≠NP

**Location**: `Layer4_Operational/TimeBridge/WC1Bridge.lean:4067`

```lean
axiom not_refuted_implies_indistinguishable
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
    (h_not_refuted : ω' ∉ tmRefutedWorlds L {v} configs)
    : TMIndistinguishable L M v enc.extractConfigAtV enc.initForPlanting haltTime
        (ω'.assignment v h_v_in) cfg_planted
```

**Strength Test Questions**:
- [ ] Does this axiom restrict what TMs can compute?
  - **Analysis**: No - it says IF a world wasn't refuted, THEN TM can't distinguish it
- [ ] Could a poly-time SAT solver violate this axiom?
  - **Analysis**: No - if SAT is poly-time solvable, all worlds get refuted quickly, making h_not_refuted vacuously false
- [ ] Does this axiom assert any time bounds?
  - **Analysis**: No - time bounds are DERIVED from the axiom + WC-1 counting
- [ ] Is this axiom information-theoretically sound?
  - **Analysis**: Yes - if TM hasn't distinguished a world, it's operationally indistinguishable

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Print axiom dependencies of the bridge axiom
cat > /tmp/bridge_axiom.lean << 'EOF'
import Layer4_Operational.TimeBridge.WC1Bridge
#print axioms LStar.StructuralOWF.Foundations.not_refuted_implies_indistinguishable
EOF
lake env lean /tmp/bridge_axiom.lean 2>&1
```

**Expected Output**:
```
'LStar.StructuralOWF.Foundations.not_refuted_implies_indistinguishable' depends on axioms:
[..., LStar.StructuralOWF.Foundations.not_refuted_implies_indistinguishable]
```

**Red Flags**:
- Axiom depending on P≠NP-related axioms
- Axiom referencing "polynomial" or "exponential" directly
- Circular dependency with main theorem

**Verification Checklist**:
- [ ] Axiom is purely semantic (no complexity assertions)
- [ ] h_configs_def ties to actual TM trace (not arbitrary)
- [ ] TMIndistinguishable conclusion is operationally meaningful
- [ ] Axiom doesn't reference time bounds

---

### ATTACK 11.2: WC-1 "+1 Per Step" Verification

**Goal**: Verify WorldCommit-1 theorem proves exactly +1 elimination per UnitRefute step

**Location**: `Layer3_InformationBounds/WorldCommit/WorldCommit.lean`

**Key Theorem**: `world_commit_refutation_excludes_one`

**Attack Questions**:
- [ ] Does WC-1 actually prove +1 (not +0 or +2)?
- [ ] Is UnitRefute defined as excluding exactly one world?
- [ ] Is the feasible set properly finite?

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check WC-1 theorem
cat > /tmp/wc1_check.lean << 'EOF'
import Layer3_InformationBounds.WorldCommit.WorldCommit
#check @LStar.WorldCommit.world_commit_refutation_excludes_one
#print axioms LStar.WorldCommit.world_commit_refutation_excludes_one
EOF
lake env lean /tmp/wc1_check.lean 2>&1

# Check UnitRefute definition
grep -A 10 "structure UnitRefute" Layer3_InformationBounds/WorldCommit/*.lean
```

**Expected**: WC-1 theorem depends only on standard axioms (propext, Classical.choice, Quot.sound)

**Verification Checklist**:
- [ ] `world_commit_refutation_excludes_one` is PROVEN (not axiom)
- [ ] Feasible set cardinality decreases by exactly 1
- [ ] UnitRefute constraint is `ω ≠ ω₀` (excludes exactly one world)
- [ ] No hidden axioms in WC-1 proof chain

---

### ATTACK 11.3: SameObservationSameState Property

**Goal**: Verify SameObservationSameState is sound and captures "TM only knows what it computed"

**Location**: `Layer4_Operational/TimeBridge/LStarEncodingTypes.lean:79`

```lean
def SameObservationSameState
    (L : LStarInstanceFG)
    (M : TuringMachine k states alphabet)
    (v : Fin L.dag.n)
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    : Prop :=
  ∀ (cfg_planted : Fin (2^(L.R v))) (t : Nat),
    let state_t := (TMConfig.step (M := M))^[t] (initForPlanting cfg_planted)
    let c := extractConfigAtV state_t
    (TMConfig.step (M := M))^[t] (initForPlanting c) = state_t
```

**Semantic Meaning**: "If TM extracts config c at time t, running with c planted reaches same state"

**Attack Questions**:
- [ ] Is this property achievable by uniform TMs?
  - **Analysis**: Yes - uniform TMs have fixed transition function, state depends only on tape contents
- [ ] Could a non-uniform TM violate this?
  - **Analysis**: Yes, but we only consider uniform TMs (Church-Turing)
- [ ] Does this property hold for standard SAT solvers?
  - **Analysis**: Yes - any deterministic TM satisfies this (state determined by computation path)

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check property definition
cat > /tmp/sameobs_check.lean << 'EOF'
import Layer4_Operational.TimeBridge.LStarEncodingTypes
#check @LStar.StructuralOWF.Foundations.SameObservationSameState
#print axioms LStar.StructuralOWF.Foundations.SameObservationSameState
EOF
lake env lean /tmp/sameobs_check.lean 2>&1
```

**Verification Checklist**:
- [ ] Property is a definition (not axiom)
- [ ] Follows from uniform TM semantics
- [ ] Captures "TM oblivious to secret planting"
- [ ] Used correctly in time bound derivation

---

### ATTACK 11.4: WorstCaseCorrectOnLStar Property

**Goal**: Verify TM correctness property is standard and achievable

**Location**: `Layer4_Operational/TimeBridge/LStarEncodingTypes.lean:45`

```lean
def WorstCaseCorrectOnLStar
    (L : LStarInstanceFG)
    (M : TuringMachine k states alphabet)
    (v : Fin L.dag.n)
    (extractConfigAtV : TMConfig M → Fin (2^(L.R v)))
    (initForPlanting : Fin (2^(L.R v)) → TMConfig M)
    (haltTime : Nat)
    : Prop :=
  ∀ (cfg : Fin (2^(L.R v))),
    let finalState := (TMConfig.step (M := M))^[haltTime] (initForPlanting cfg)
    extractConfigAtV finalState = cfg
```

**Semantic Meaning**: "For ALL 2^R possible plantings, TM correctly identifies which was planted"

**Attack Questions**:
- [ ] Is "worst-case correct" the right notion?
  - **Analysis**: Yes - OWF security requires correctness on ALL inputs
- [ ] Is this achievable by poly-time TMs?
  - **Analysis**: That's the question! If achievable in poly-time, OWF doesn't exist
- [ ] Is the property non-vacuous?
  - **Analysis**: Yes - 2^(L.R v) is exponentially large, so this is substantive

**Verification Checklist**:
- [ ] Property is a definition (not axiom)
- [ ] Quantifies over ALL 2^R configs (worst-case)
- [ ] "Correct" means extractConfigAtV returns planted config
- [ ] Non-vacuous for large R

---

### ATTACK 11.5: Time Bound Derivation Chain

**Goal**: Verify time bound 2^R - 1 is correctly derived from axiom

**Proof Chain**:
```
not_refuted_implies_indistinguishable (axiom)
    ↓
all wrong worlds must be refuted (by contradiction + WC correctness)
    ↓
refuted.length = 2^R - 1 (counting: 2^R worlds total, 1 planted)
    ↓
each refutation takes ≥1 step (WC-1 structure)
    ↓
haltTime ≥ 2^R - 1 (time bound)
```

**Key Theorems**:
1. `derive_all_wrong_worlds_refuted` (WC1Bridge.lean:2320)
2. `wrong_worlds_count_singleton` (WC1Bridge.lean:2765)
3. `fg_first_commit_time_lower_bound_via_wc1` (WC1Bridge.lean:2435)

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check time bound theorem
cat > /tmp/timebound_check.lean << 'EOF'
import Layer4_Operational.TimeBridge.WC1Bridge
#check @LStar.StructuralOWF.Foundations.fg_first_commit_time_lower_bound_via_wc1
#print axioms LStar.StructuralOWF.Foundations.fg_first_commit_time_lower_bound_via_wc1
EOF
lake env lean /tmp/timebound_check.lean 2>&1
```

**Attack Questions**:
- [ ] Is 2^R - 1 correct (not 2^R or 2^R - 2)?
  - **Analysis**: Yes - 2^R total worlds, 1 planted, so 2^R - 1 wrong worlds to refute
- [ ] Is the "-1" propagated correctly to final theorem?
  - **Analysis**: Check `exponential_dominates_poly_general_minus_one` handles this

**Verification Checklist**:
- [ ] Bound is 2^R - 1 (not 2^R)
- [ ] Each step eliminates exactly 1 world (WC-1)
- [ ] Final theorem uses correct bound
- [ ] Monotonicity lemma handles time extension

---

### ATTACK 11.6: tmRefutedWorlds and Nodup Property

**Goal**: Verify refuted worlds are correctly determined and counted

**Location**: `Layer4_Operational/TimeBridge/WC1Bridge.lean:726`

**Key Definitions**:
- `tmRefutedWorlds`: Builds list of refuted worlds from TM config trace
- `extractViolatorsForConfig`: Returns the world that violates a given config observation
- `buildRefutedWorlds`: Constructs refuted worlds list incrementally

**Why Nodup Matters**: The time bound proof counts refuted worlds. If the list has duplicates, the count would be wrong. The `tmRefutedWorlds_nodup` theorem proves no duplicates.

**Attack Questions**:
- [ ] Is tmRefutedWorlds correctly defined from TM trace?
- [ ] Does extractViolatorsForConfig return exactly one violator?
- [ ] Is nodup proven (not assumed)?
- [ ] Does the counting argument use nodup correctly?

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check tmRefutedWorlds definition
grep -A 15 "noncomputable def tmRefutedWorlds" Layer4_Operational/TimeBridge/WC1Bridge.lean

# Check nodup theorem
grep -n "theorem tmRefutedWorlds_nodup" Layer4_Operational/TimeBridge/WC1Bridge.lean

# Check extractViolatorsForConfig returns single element
grep -n "extractViolatorsForConfig_length_le_one" Layer4_Operational/TimeBridge/WC1Bridge.lean
```

**Key Theorems**:
- `tmRefutedWorlds_nodup_general` (line 1185)
- `extractViolatorsForConfig_length_le_one` (line 740)
- `buildRefutedWorlds_nodup` (line 1131)

**Verification Checklist**:
- [ ] tmRefutedWorlds built from actual TM trace
- [ ] extractViolatorsForConfig returns ≤1 element
- [ ] nodup property is PROVEN
- [ ] Counting in time bound uses nodup

---

### ATTACK 11.7: LStarTMEncoding Structure Soundness

**Goal**: Verify LStarTMEncoding fields are reasonable and prevent cheating

**Location**: `Layer4_Operational/TimeBridge/WC1Bridge.lean:3890`

**Key Fields**:
- `initForPlanting`: Creates TM initial state from planted config
- `extractConfigAtV`: Reads TM's current guess for config at v
- `sameObservationSameState`: Obliviousness property
- `worstCaseCorrect_at_C_n_k`: Correctness at poly-time bound
- `h_halts`: Halting guarantee
- `h_extract_tape0`: Extract reads only tape 0
- `encoding_coherence`: initForPlanting uses standard encoding

**Attack Questions**:
- [ ] Could a cheating encoding bypass the time bound?
  - **Analysis**: No - encoding_coherence forces standard input encoding
- [ ] Could extractConfigAtV cheat by returning wrong values?
  - **Analysis**: No - worstCaseCorrect requires it to return correct planted config
- [ ] Is sameObservationSameState enough to prevent backdoor knowledge?
  - **Analysis**: Yes - forces TM state to depend only on extracted values

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check LStarTMEncoding structure
grep -A 50 "structure LStarTMEncoding" Layer4_Operational/TimeBridge/WC1Bridge.lean
```

**Verification Checklist**:
- [ ] All fields are necessary (no redundancy)
- [ ] No fields allow cheating
- [ ] encoding_coherence blocks custom encodings
- [ ] Fields are used in time bound proof

---

### ATTACK 11.8: UniformityStructure Integration

**Goal**: Verify algspec_has_tm properly includes uniformity via typeclass

**Location**: `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean:340-385`

**L* UniformityStructure Instance**:
```lean
instance : UniformityStructure
    (Σ _n : Nat, LStar.StructuralOWF.LStarInstanceFG)
    (Σ n : Nat, Vector Bool (2 * n + 64)) where
  uniformityProp := fun {T} M =>
    -- (1) HaltPreservesTape0: TM doesn't modify tape 0 after halting
    -- (2) For each L* instance and gate vertex:
    --     ∃ initForPlanting, extractConfigAtV, coinsFor,
    --       SameObservationSameState ∧ WorstCaseCorrectOnLStar ∧ ...
```

**Attack Questions**:
- [ ] Is uniformityProp part of algspec_has_tm axiom?
  - **Analysis**: Yes - axiom conclusion includes `uniformityProp M`
- [ ] Could a TM satisfy algspec_has_tm without uniformity?
  - **Analysis**: No - uniformityProp is required by the axiom
- [ ] Is the typeclass resolution correct for L* types?
  - **Analysis**: Check instance priority and specialization

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check algspec_has_tm axiom
cat > /tmp/unified_axiom.lean << 'EOF'
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
#check @LStar.Complexity.algspec_has_tm
#print axioms LStar.Complexity.algspec_has_tm
EOF
lake env lean /tmp/unified_axiom.lean 2>&1
```

**Verification Checklist**:
- [ ] uniformityProp is in axiom conclusion
- [ ] L* instance provides substantive uniformity
- [ ] Non-L* types get trivial (True) uniformity
- [ ] Type specialization works correctly

---

### ATTACK 11.9: TMIndistinguishable Definition

**Goal**: Verify TMIndistinguishable captures correct operational semantics

**Location**: `Layer4_Operational/TimeBridge/WC1Bridge.lean`

**Definition** (approximate):
```lean
def TMIndistinguishable L M v extractConfigAtV initForPlanting haltTime cfg1 cfg2 : Prop :=
  extractConfigAtV ((TMConfig.step)^[haltTime] (initForPlanting cfg1)) =
  extractConfigAtV ((TMConfig.step)^[haltTime] (initForPlanting cfg2))
```

**Semantic Meaning**: "TM outputs the same config when planted with cfg1 vs cfg2"

**Attack Questions**:
- [ ] Is this the right definition of indistinguishability?
  - **Analysis**: Yes - operational indistinguishability = same output
- [ ] Could TM be "indistinguishable" but still distinguish internally?
  - **Analysis**: No - if output is same, TM hasn't distinguished for correctness purposes
- [ ] Is haltTime the right time to check?
  - **Analysis**: Yes - we care about final output at halt time

**Verification Checklist**:
- [ ] Definition is operational (based on TM output)
- [ ] Uses extractConfigAtV consistently
- [ ] haltTime parameter is sensible
- [ ] Symmetric in cfg1 and cfg2

---

### ATTACK 11.10: Proof Chain from Axiom to P≠NP

**Goal**: Verify complete chain from new axiom to P≠NP theorem

**Chain**:
```
algspec_has_tm (Church-Turing + uniformity)
    ↓
not_refuted_implies_indistinguishable (indistinguishability bridge)
    ↓
derive_all_wrong_worlds_refuted (by contradiction)
    ↓
fg_first_commit_time_lower_bound_via_wc1 (time bound)
    ↓
StructuralOWFExponential.fg_exponential_time_lower_bound
    ↓
P_ne_NP
```

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check final theorem axioms
cat > /tmp/final_check.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/final_check.lean 2>&1
```

**Expected Axioms**:
- propext, Classical.choice, Quot.sound (standard)
- algspec_has_tm (Church-Turing)
- not_refuted_implies_indistinguishable (indistinguishability bridge)

**Verification Checklist**:
- [ ] Exactly 2 custom axioms in P_ne_NP chain
- [ ] Old axiom `tm_correctness_implies_realizesAllValuesFrom_flat_encoded` NOT present
- [ ] Chain is complete (no missing links)
- [ ] All intermediate theorems are proven (no sorries)

---

### ATTACK 11.11: WorstCaseCorrectOnLStar Monotonicity

**Goal**: Verify correctness extends to times beyond halt time

**Key Theorem**: `WorstCaseCorrectOnLStar_monotone` (LStarEncodingTypes.lean:234)

**Why This Matters**: The time bound might be derived at a smaller time than the adversary's actual run time. Monotonicity ensures correctness at t1 implies correctness at t2 ≥ t1.

**Verification Commands**:
```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Check monotonicity theorem
cat > /tmp/mono_check.lean << 'EOF'
import Layer4_Operational.TimeBridge.LStarEncodingTypes
#check @LStar.StructuralOWF.Foundations.WorstCaseCorrectOnLStar_monotone
#print axioms LStar.StructuralOWF.Foundations.WorstCaseCorrectOnLStar_monotone
EOF
lake env lean /tmp/mono_check.lean 2>&1
```

**Attack Questions**:
- [ ] Does monotonicity require HaltPreservesTape0?
  - **Analysis**: Yes - TM must not modify tape 0 after halting
- [ ] Does monotonicity require ExtractReadsOnlyTape0?
  - **Analysis**: Yes - extract must only depend on tape 0
- [ ] Are these properties part of UniformityStructure?
  - **Analysis**: Check if they're in L* uniformityProp

**Verification Checklist**:
- [ ] Monotonicity theorem is PROVEN (not axiom)
- [ ] HaltPreservesTape0 is in L* uniformityProp
- [ ] ExtractReadsOnlyTape0 is in L* uniformityProp
- [ ] All preconditions are satisfied by adversary structure

---

## Summary Checklist

### Critical Checks (Must All Pass):

- [ ] `not_refuted_implies_indistinguishable` doesn't assume P≠NP
- [ ] WC-1 theorem (`world_commit_refutation_excludes_one`) is PROVEN, not axiom
- [ ] Time bound 2^R - 1 is correctly derived
- [ ] SameObservationSameState captures "TM oblivious to planting"
- [ ] WorstCaseCorrectOnLStar is standard TM correctness
- [ ] tmRefutedWorlds nodup property is PROVEN
- [ ] LStarTMEncoding structure prevents cheating encodings
- [ ] algspec_has_tm includes uniformityProp
- [ ] TMIndistinguishable is operationally sound
- [ ] P_ne_NP depends on exactly 2 custom axioms
- [ ] No sorries in proof chain
- [ ] Monotonicity lemma bridges time bound mismatch

### Failure Criteria:

- Axiom secretly assumes P≠NP
- WC-1 "+1" property not proven
- Time bound wrong (2^R instead of 2^R - 1)
- Missing link in proof chain
- Sorry in critical path
- Cheating encoding possible
- Axiom count ≠ 2

---

## Quick Test Commands

```bash
cd /Volumes/Ddrive/PNePNP-Publication/lean

# Full build
lake build

# Check axiom count for P_ne_NP
cat > /tmp/axiom_full.lean << 'EOF'
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge
#print axioms LStar.Complexity.StructuralOWFBridge.P_ne_NP
EOF
lake env lean /tmp/axiom_full.lean 2>&1 | grep -E "algspec_has_tm|not_refuted_implies_indistinguishable|tm_correctness"

# Check for sorries
grep -rn "\bsorry\b" --include="*.lean" Layer4_Operational/TimeBridge/ | grep -v "-- sorry"
grep -rn "\bsorry\b" --include="*.lean" Layer5_Applications/ | grep -v "-- sorry"

# Check WC-1 bridge theorems are proven (not axiom)
grep -n "^theorem\|^axiom" Layer4_Operational/TimeBridge/WC1Bridge.lean | head -30
```

---

## References

- `Layer4_Operational/TimeBridge/WC1Bridge.lean`: Main WC-1 bridge file
- `Layer4_Operational/TimeBridge/LStarEncodingTypes.lean`: SameObservationSameState, WorstCaseCorrectOnLStar
- `Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean`: Unified algspec_has_tm axiom
- `Layer3_InformationBounds/WorldCommit/WorldCommit.lean`: WC-1 theorem
- `docs/AXIOM_FINAL_COUNT.md`: Trust boundary documentation
