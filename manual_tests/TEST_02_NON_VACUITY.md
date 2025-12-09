# TEST 02: Non-Vacuity Verification

**Priority**: CRITICAL
**Risk Level**: Proof-Invalidating
**Estimated Time**: 3-5 hours for comprehensive verification

---

## Overview

A theorem can be "proven" but meaningless if it's vacuously true. This happens when:
- Types are uninhabited (empty)
- Preconditions are unsatisfiable
- Universal quantifiers range over empty sets
- Existential quantifiers trivially satisfied

**The Danger**: `∀ x : Empty, P x` is always true (vacuously) for ANY P.

---

## Attack Vectors

### ATTACK 2.1: Empty Type Detection

**Goal**: Verify all key types are inhabited

**Types to Check**:

| Type | File | Must Contain |
|------|------|--------------|
| `LStarInstanceFG` | Layer2_StructuralOWF/FrontierGate/FrontierGate.lean | At least one instance |
| `NodeData` | Layer0_Foundations/SCL/NodeData.lean | At least one node |
| `ConfigSpace L C` | Layer3_InformationBounds/SegmentReduction/ConfigTypes.lean | At least one config |
| `RandAdv α β T` | Layer5_Applications/PvsNP/ComplexityClasses/RandAdv.lean | At least one adversary |
| `TuringMachine` | Layer4_Operational/TuringMachine/TuringMachineSemantics.lean | At least one TM |
| `CNF` | Layer0_Foundations/Base/CNF.lean | At least one formula |
| `CutData` | Layer0_Foundations/SCL/SCLCut.lean | At least one cut |

**Method**:
```lean
-- For each type, prove Nonempty or construct explicit witness

-- Test 1: LStarInstanceFG
#check (inferInstance : Nonempty LStarInstanceFG)  -- Should typecheck
-- OR construct explicitly:
example : LStarInstanceFG := ⟨...⟩  -- Fill in

-- Test 2: NodeData
example : NodeData := {
  Known := Unit,
  UnknownIdx := Empty,  -- Could this be the problem?
  State := Unit,
  -- ...
}

-- Test 3: Adversary (RandAdv)
def trivial_adversary : RandAdv Nat Bool 1 := {
  run := fun _ _ => true,
  -- ...
}
```

**Red Flags**:
- `Nonempty` instance not found
- Cannot construct explicit witness
- Type requires `False` to construct

---

### ATTACK 2.2: The Language L* Emptiness Attack

**Goal**: Verify L* (the "hard" language) is non-empty

**Critical Question**: Is there ANY string in L*?

**Method**:
```lean
-- L* should contain at least one instance for some n
-- Check: Can we construct a concrete L* instance?

-- Find the L* definition
-- Typically: L* = { x | ∃ witness, verifier accepts (x, witness) }

-- Test: For some concrete n, does L*_n have members?
example : ∃ (n : Nat) (x : LStarInstance n), x ∈ L_star := by
  -- Must be constructive!
  use 128  -- security parameter
  use concrete_instance
  exact membership_proof
```

**Verification Checklist**:
- [ ] L* definition allows non-empty instances
- [ ] For n = 128 (minimum parameter), L*_n is non-empty
- [ ] Can construct explicit member of L*

---

### ATTACK 2.3: Adversary Class Emptiness

**Goal**: Verify PPT adversary class is non-empty

**The Risk**: If no PPT adversary exists, "no PPT adversary can invert" is vacuously true

**Method**:
```lean
-- Construct a trivial PPT adversary (doesn't matter if it's useless)
def trivial_ppt : RandAdv (Sigma fun n => Vector Bool n) (Sigma fun n => Vector Bool n) 1 := {
  run := fun _ s => s,  -- Identity function
  time_bound := fun n => n + 1,
  C := 1,
  k := 1,
  poly_explicit := ...,  -- Prove n+1 ≤ 1*(n+1)^1
  -- ...
}

-- This proves: ∃ A, A is a PPT adversary
-- Therefore: "no PPT adversary" quantifies over non-empty set
```

**Existing Test**: `testing/RedTeamBridge.lean` has `identity_in_fp` which does this (lines 29-55).

**Verification**:
- [ ] `identity_in_fp` theorem exists and compiles
- [ ] Can construct other non-trivial PPT adversaries
- [ ] Adversary class includes "reasonable" algorithms (not just identity)

---

### ATTACK 2.4: Security Parameter Degeneracy

**Goal**: Verify proof works for meaningful n (not just n=0)

**The Risk**: If proof only works for n=0, it's degenerate

**Method**:
```bash
# Search for security parameter constraints
grep -rn "n ≥" --include="*.lean" | grep -v ".lake"
grep -rn "h_n" --include="*.lean" | grep -v ".lake" | head -20
```

**Check Points**:
1. What is minimum n in the proof?
2. Does the bound 2^n make sense for small n?
3. Are there special cases for n=0, n=1?

**Test**:
```lean
-- Verify the theorem holds for concrete n
-- n = 128 should be the minimum meaningful parameter

-- Check: Does P_ne_NP depend on n ≥ 128?
-- Look for: h_n : n ≥ 128 or similar
```

**Verification**:
- [ ] Proof works for n ≥ 128 (standard security parameter)
- [ ] No degenerate n=0 special case
- [ ] Exponential bound 2^n is non-trivial for used n values

---

### ATTACK 2.5: Vacuous Implication Detection

**Goal**: Find theorems of form `(False) → anything`

**Method**:
```lean
-- Search for suspicious patterns:
-- 1. Premises that can never be satisfied
-- 2. Type constraints that are impossible

-- Red flag patterns:
-- theorem foo (h : False) : P := by trivial
-- theorem bar (h : 0 = 1) : P := by trivial
-- theorem baz (x : Empty) : P := by exact x.elim
```

**Automated Search**:
```bash
# Look for Empty type in theorem signatures
grep -rn "Empty" --include="*.lean" | grep -v ".lake" | grep -E "theorem|def"

# Look for explicit False premises
grep -rn ": False →\|h.*:.*False" --include="*.lean" | grep -v ".lake"
```

---

### ATTACK 2.6: Singleton Type Collapse

**Goal**: Detect when types collapse to trivial (Unit/singleton)

**The Risk**: If ConfigSpace has only 1 element, cardinality bounds are trivial

**Method**:
```lean
-- Check: Is ConfigSpace ever singleton?
-- ConfigSpace L C = Π v ∈ C, Config v

-- If C = ∅, then ConfigSpace L ∅ = Unit (singleton!)
-- Bound: |Unit| ≥ 2^0 = 1 ✓ (trivially true but vacuous)

-- Important: Does the proof USE non-empty cuts?
-- Check for: h_nonempty : C.Nonempty or C.card > 0
```

**Verification**:
- [ ] Main theorems require non-empty cuts
- [ ] FG gate cut is provably non-empty
- [ ] ConfigSpace has cardinality > 1 in actual use

---

### ATTACK 2.7: Instantiation Witness Test

**Goal**: For each existential, provide concrete witness

**Key Existentials**:

1. **OWF Exists**: `∃ f, f is one-way`
```lean
-- Witness: Plant(φ, r) function
-- Check: Is this explicitly constructed?
#check Plant_function  -- Should exist and be concrete
```

2. **Hard Instance Exists**: `∃ x, x is hard for all PPT`
```lean
-- Witness: FG-planted instance
-- Check: Is this explicitly constructed?
#check hard_instance  -- Should exist
```

3. **Separation Exists**: `∃ L, L ∈ NP \ P`
```lean
-- Witness: L* language
-- Check: Is L* explicitly defined?
#check L_star_definition
```

**For Each**:
- [ ] Witness is explicitly constructed (not just "exists")
- [ ] Witness has verifiable properties
- [ ] Witness isn't trivial/degenerate

---

### ATTACK 2.8: Fintype Cardinality Sanity

**Goal**: Verify cardinality computations are non-degenerate

**Method**:
```lean
-- Key cardinality claims:
-- |ConfigSpace L C| = 2^(Σ_{v∈C} R_v)

-- Check for each component:
-- 1. R_v > 0 for FG gates (emergence exists)
-- 2. C is non-empty (cut has nodes)
-- 3. Product is non-trivial

-- Test:
example : ∀ L : LStarInstanceFG, ∀ C : Finset (Fin L.dag.n),
  C.Nonempty → Fintype.card (ConfigSpace L C) > 1 := by
  intro L C hne
  -- Must prove this constructively
  sorry  -- Fill in
```

---

### ATTACK 2.9: Known vs Unknown Bit Balance

**Goal**: Verify meaningful information-theoretic setup

**Check**: For FG nodes:
- |UnknownIdx| > 0 (there ARE unknown bits)
- |Known| is exponential in |UnknownIdx|
- The λ (residual) is positive

**Method**:
```lean
-- Check FG gate structure
-- R_v = number of emergent bits
-- For exponential profile: R_v = n (security parameter)

-- Verify: R_v > 0 always
#check fg_R_positive  -- Should be a theorem

-- Verify: λ = R - s where s is revealed bits
-- For s = 0 (FG reveals nothing): λ = R > 0
```

---

## Execution Protocol

### Step 1: Type Inhabitance Tests

Create file `lean/testing/NonVacuityTests.lean`:
```lean
import Layer5_Applications.PvsNP.PrimaryPath.StructuralOWFBridge

-- Test 1: LStarInstanceFG is inhabited
#check (inferInstance : Nonempty LStarInstanceFG)

-- Test 2: Can construct PPT adversary
example : ∃ (A : RandAdv Nat Nat 1), True := ⟨⟨...⟩, trivial⟩

-- Test 3: L* is non-empty (for some n)
-- This is the critical test
-- ...
```

### Step 2: Manual Witness Construction

For the main theorem, trace back and construct explicit witnesses:
1. P_ne_NP needs: separation witness
2. Separation needs: hard language
3. Hard language needs: OWF
4. OWF needs: Plant function
5. Plant function needs: CNF + randomness

Construct concrete instances of each.

### Step 3: Cardinality Verification

For key cardinality claims:
```lean
-- Verify 2^n > 1 for n ≥ 1
example (n : Nat) (h : n ≥ 1) : 2^n > 1 := by
  exact Nat.one_lt_two_pow h

-- Verify ConfigSpace cardinality
-- ...
```

---

## Pass/Fail Criteria

### PASS Conditions (ALL must be true):
- [ ] All key types are inhabited (Nonempty instance)
- [ ] L* language has explicit non-empty witness
- [ ] PPT adversary class is non-empty
- [ ] Security parameter n has meaningful minimum (≥ 128)
- [ ] No vacuous implications detected
- [ ] Cardinality bounds are non-trivial

### FAIL Conditions (ANY triggers failure):
- [ ] Any key type is empty/uninhabited
- [ ] Cannot construct L* member
- [ ] PPT adversary class is empty
- [ ] Proof only works for n=0
- [ ] Theorem has form `False → P`
- [ ] ConfigSpace collapses to singleton in all uses

---

## Concrete Test Cases

### Test Case 2.1: Plant Function Exists
```lean
-- Verify Plant(φ, r) is constructable
example : ∃ (φ : CNF) (r : Randomness), True := by
  use some_cnf  -- Must provide concrete CNF
  use some_randomness  -- Must provide concrete randomness
  trivial
```

### Test Case 2.2: FG Gate Has Emergence
```lean
-- Verify R_v > 0 for FG gates
theorem fg_has_positive_emergence (L : LStarInstanceFG) (v : L.fg.GateNode) :
    L.R v > 0 := by
  -- Must prove this
  sorry
```

### Test Case 2.3: Cut is Non-Empty
```lean
-- Verify the cut used in the proof is non-empty
theorem proof_cut_nonempty (L : LStarInstanceFG) :
    (fg_cut L).Nonempty := by
  -- Must prove this
  sorry
```

---

## Appendix: Common Vacuity Patterns

### Pattern 1: Empty Dependent Type
```lean
-- VACUOUS: P indexed by Empty
theorem bad (x : Empty) (P : Empty → Prop) : P x := x.elim
```

### Pattern 2: False Premise
```lean
-- VACUOUS: Impossible premise
theorem bad (h : 0 = 1) : P := by omega
```

### Pattern 3: Unsatisfiable Typeclass
```lean
-- VACUOUS: No instance exists
theorem bad [inst : Impossible] : P := inst.elim
```

### Pattern 4: Singleton Quantification
```lean
-- VACUOUS (if S has 1 element)
theorem bad (s : S) (h : ∀ x : S, x = s) : P := ...
```

---

## Known Non-Vacuity Guarantees

From existing code:

1. **`identity_in_fp`** (RedTeamBridge.lean): Proves FP is non-empty
2. **`Inhabited Known`** (NodeData.lean): Guarantees Known non-empty
3. **`Fintype` instances**: Guarantee finite but non-empty types

These provide baseline non-vacuity but MORE verification needed for:
- L* membership
- OWF construction
- Separation witness

---

## Additional Attack Vectors (Deep Red Team)

### ATTACK 2.10: Subtype Emptiness Attack

**Goal**: Find subtypes `{ x : α // P x }` where no x satisfies P

**Method**:
```lean
-- Subtypes can be empty if predicate is never satisfied
-- E.g., { n : Nat // n < 0 } is empty!

-- Search for Subtype usage
-- grep -rn "Subtype\|{ .* // " --include="*.lean"

-- For each subtype, verify:
-- 1. The predicate is satisfiable
-- 2. There's a witness construction
```

**Critical Subtypes to Check**:
- `{ v // L.fg.gateReq v }` - Are there FG gate nodes?
- `{ x // L x }` - Are there L* members?
- `{ A // PPT A }` - Are there PPT adversaries?

---

### ATTACK 2.11: Dependent Type Parameter Degeneracy

**Goal**: Find cases where type parameters cause emptiness

**Method**:
```lean
-- When types depend on parameters, parameter choice affects inhabitance

-- Example: Vector Bool 0 has exactly one element (empty vector)
-- But Vector Bool n for n > 0 has 2^n elements

-- Check: Are there dependent types that collapse for certain parameters?

-- Specifically check:
-- ConfigSpace L C when C is empty
-- Assign v when |UnknownIdx| = 0
-- Witness type when no witness exists
```

---

### ATTACK 2.12: Universe Level Inhabitance

**Goal**: Verify types at different universe levels are inhabited

**Method**:
```lean
-- Lean has universe polymorphism
-- Types at higher universes might behave differently

-- Check: Are all universe-polymorphic types properly instantiated?
#check @P_ne_NP  -- What universes does it quantify over?

-- Red flag: Type.{0} vs Type.{u} might have different properties
```

---

### ATTACK 2.13: Decidability Instance Availability

**Goal**: Verify decidability instances exist where needed

**Method**:
```lean
-- Some proofs require Decidable instances
-- If missing, the proof might not be computable

-- Check for:
#check (inferInstance : Decidable (x ∈ L_star))
#check (inferInstance : DecidableEq Config)

-- If these fail, there might be hidden non-constructivity
```

---

### ATTACK 2.14: Proof Irrelevance Exploitation

**Goal**: Check if proof irrelevance hides vacuity

**Method**:
```lean
-- In Prop, all proofs are equal (proof irrelevance)
-- This could hide that "the proof" is actually empty

-- Check: For key Prop-valued types, can we extract witnesses?

-- Example:
-- If (h : ∃ x, P x) is in Prop, we can't extract x
-- But we should be able to prove Nonempty { x // P x }
```

---

### ATTACK 2.15: Coercion Chain Emptiness

**Goal**: Find coercions that pass through empty types

**Method**:
```lean
-- Type coercions can hide complexity
-- A chain A → B → C might fail if B is empty

-- Check all coercion chains used in the proof
-- Verify each intermediate type is inhabited
```

---

### ATTACK 2.16: Function Space Analysis

**Goal**: Verify function spaces are non-trivially inhabited

**Method**:
```lean
-- Function space α → β is:
-- - Empty if α is nonempty and β is empty
-- - Singleton if α is empty (only one function: absurd)
-- - Large if both are nonempty

-- For key function types in the proof:
-- RandAdv α β T includes (Fin T → α → β)
-- Verify Fin T is nonempty (T > 0)
-- Verify α and β are nonempty
```

**Verification**:
- [ ] All RandAdv have T > 0 (coins_pos field)
- [ ] Input and output types are inhabited
- [ ] Function spaces are non-trivial

---

### ATTACK 2.17: Large Security Parameter Test

**Goal**: Verify proof works for realistic security parameters (n ≥ 128, n = 2048)

**Method**:
```lean
-- Standard cryptographic security parameters:
-- n = 128 (minimum modern security)
-- n = 256 (standard)
-- n = 2048 (high security)

-- Test 1: Construct L* instance with n = 128
example : ∃ (L : LStarInstanceFG), L.n = 128 := by
  -- Must be constructible
  sorry

-- Test 2: Verify 2^128 cardinality is representable
-- Lean's Nat is unbounded, but check computability
#check (2^128 : Nat)  -- Should work

-- Test 3: Verify bound 2^n > n^k holds concretely
example : 2^128 > 128^10 := by decide  -- Should succeed

-- Test 4: Construct L* instance with n = 2048
example : ∃ (L : LStarInstanceFG), L.n = 2048 := by
  sorry
```

**Questions**:
- [ ] Can L* be instantiated with n = 128?
- [ ] Can L* be instantiated with n = 2048?
- [ ] Are there hidden upper bounds on n?
- [ ] Does proof degenerate for large n?

**Pass Criteria**: Proof works for all n ≥ 128 without artificial restrictions.

---

### ATTACK 2.18: Cardinality Overflow Analysis

**Goal**: Verify 2^n doesn't cause representational issues

**Method**:
```lean
-- Lean's Nat is unbounded, but...
-- 1. Fintype.card returns Nat - can it overflow?
-- 2. 2^n for large n might be slow to compute
-- 3. Are there places where we assume Nat fits in machine word?

-- Check 1: Fintype.card is pure counting
#check @Fintype.card  -- Returns Nat (unbounded)

-- Check 2: 2^n is exact, not approximation
example (n : Nat) : 2^n = Nat.pow 2 n := rfl

-- Check 3: No truncation in comparisons
example (n : Nat) : 2^n ≥ 2^n := le_refl _

-- Check 4: Large exponents work
example : 2^1000 > 2^999 := by
  exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by norm_num)
```

**Questions**:
- [ ] Is Fintype.card truly unbounded?
- [ ] Are there hidden Word64/UInt64 conversions?
- [ ] Does `decide` tactic work for large cardinalities?
- [ ] Are comparisons like 2^n > n^k always computable?

**Pass Criteria**: No overflow or truncation for any n.

---

### ATTACK 2.19: Fintype Decidability and Enumeration

**Goal**: Verify ConfigSpace elements can actually be enumerated

**Method**:
```lean
-- Fintype requires:
-- 1. elems : Finset α (all elements)
-- 2. complete : ∀ x, x ∈ elems (every element listed)

-- For ConfigSpace L C:
-- elems must list all configurations
-- This requires C to be finite and enumerable

-- Check 1: ConfigSpace has Fintype instance
#check (inferInstance : Fintype (ConfigSpace L C))

-- Check 2: Can we enumerate small examples?
#eval (Finset.univ : Finset (Vector Bool 3)).card  -- Should be 8

-- Check 3: Is enumeration computable for large n?
-- Vector Bool 128 has 2^128 elements - can't enumerate!
-- But Fintype.card doesn't require enumeration, just existence

-- Check 4: Are there non-computable Fintype instances?
-- noncomputable def bad_fintype : Fintype X := ...
-- These might hide vacuity
```

**Questions**:
- [ ] Are all Fintype instances computable?
- [ ] Does Fintype.card require actual enumeration?
- [ ] Are there noncomputable Fintype definitions in the proof?
- [ ] Can we construct explicit witnesses for Fintype.card?

**Pass Criteria**: All Fintype instances are computably constructed (or explicitly marked noncomputable with justification).

---

## Critical Lemma Coverage (from PROOF_CONTROL_FLOW.md)

The codebase supports **two proof profiles** that share the same trust boundary:

| Profile | R_v Formula | Bound | Key Files | Proof Path |
|---------|-------------|-------|-----------|------------|
| **Exponential** | n | 2^n | RanksExponential, StructuralOWFExponential, TMAdapterExponential | Top-down |
| **QP-Sharp** | (log₂ n)² | n^{log n} | RanksQP, OWFSecurity, TMAdapter | Bottom-up (segment reduction) |

The **exponential profile** uses a top-down semantic derivation (simpler, stronger bounds).
The **QP profile** uses bottom-up segment reduction with WC-1 counting.

The following attacks verify non-vacuity of critical theorems from **both** proof spines. The exponential profile has **11 critical theorems** [1]-[11]; QP-specific theorems are marked.

---

### ATTACK 2.20: CutData Inhabitedness ([2] SCL_cut)

**Goal**: Verify CutData type is inhabited and produces non-trivial bounds

**Critical Theorem**: `SCL_cut` - Global Cut Bound
```lean
theorem SCL_cut (C : CutData)
  (h_keyed : ∀ i, NodeData.keyed (C.data i)) :
  Fintype.card (C.GlobalState) ≥ 2 ^ cut_lambda C
```

**Method**:
```lean
-- CutData requires:
-- 1. numNodes : Nat (number of nodes in cut)
-- 2. data : Fin numNodes → NodeData (node data for each)
-- 3. GlobalState definition

-- Check 1: Can we construct CutData with numNodes > 0?
-- Empty cut (numNodes = 0) trivializes: GlobalState = Unit, cut_lambda = 0

-- Check 2: Verify cut_lambda is sum of lambdas
-- cut_lambda C = Σ_i (lambda (C.data i))
-- If all NodeData have lambda = 0, bound is trivial

-- Check 3: Trace from LStarInstanceFull to CutData
-- LStarToNodeData.lean should produce CutData with positive lambda

-- Location: Layer0_Foundations/SCL/SCLCut.lean
-- Bridge: Layer1_Construction/Bridge/LStarToNodeData.lean
```

**Questions**:
- [ ] Is CutData constructible from L* with numNodes > 0?
- [ ] Does FG gate cut produce cut_lambda > 0?
- [ ] Can cut_lambda ever be 0 in the actual proof path?
- [ ] Is GlobalState for FG cut exponentially large (not Unit)?

**Pass Criteria**: CutData constructed from FG cut has cut_lambda ≥ 49 for n ≥ 128.

---

### ATTACK 2.21: World Cardinality Non-Vacuity (QP Profile)

**Profile Note**: This attack targets the **QP profile** (bottom-up segment reduction path). The **exponential profile** uses top-down approach via `TMAdapterExponential.lean` and bypasses segment reduction. Both profiles are valid; this attack ensures the QP path is non-vacuous.

**Goal**: Verify BitsOnlyWorlds and FeasibleWorlds are properly inhabited with non-trivial cardinality

**Critical Theorems**:
- `bits_only_cardinality_exact`: |BitsOnlyWorlds| = 2^(ρ-s)
- `refutation_count_exponential_bound`: refutationCount ≥ 2^(ρ-s) - 1

**Actual Codebase Structure** (no `SegmentContext` type exists):
```lean
-- ρ (total emergence) is computed inline:
-- ρ = C.sum (fun v => L.R v)  -- sum of R values over cut C

-- s (revealed bits) is computed via:
-- def effectiveRevealedCount (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
--     (π : ExecutionPrefixReal L) : Nat :=
--   (distinctRevealedCoords L C π).card
-- Location: Layer3_InformationBounds/SegmentReduction/SegmentReduction.lean:407-409

-- BitsOnlyWorlds definition:
-- noncomputable def BitsOnlyWorlds (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
--     (π : ExecutionPrefixReal L) : Finset (CutWorld L C) :=
--   let bitConstraints := extractBitConstraints L C π.revealedBits
--   Finset.univ.filter (fun ω => bitConstraints.all (fun c => c.Satisfies ω))
-- Location: Layer3_InformationBounds/SegmentReduction/SegmentReduction.lean:273-279

-- FeasibleWorlds definition:
-- noncomputable def FeasibleWorlds (L : LStarInstanceFG) (C : Finset (Fin L.dag.n))
--     (π : ExecutionPrefix L) : Finset (CutWorld L C) :=
--   Finset.univ.filter (fun ω => ConsistentWith ω π)
-- Location: Layer3_InformationBounds/WorldCommit/CutWorlds.lean:262-264
```

**Method**:
```lean
-- Check 1: Is ρ computed correctly for FG instances?
-- For FG: R_fg = n (security parameter), so ρ = n for single-gate cut

-- Check 2: Is s = 0 proven for FG?
-- seedLock_forces_completeObservation proves no partial revelations help
-- Location: Layer3_InformationBounds/Keyedness/SeedLockProperties.lean:274

-- Check 3: Are BitsOnlyWorlds non-empty?
-- BitsOnlyWorlds is filtered from Finset.univ - always at least one element
-- For FG with s = 0: |BitsOnlyWorlds| = 2^n

-- Check 4: Is FeasibleWorlds guaranteed non-empty?
-- The planted solution always exists: initial_feasible_worlds_count proves
-- (FeasibleWorlds L C (emptyPrefix L)).card = 2^(C.sum (fun v => L.R v))
-- Location: Layer3_InformationBounds/WorldCommit/CutWorlds.lean:323
```

**Questions**:
- [ ] Is ρ = C.sum (fun v => L.R v) computed correctly?
- [ ] Is FeasibleWorlds guaranteed non-empty (planted solution)?
- [ ] Does s = 0 hold for FG instances (via seed-lock)?
- [ ] Are there hidden constraints making ρ - s = 0?

**Pass Criteria**: For FG instance with n ≥ 128: ρ = n, s = 0, |BitsOnlyWorlds| = 2^n.

---

### ATTACK 2.22: FPneFNP Derivability ([10] parity_owf_implies_fpnefnp)

**Goal**: Verify FPneFNP_parametric_bits is DERIVED (not assumed), making the final theorem non-vacuous

**Critical Theorem**:
```lean
theorem fpnefnp_implies_not_peqnp
    (h_fpnefnp : FPneFNP_parametric_bits)
    : ¬PeqNP_parametric
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean:1714
```

**Method**:
```lean
-- This theorem has a hypothesis: h_fpnefnp : FPneFNP_parametric_bits
-- If FPneFNP_parametric_bits is never proven, theorem is vacuously true!

-- Check 1: Is FPneFNP_parametric_bits defined correctly?
-- Definition: ∃ f ∈ FNP, f ∉ FP (witness-based separation)
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean:1405

-- Check 2: Is FPneFNP_parametric_bits PROVEN somewhere?
-- Should be derived from OWF existence:
-- OWF exists → FP ≠ FNP (standard complexity theory)

-- Check 3: Trace the derivation chain
-- [9] f_is_parity_owf_exponential_flat (OWF security)
--   → parity_owf_implies_fpnefnp (Layer5_Applications/PvsNP/PrimaryPath/StructuralOWFBridge.lean)
--   → FPneFNP_parametric_bits (instantiated)

-- Check 4: Is this derivation complete (no sorries)?
-- Location: Layer5_Applications/PvsNP/PrimaryPath/StructuralOWFBridge.lean
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean
```

**Questions**:
- [ ] Is FPneFNP_parametric_bits proven (not just assumed)?
- [ ] Does OWF existence imply FPneFNP in the codebase?
- [ ] Is the derivation OWF → FP≠FNP complete?
- [ ] Are there sorries in the OWF → FP≠FNP path?

**Pass Criteria**: FPneFNP_parametric_bits is derived from OWF theorem [11], not assumed.

---

### ATTACK 2.23: PeqNP_parametric Well-Formedness ([11] pnenp FINAL)

**Goal**: Verify PeqNP_parametric is a meaningful hypothesis (not trivially false)

**Main Theorem** (clean form):
```lean
theorem fpnefnp_implies_not_peqnp
    (h_fpnefnp : FPneFNP_parametric_bits)
    : ¬PeqNP_parametric
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean:1714
```

**Intermediate Contradiction Lemma** (used internally):
```lean
theorem fpnefnp_and_peqnp_contradiction
    (h_fpnefnp : FPneFNP_parametric_bits)
    (h_peqnp : PeqNP_parametric)
    : False
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean:1468
```

**Method**:
```lean
-- The main theorem fpnefnp_implies_not_peqnp uses the clean implication form
-- Internally it relies on fpnefnp_and_peqnp_contradiction

-- Check 1: What is PeqNP_parametric?
-- Definition: ∀ L, InNP L → InP L (with uniform polynomial bounds)
-- This should NOT be trivially false (we're proving it false!)
-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean:1430-1450

-- Check 2: Is PeqNP_parametric internally consistent?
-- If PeqNP_parametric implies False without any other hypotheses,
-- then the theorem is trivial (proves anything from contradiction)

-- Check 3: What makes the contradiction work?
-- h_fpnefnp (FP ≠ FNP) + h_peqnp (P = NP) → contradiction
-- The contradiction should require BOTH hypotheses

-- Check 4: Verify theorem structure
-- Should be: assume P=NP, derive FP=FNP, contradict FP≠FNP
-- NOT: PeqNP_parametric is ill-defined or trivially false

-- Location: Layer5_Applications/PvsNP/PrimaryPath/ParametricBitstringBridge.lean
-- Definition: Layer5_Applications/PvsNP/ComplexityClasses/ComplexityClasses.lean
```

**Questions**:
- [ ] Is PeqNP_parametric a well-formed Prop (not trivially False)?
- [ ] Does the contradiction require BOTH hypotheses?
- [ ] Is there a model where PeqNP_parametric holds? (consistency check)
- [ ] Does the proof use h_pnenp_parametric essentially (not just discard)?

**Pass Criteria**: PeqNP_parametric is consistent (not trivially False) and contradiction requires both hypotheses.

---

### ATTACK 2.24: WorldCommit WC-1 Property (QP Profile)

**Profile Note**: This attack targets the **QP profile** (bottom-up segment reduction). The **exponential profile** uses top-down derivation via visited encodings counting and does not use WC-1. This attack ensures the QP path is non-vacuous.

**Goal**: Verify WC-1 property (each refutation eliminates ≤1 world) is non-vacuous

**Critical Dependency**: `refutation_count_exponential_bound` uses WC-1 property

**Method**:
```lean
-- WC-1 Property: Each refutation eliminates at most one world
-- This is CRITICAL for counting argument:
-- 2^(ρ-s) worlds → need 2^(ρ-s) - 1 refutations (one at a time)

-- Check 1: Is WC-1 defined as a theorem or axiom?
-- Actual theorem name: world_commit_refutation_excludes_one
-- Location: Layer3_InformationBounds/WorldCommit/WorldCommit.lean:579

-- Check 2: Does WC-1 have non-trivial content?
-- If worlds are singletons, WC-1 is trivially true
-- If refutations can eliminate 0 worlds, WC-1 is trivially true

-- Check 3: Verify worlds are distinguishable
-- Different bit assignments → different worlds
-- WC-1 says refuting one assignment doesn't affect others

-- Check 4: Is WC-1 proven or assumed?
-- FULLY PROVEN via 4 supporting lemmas:
-- - WC-1.1: committedWorld_feasible_before
-- - WC-1.2: committedWorld_violates_unitRefute
-- - WC-1.3: unitRefute_excludes_target
-- - WC-1.4: unitRefute_preserves_others
-- Header comment: "0 axioms, 0 sorries - FULLY PROVEN"
```

**Questions**:
- [ ] Is WC-1 property proven (not axiom)?
- [ ] Are there multiple worlds to refute (not singleton)?
- [ ] Does refutation genuinely eliminate exactly 1 world?
- [ ] Is the WC-1 → refutation_count connection sound?

**Pass Criteria**: WC-1 is proven theorem, and refutation count argument is sound.

---

### ATTACK 2.25: Extractor Witness Validity ([8] plant_extract_correct)

**Goal**: Verify extracted witness is genuinely satisfying (not trivial/empty)

**Critical Theorem**:
```lean
theorem plant_extract_correct (n : Nat) (φ : CNF) (r : Randomness) (h_nvars : φ.nvars ≥ 4)
    (h_dgLen : r.dgLen = (Nat.log 2 φ.nvars) ^ 2)
    (h_sat : φ.satisfies r.assignment) :
    let x := plant_n n φ r h_nvars h_dgLen
    φ.satisfies (extract x r).assignment
-- Location: Layer2_StructuralOWF/Extractor/Extractor.lean:282
```

**Method**:
```lean
-- This theorem has hypothesis: h_sat : φ.satisfies r.assignment
-- This means we must START with a satisfying assignment

-- Check 1: Does this create circularity?
-- We're proving OWF exists → P≠NP
-- But extractor requires existing satisfying assignment?

-- Check 2: What is the structure?
-- plant_n φ r creates instance L from φ and randomness r
-- r.assignment IS the satisfying assignment (built in)
-- extract recovers it from L

-- Check 3: Is φ.satisfies well-defined?
-- φ : CNF, should have non-trivial clauses
-- satisfies should check all clauses

-- Check 4: Is extraction non-trivial?
-- extract should not be identity function
-- Must decode from L* structure
-- Supporting theorems: extract_preserves_assignment, extract_poly_time_planted

-- Location: Layer2_StructuralOWF/Extractor/Extractor.lean
```

**Questions**:
- [ ] Is the planted assignment genuinely satisfying?
- [ ] Does extraction require non-trivial decoding?
- [ ] Is there circularity (need witness to prove witness exists)?
- [ ] Can φ be unsatisfiable (making h_satisfies False)?

**Pass Criteria**: Extractor recovers planted witness through actual decoding, no circularity.

---

## Summary: Critical Lemma Coverage

### Exponential Profile (Primary - 11 Theorems)

| # | Critical Theorem | Location | Attack | Status |
|---|-----------------|----------|--------|--------|
| [1] | SCL_node | Layer0_Foundations/SCL/SCLNode.lean:297 | 2.1, 2.6, 2.8, 2.9 | ✅ Covered |
| [2] | SCL_cut | Layer0_Foundations/SCL/SCLCut.lean:439 | 2.20 | ✅ Covered |
| [3] | L_satisfies_A2 + L_satisfies_A3 | Layer1_Construction/Properties/A2_Injectivity.lean:231, A3_Emergence.lean:260 | 2.1 | ✅ Covered |
| [4] | R_of_flat (def:216, pos:276) | Layer3_InformationBounds/Randomness/RanksExponential.lean | 2.4, 2.9 | ✅ Covered |
| [5] | seedLock_forces_completeObservation | Layer3_InformationBounds/Keyedness/SeedLockProperties.lean:274 | 2.9 | ✅ Covered |
| [6] | visitedEncodings_card_ge_pow | Layer4_Operational/TuringMachine/TuringMachineSemantics.lean:288 | 2.8 | ✅ Covered |
| [7] | fg_first_commit_time_lower_bound | Layer4_Operational/TimeBridge/TMAdapterExponential.lean:3559 | 2.3, 2.4 | ✅ Covered |
| [8] | plant_extract_correct | Layer2_StructuralOWF/Extractor/Extractor.lean:282 | 2.25 | ✅ Covered |
| [9] | f_is_parity_owf_exponential_flat | Layer2_StructuralOWF/Security/StructuralOWFExponential.lean:1489 | 2.3 (PPT) | ✅ Covered |
| [10] | parity_owf_implies_fpnefnp | Layer5_Applications/PvsNP/PrimaryPath/StructuralOWFBridge.lean:2443 | 2.22 | ✅ Covered |
| [11] | pnenp (P_ne_NP) | Layer5_Applications/PvsNP/PrimaryPath/StructuralOWFBridge.lean:2905,3237 | 2.22, 2.23 | ✅ Covered |

### QP Profile (Alternative - Additional Theorems)

| Theorem | Location | Attack | Notes |
|---------|----------|--------|-------|
| bits_only_cardinality_exact | Layer3_InformationBounds/SegmentReduction/SegmentReduction.lean:2241 | 2.21 | QP bottom-up path |
| refutation_count_exponential_bound | Layer3_InformationBounds/SegmentReduction/SegmentReduction.lean:3188 | 2.21, 2.24 | Uses WC-1 property |
| world_commit_refutation_excludes_one (WC-1) | Layer3_InformationBounds/WorldCommit/WorldCommit.lean:579 | 2.24 | Each refutation eliminates ≤1 world |

### Coverage Summary

**Exponential Profile**: 11 critical theorems - **ALL COVERED**
**QP Profile**: 3 additional theorems - **ALL COVERED**
**Total Attacks**: 25 (2.1-2.25)
**Profile-Agnostic Attacks**: 2.1-2.19 (apply to both)
**Profile-Specific Attacks**: 2.20-2.25 (target specific theorems)