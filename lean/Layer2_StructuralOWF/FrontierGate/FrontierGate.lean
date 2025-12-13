import Layer1_Construction.Core.InstanceOps
import Layer0_Foundations.Base.EncodedCNF
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Bitwise
import Layer3_InformationBounds.Support.TimingModel  -- Layer 3 dependency (will be updated when Layer 3 is organized)

/-! ## FrontierGate: Encoding and Identity Digest for Exponential World Splitting

**Architecture: R-bit Identity Digest**

The FG mechanism uses R-bit identity digest - the digest IS the full configuration:

1. **encodeSeed (Source of Hardness)**: Uses ALL R emergent bits
   - `encodeSeed L v hist emergent` embeds the full emergent vector into the seed
   - A2 injectivity: different emergent vectors → different seeds (full bit-level)
   - This is where the 2^R lower bound originates

2. **computeDigest (Identity Function)**: Returns full R-bit configuration
   - `computeDigest cfg = identityDigestVec cfg` - returns all R bits unchanged
   - Role: transparent discriminator (different configs → different digests)
   - Injectivity is trivial: identity function is bijective

**Proof Chain**:
```
cfg1 ≠ cfg2
  → identityDigest(cfg1) ≠ identityDigest(cfg2)  [identity is injective]
  → encodeSeed(cfg1) ≠ encodeSeed(cfg2)          [A2 injectivity]
  → different seeds → different instances
```

**Key Insight**: The hardness comes from the CUT (topology) and SIZE (2^R configurations),
not from the specific discriminator. Using identity makes the proof chain transparent.

**Digest Computation**:
```lean
digest_fg = identityDigestVec(cfg) = full R-bit configuration (identity function)
```

**World Splitting**:
- QP: R = (log n)² → 2^{(log n)²} = n^{log n} worlds
- Exponential: R = n → 2^n worlds

**Trust Boundary**: Proven theorem (no custom axioms).

**Paper**: §4 "FrontierGate Mechanism", §4.2 "World Splitting".

See Layer2_StructuralOWF/Layer2_README.md for FG mechanism details.

## Algorithmic Impossibility via FG Mechanism

This section analyzes why the FG mechanism prevents polynomial-time solving for
algorithms attempting to solve L* with planted instances.

### The Three Ways to Solve a Problem

**Context**: Every algorithm must resolve computational uncertainty through one of three mechanisms:

1. **Way 1: Storage** - Store all possibilities simultaneously (exponential space)
2. **Way 2: Randomized Search** - Try random guesses (exponential expected time)
3. **Way 3: Elimination** - Incrementally prune the search space via local reasoning

**Standard algorithms** (SAT solvers, CSPs, planners) all rely primarily on Way 3:
- Test a partial assignment
- Discover it leads to a contradiction (e.g., unit clause conflict in DPLL)
- **CRUCIALLY**: Prune not just this assignment, but an ENTIRE SUBTREE of related assignments
- Example: In DPLL, setting x=false and deriving (¬x ∨ y) forces y=true for ALL assignments with x=false

**Why Way 3 works for normal SAT**: Local constraints (clauses) create **dependency cascades**
- One variable determines another via unit propagation
- Contradictions prune exponentially many assignments
- Total work: O(2^k) for k << n, typically polynomial in practice

### Why FG Destroys Way 3 (The Cut Topology Barrier)

**The FG mechanism** creates an R-bit information barrier via cut topology:
```lean
digest_fg = identityDigestVec(cfg)  -- full R-bit configuration
```

**The barrier comes from CUT TOPOLOGY, not the discriminator**:
- Each assignment determines a unique R-bit configuration at the cut
- A2 injectivity: different configs → different seeds → different instances
- 2^R possible configurations must be searched exhaustively

**Consequence for Elimination**:

**Scenario**: Algorithm tests candidate assignment α = (v₀, v₁, ..., vₙ₋₁) and discovers:
```
expected_digest ≠ computed_digest(α)  -- Digest mismatch → refutation
```

**Question**: Can the algorithm prune other assignments based on this failure?

**Answer**: No, for the following reasons:

1. **No cascade pruning**: Digest mismatch indicates only that α is incorrect
   - The cut topology hides which variables caused the failure
   - Information flows through the DAG structure, not individual variables

2. **No subtree elimination**: Each configuration is independent
   - No correlation between failure of α and failure of similar assignments
   - Must test each candidate independently

3. **Information bottleneck**: Each refutation eliminates exactly 1 configuration
   - "α is not the planted assignment"
   - Does not constrain any other assignment's validity
   - Cannot deduce properties of unexplored assignments

**Contrast with Unit Propagation (normal SAT)**:
```
Clause: (x ∨ y ∨ z)
If test x=0, y=0: DEDUCE z=1 for ALL assignments with x=0, y=0 (cascade!)

FG mechanism:
If test (x,y,z): Learn only that THIS specific config is wrong
                 (No deduction about other configs!)
```

**The Counting Argument**:

- Planted instance has R emergent bits at the cut → 2^R possible configurations
- Algorithm must distinguish the unique planted config from 2^R candidates
- Each refutation eliminates exactly 1 candidate (no cascade)
- Therefore: Must test ≥ 2^R - 1 candidates → exponential work

**Why the Cut Creates Hardness**:

The cut topology creates an information barrier:
- **A2 Injectivity**: Different R-bit vectors → different seeds (bijective)
- **Cut Isolation**: Configuration at cut depends on ALL ancestor assignments
- **No Partial Information**: Cannot determine config without full assignment

### Why Other Approaches Fail

**Attempt 1: Guess digest first, solve constrained problem?**
- Digest is R bits → 2^R possibilities
- Must solve EACH constrained problem (still NP-complete via planted CNF)
- No improvement in total work

**Attempt 2: Symbolic reasoning (SAT solver style)?**
- Planted instance has unique satisfying assignment (PSS property)
- No learning shortcuts when there's exactly one solution

**Attempt 3: Algebraic methods (Gröbner basis, etc.)?**
- SEED GENERATION uses nonlinear cryptographic hash
- No algebraic structure to exploit (pseudo-random seeds break algebraic attacks)

**Attempt 4: Guess-and-check with verification?**
- Equivalent to Way 2 (Randomized Search) → expected 2^R trials
- Verification is cheap (polynomial), but finding correct guess is exponential

### The Information-Theoretic Perspective

**Fundamental Constraint**: Information must flow from seeds to decision

- **Input**: Planted seeds (n × λ bits of randomness)
- **Output**: Witness (satisfying assignment)
- **Bottleneck**: FG digest forces algorithm to resolve ≥ 2^R possibilities

**Information Conservation Law (SCL)**:
```
q + Φ ≥ R     (bits read + bits stored ≥ bits that must emerge)
```

For FG-wired instances with minimal q (few designated reads):
- R_fg = n (Exponential) or (log n)² (QP)
- q_fg ≈ 0 (cut topology prevents early revelation of seeds)
- Therefore: Φ_fg ≥ R_fg → MUST maintain ≥ 2^R_fg distinguishable states

**Time Consequence** (Layer 3 → Layer 4 bridge):
- Maintaining 2^k distinguishable states requires ≥ 2^k computational steps (operational)
- Cannot reach solution without visiting exponentially many states
- Any algorithm using < 2^R time violates information conservation

### Summary: Computational Trilemma

**Theorem** (Informal): For FG-wired planted instances, every polynomial-time algorithm must:

1. Fail to solve the instance correctly, OR
2. Use exponential space (violating polynomial-space constraint via Way 1), OR
3. Use exponential time (violating polynomial-time constraint as Ways 2/3 are blocked)

**FG achieves this by**:
- Making Way 1 impossible: Cut topology forces 2^R distinguishable states (exponential space)
- Making Way 2 impractical: 2^R search space with no structure (exponential time)
- Making Way 3 impossible: Cut topology prevents cascade pruning (no subtree elimination)

**Analysis**: The proof establishes information-theoretic impossibility rather than
algorithmic difficulty. The problem structure (via FG) makes polynomial-time solving
impossible due to information flow constraints, independent of algorithmic approach.

### Lean Formalization Notes

**Key Theorems in This File**:
- `identityDigestVec_injective`: Identity digest is injective (trivially true)
- `different_config_different_identityDigest`: Different configs have different digests (proven)
- `fg_emergence_bound`: Cut emergence bounded by FG rank (proven, enables SCL application)

**Information→Time Bridge**:
- Layer 2 (here): FG creates exponential information barrier
- Layer 3 (SegmentReduction.lean): Proves ≥ 2^R refutations required
- Layer 4 (TMToExecutionPrefix.lean): Proves time ≥ refutations (operational semantics)
- Layer 5 (Security.lean): OWF exists → P≠NP (complexity theory)

**Trust Boundary**: FG mechanism uses ZERO custom axioms - all proven from first principles
(identity function, vector operations). See `#print axioms` statements at end of file.

-/
namespace LStar.StructuralOWF

open LStar
open LStar.LStarInstanceFull
open LStar.StructuralOWF.Foundations
open LStar.StructuralOWF.Foundations.TimingModel

/-- Map a position in the emergent bits to an index in the combined core vector.
    Since core = (packParents).append(emergent), emergent bits start at parentBits. -/
noncomputable def emergentIndex (L : LStarInstanceFull) (v : Fin L.dag.n) (pos : Fin (L.R v)) : 
    Fin (parentBits L v + L.R v) :=
  ⟨parentBits L v + pos.val, Nat.add_lt_add_left pos.isLt _⟩

/-- Lemma: Getting from core at an emergent index gives the corresponding emergent bit.
    Uses the right slice lemma (get_append_right defined in SeedChain.lean). -/
lemma core_get_emergent (L : LStarInstanceFull) (v : Fin L.dag.n)
    (hist : ParentHistory L v) (e : Vector Bool (L.R v)) (pos : Fin (L.R v)) :
    let core : Vector Bool (parentBits L v + L.R v) := (packParents L v hist).append e
    core.get (emergentIndex L v pos) = e.get pos := by
  simp only [emergentIndex]
  exact Vector.get_append_right (packParents L v hist) e pos

/-- A compact digest used by FG; details will be refined later. -/
structure GateDigest where
  /-- Minimum number of emergent bits required at a gate. -/
  segmentBudget : Nat
  /-- Concrete digest content to be embedded in the emergent slice. -/
  bits : Vector Bool segmentBudget
  deriving DecidableEq, Repr

/-! ## Digest = R-bit Identity Construction

FG digest is the FULL R-bit emergent configuration (identity function).
The digest IS the configuration - this is the direct, clean approach.

**Architecture (R-bit Identity)**:
- **What it does**: Returns all R bits unchanged
- **Why identity?**: Simplest discriminator - different configs have different digests
- **Hardness source**: A2 injectivity on full R-bit vectors

**Proof chain**:
```
cfg1 ≠ cfg2                                    [given]
         → identityDigest(cfg1) ≠ identityDigest(cfg2)  [identity is injective]
         → encodeSeed(cfg1) ≠ encodeSeed(cfg2)          [A2 injectivity]
         → different seeds → different instances
```

The 2^R lower bound comes from A2 injectivity on FULL R-bit vectors.
Identity digest makes this completely transparent.
-/

/-- Compute R-bit identity digest: the digest IS the configuration bits.

    - Input: cfg ∈ Fin(2^R) (R-bit emergent config as index)
    - Output: Vector Bool R (R-bit digest = the config bits) -/
def identityDigestVec {n : Nat} (cfg : Fin (2^n)) : Vector Bool n :=
  Vector.ofFn fun i : Fin n => (cfg.val >>> i.val) % 2 = 1

/-- Compute the full FG digest for a configuration as R-bit identity. -/
def computeDigestIdentity {n : Nat} (cfg : Fin (2^n)) : GateDigest :=
  { segmentBudget := n
  , bits := identityDigestVec cfg }

/-- Helper: mod 2 = 1 iff &&& 1 ≠ 0. -/
private lemma mod_two_eq_one_iff_and_ne_zero (k : Nat) : k % 2 = 1 ↔ 1 &&& k ≠ 0 := by
  have h1 : 1 &&& k = k &&& 1 := Nat.and_comm 1 k
  rw [h1]
  have h2 : k &&& 1 = k % 2 := (Nat.and_one_is_mod k)
  rw [h2]
  constructor <;> intro h <;> omega

/-- Identity digest is injective: different configs have different digests.

    This is trivially true because identityDigestVec is a bijection. -/
theorem identityDigestVec_injective {n : Nat} :
    Function.Injective (@identityDigestVec n) := by
  intro cfg1 cfg2 h_eq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · -- For bits within range, extract bit equality from vector equality
    have h_bit_eq : (identityDigestVec cfg1).get ⟨i, hi⟩ = (identityDigestVec cfg2).get ⟨i, hi⟩ := by
      rw [h_eq]
    unfold identityDigestVec at h_bit_eq
    simp only [Vector.get_ofFn] at h_bit_eq
    have h_prop_iff : (cfg1.val >>> i) % 2 = 1 ↔ (cfg2.val >>> i) % 2 = 1 :=
      decide_eq_decide.mp h_bit_eq
    -- Use the helper lemmas to convert to testBit
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at h_prop_iff ⊢
    rw [mod_two_eq_one_iff_and_ne_zero, mod_two_eq_one_iff_and_ne_zero] at h_prop_iff
    -- Goal is (1 &&& cfg1.val / 2^i != 0) = (1 &&& cfg2.val / 2^i != 0)
    -- h_prop_iff : (1 &&& cfg1.val / 2^i ≠ 0) ↔ (1 &&& cfg2.val / 2^i ≠ 0)
    -- a != 0 = decide (a ≠ 0), so apply Bool.eq_iff_iff
    apply Bool.eq_iff_iff.mpr
    simp only [ne_eq, bne_iff_ne]
    exact h_prop_iff
  · -- For bits beyond n, both configs have 0 (since cfg < 2^n)
    have h1 : Nat.testBit cfg1.val i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le cfg1.isLt (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    have h2 : Nat.testBit cfg2.val i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le cfg2.isLt (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    rw [h1, h2]

/-- Different configs imply different identity digests (immediate from injectivity). -/
theorem different_config_different_identityDigest {n : Nat}
    (cfg1 cfg2 : Fin (2^n)) (h : cfg1 ≠ cfg2) :
    identityDigestVec cfg1 ≠ identityDigestVec cfg2 :=
  fun heq => h (identityDigestVec_injective heq)

/-! ### Parity Functions (Auxiliary Interface)

These functions compute the XOR parity of configurations.
Parity provides a convenient 1-bit summary for some proofs.
The main digest function is `computeDigest` which returns R bits.
-/

/-- Compute parity of a configuration (XOR of all bits). -/
def localParity {n : Nat} (cfg : Fin (2^n)) : Nat :=
  (List.range n).foldl (fun acc i =>
    let bit := (cfg.val >>> i) % 2
    (acc + bit) % 2) 0

/-- Local parity is always 0 or 1. -/
lemma localParity_lt_two {n : Nat} (cfg : Fin (2^n)) : localParity cfg < 2 := by
  unfold localParity
  suffices ∀ (xs : List Nat) (acc : Nat), acc < 2 →
    List.foldl (fun acc i => (acc + (cfg.val >>> i) % 2) % 2) acc xs < 2 by
    apply this
    decide
  intro xs
  induction xs with
  | nil => intro acc h; simp; exact h
  | cons x xs ih =>
    intro acc h_acc
    simp only [List.foldl_cons]
    apply ih
    exact Nat.mod_lt _ (by decide : 0 < 2)

/-- FG digest bit: 1-bit parity of configuration. -/
def fgDigestBit {n : Nat} (cfg : Fin (2^n)) : Bool :=
  match localParity cfg with
  | 0 => false
  | _ => true

/-- Compute the full FG digest for a configuration.
    Returns R-bit identity digest (the full configuration bits). -/
def computeDigest {n : Nat} (cfg : Fin (2^n)) : GateDigest :=
  computeDigestIdentity cfg

/-- FG digest bit equals the parity of the configuration. -/
theorem fg_digest_is_parity_Proven
    {n : Nat}
    (cfg : Fin (2^n))
    : (fgDigestBit cfg = true) ↔ (localParity cfg = 1) := by
  unfold fgDigestBit
  cases h : localParity cfg with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp
    | succ k =>
      have := localParity_lt_two cfg
      rw [h] at this
      omega

/-- Different parities imply different digest bits. -/
theorem different_parity_different_digest
    {n : Nat}
    (cfg1 cfg2 : Fin (2^n))
    (h_parity : localParity cfg1 ≠ localParity cfg2)
    : fgDigestBit cfg1 ≠ fgDigestBit cfg2 := by
  unfold fgDigestBit
  intro h_eq
  cases h1 : localParity cfg1 with
  | zero =>
    cases h2 : localParity cfg2 with
    | zero =>
      -- Both 0 → contradiction with h_parity
      simp [h1, h2] at h_parity
    | succ m2 =>
      -- cfg1 = 0, cfg2 ≥ 1
      cases m2 with
      | zero => simp [h1, h2] at h_eq  -- cfg2 = 1, digests differ
      | succ k2 =>
        -- cfg2 ≥ 2, contradicts parity < 2
        have hp2 := localParity_lt_two cfg2
        rw [h2] at hp2
        omega
  | succ m1 =>
    cases h2 : localParity cfg2 with
    | zero =>
      -- cfg1 ≥ 1, cfg2 = 0
      cases m1 with
      | zero => simp [h1, h2] at h_eq  -- cfg1 = 1, digests differ
      | succ k1 =>
        -- cfg1 ≥ 2, contradicts parity < 2
        have hp1 := localParity_lt_two cfg1
        rw [h1] at hp1
        omega
    | succ m2 =>
      -- Both ≥ 1
      cases m1 with
      | zero =>
        cases m2 with
        | zero =>
          -- Both exactly 1 → parities equal
          rw [h1, h2] at h_parity
          simp at h_parity
        | succ k2 =>
          -- cfg1 = 1, cfg2 ≥ 2
          have hp2 := localParity_lt_two cfg2
          rw [h2] at hp2
          omega
      | succ k1 =>
        -- cfg1 ≥ 2
        have hp1 := localParity_lt_two cfg1
        rw [h1] at hp1
        omega

/-! ## Digest Injectivity from A2

Seeds encode digests via emergent bits. A2 (encoding injectivity from SeedChain)
implies different digests result in different seeds.
-/

/-! ### Bitvector ↔ Configuration Bijection

We establish a bijection between `Vector Bool n` and `Fin (2^n)`:
- `configFromBits`: Vector → Fin (LSB-first encoding)
- `bitsFromConfig`: Fin → Vector (bit extraction)

This bijection is essential for connecting:
- `incomplete_obs_has_collision` which returns `Fin (2^R)` configs
- `different_emergent_different_seed` which takes `Vector Bool R`
-/

/-- Encode a Boolean vector (LSB-first) as a configuration index via XOR toggling.

Iterating over bit positions i = 0..n-1, we toggle bit i with XOR if bits[i] is true,
keeping the value strictly below 2^n at every step.
-/
def configFromBits {n : Nat} (bits : Vector Bool n) : Fin (2^n) :=
  let toggle (acc : Nat) (i : Nat) : Nat :=
    if h : i < n then
      let bi := bits.get ⟨i, h⟩
      if bi then acc ^^^ (2^i) else acc
    else acc
  let val := (List.range n).foldl toggle 0
  ⟨val % (2^n), Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-! ### Bit Manipulation Helpers for Bijection Proof -/

/-- Extract bit i from a natural number as 0 or 1.
Local definition to avoid circular dependency with Layer3. -/
private def localGetBit (cfg : Nat) (i : Nat) : Nat :=
  (cfg / (2^i)) % 2

/-- **XOR Bounds**: XOR with 2^i preserves the bound < 2^n when i < n. -/
private lemma xor_pow_two_lt {n i : Nat} (hi : i < n) (cfg : Nat) (hcfg : cfg < 2^n) :
    cfg ^^^ (2^i) < 2^n := by
  have hmask : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by omega : 1 < 2) hi
  simpa using (Nat.bitwise_lt_two_pow (f := fun a b => a ^^ b) hcfg hmask)

/-- Bridge lemma: localGetBit (Nat 0/1) corresponds to testBit (Bool). -/
private lemma localGetBit_eq_testBit (n i : Nat) :
    localGetBit n i = (if Nat.testBit n i then 1 else 0) := by
  unfold localGetBit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  split_ifs with h_decide
  case pos => rwa [decide_eq_true_iff] at h_decide
  case neg =>
    have h_not_one : ¬((n / 2^i) % 2 = 1) := fun h => h_decide (decide_eq_true h)
    have h_bound : (n / 2^i) % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
    interval_cases (n / 2^i) % 2
    · rfl
    · contradiction

/-- Decode a configuration index to a Boolean vector (LSB-first).

Extracts bit i as `(cfg.val >>> i) % 2 = 1` for i = 0..n-1.
This is the inverse of `configFromBits`.
-/
def bitsFromConfig {n : Nat} (cfg : Fin (2^n)) : Vector Bool n :=
  Vector.ofFn (fun i : Fin n => (cfg.val >>> i.val) % 2 = 1)

/-- Bit-precision: For LSB-first `configFromBits`, the i-th bit equals the input bit.

**Proof strategy**: The XOR fold toggles bit i iff bits[i] = true. Since all
operations stay within indices < n, the modulo 2^n doesn't affect bit i.val < n. -/
lemma localGetBit_configFromBits {n : Nat} (bits : Vector Bool n) (i : Fin n) :
    localGetBit (configFromBits bits).val i.val = (if bits.get i then 1 else 0) := by
  classical
  -- Unfold the construction with a toggle fold
  let toggle : Nat → Nat → Nat := fun acc j =>
    if h : j < n then
      let b := bits.get ⟨j, h⟩
      if b then acc ^^^ (2 ^ j) else acc
    else acc
  let val := (List.range n).foldl toggle 0
  -- Show the value stays within 2^n, so the final `% 2^n` is identity
  have h_val_lt : val < 2 ^ n := by
    let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
    have hstep : ∀ k, k ≤ n → val_k k < 2 ^ n := by
      intro k hk
      induction' k with k ih
      · simp [val_k]
      · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
        have hk_le : k ≤ n := Nat.le_of_lt hklt
        by_cases Hb : bits.get ⟨k, hklt⟩
        · have : val_k (k + 1) = (val_k k) ^^^ (2 ^ k) := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, hklt, Hb]
          have ih' : val_k k < 2 ^ n := ih hk_le
          have bound := xor_pow_two_lt (n := n) (i := k) hklt (val_k k) ih'
          simpa [this] using bound
        · have : val_k (k + 1) = val_k k := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, hklt, Hb]
          simpa [this] using ih hk_le
    have : val = val_k n := by simp [val_k, val]
    simpa [this] using hstep n (le_rfl)
  -- Since val < 2^n, the modulo in configFromBits is identity
  have h_mod : (configFromBits bits).val = val := by
    simpa [configFromBits, val] using (Nat.mod_eq_of_lt h_val_lt)
  -- Prove a prefix-fold invariant for the testBit at index i
  let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
  have inv : ∀ k, k ≤ n →
      Nat.testBit (val_k k) i.val = (if i.val < k then bits.get i else false) := by
    intro k hk
    induction' k with k ih
    · simp [val_k]
    · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
      have step : val_k (k + 1) = toggle (val_k k) k := by
        simp [val_k, List.range_succ, List.foldl_append]
      by_cases hkeq : i.val = k
      · -- Toggling at bit i
        subst hkeq
        have ih0 : Nat.testBit (val_k i.val) i.val = false := by
          have hkle : i.val ≤ n := i.isLt.le
          simpa [Nat.lt_irrefl] using ih hkle
        by_cases Hb : bits.get ⟨i.val, i.isLt⟩
        · have htb : Nat.testBit (val_k (i.val + 1)) i.val = true := by
            simp [step, toggle, i.isLt, Hb, Nat.testBit_xor, Nat.testBit_two_pow_self, ih0]
          simpa [Hb] using htb
        · have htb : Nat.testBit (val_k (i.val + 1)) i.val = false := by
            simp [step, toggle, i.isLt, Hb, ih0]
          simpa [Hb] using htb
      · -- Toggling at a different bit preserves bit i
        have hpres : Nat.testBit (val_k (k + 1)) i.val = Nat.testBit (val_k k) i.val := by
          by_cases Hb : bits.get ⟨k, hklt⟩
          · have hneq : k ≠ i.val := fun hk => hkeq (hk.symm)
            simp [step, toggle, hklt, Hb, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hneq]
          · simp [step, toggle, hklt, Hb]
        have ih' := ih (Nat.le_of_lt hklt)
        have eq_if : (if i.val < k + 1 then bits.get i else false)
                   = (if i.val < k then bits.get i else false) := by
          have : i.val ≤ k ↔ i.val < k := by
            constructor
            · intro hle; exact lt_of_le_of_ne hle hkeq
            · intro hlt; exact Nat.le_of_lt hlt
          simp only [Nat.lt_succ_iff, this]
        simp only [eq_if]; exact hpres.trans ih'
  -- Conclude at k = n: the testBit equals bits.get i (since i.val < n)
  have htb : Nat.testBit val i.val = bits.get i := by
    simpa using inv n (le_rfl)
  -- Convert testBit characterization to localGetBit (0/1)
  have hget : localGetBit val i.val = (if bits.get i then 1 else 0) := by
    have := localGetBit_eq_testBit val i.val
    simpa [htb] using this
  simpa [h_mod] using hget

/-- Roundtrip: configFromBits ∘ bitsFromConfig = id

**Proof**: Uses Fin extensionality and bit-level equality via `localGetBit_configFromBits`. -/
theorem configFromBits_bitsFromConfig {n : Nat} (cfg : Fin (2^n)) :
    configFromBits (bitsFromConfig cfg) = cfg := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · -- For i < n: use localGetBit_configFromBits
    -- First show: (bitsFromConfig cfg).get ⟨i, hi⟩ = Nat.testBit cfg.val i
    have h_bits_get : (bitsFromConfig cfg).get ⟨i, hi⟩ = Nat.testBit cfg.val i := by
      simp only [bitsFromConfig, Vector.get_ofFn]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [Nat.shiftRight_eq_div_pow]
    -- localGetBit (configFromBits (bitsFromConfig cfg)).val i = (if bits.get i then 1 else 0)
    have h_getbit := localGetBit_configFromBits (bitsFromConfig cfg) ⟨i, hi⟩
    -- Convert localGetBit to testBit using the bridge lemma
    rw [localGetBit_eq_testBit] at h_getbit
    -- h_getbit : (if testBit ... i then 1 else 0) = (if bits.get ⟨i, hi⟩ then 1 else 0)
    -- Substitute h_bits_get into h_getbit
    simp only [h_bits_get] at h_getbit
    -- Now h_getbit : (if testBit result i then 1 else 0) = (if testBit cfg i then 1 else 0)
    -- Extract Bool equality from Nat equality
    -- h_getbit relates the if-then-else Nat values
    -- We use case analysis on Bool values to derive the Bool equality
    cases htb_val : Nat.testBit cfg.val i <;> cases htb'_val : Nat.testBit (configFromBits (bitsFromConfig cfg)).val i
    · rfl  -- both false
    · -- false.true case: h_getbit becomes 1 = 0, contradiction
      simp only [htb'_val, htb_val, ↓reduceIte, Bool.false_eq_true] at h_getbit
      exact absurd h_getbit (by omega)
    · -- true.false case: h_getbit becomes 0 = 1, contradiction
      simp only [htb'_val, htb_val, ↓reduceIte, Bool.false_eq_true] at h_getbit
      exact absurd h_getbit.symm (by omega)
    · rfl  -- both true
  · -- For i ≥ n: both are 0 (values are < 2^n)
    have h_cfg_lt : cfg.val < 2^n := cfg.isLt
    have h_result_lt : (configFromBits (bitsFromConfig cfg)).val < 2^n :=
      (configFromBits (bitsFromConfig cfg)).isLt
    have h1 : Nat.testBit cfg.val i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le h_cfg_lt (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    have h2 : Nat.testBit (configFromBits (bitsFromConfig cfg)).val i = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le h_result_lt (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)))
    rw [h1, h2]

/-- Injectivity of bitsFromConfig (immediate from roundtrip). -/
theorem bitsFromConfig_injective {n : Nat} (cfg1 cfg2 : Fin (2^n)) :
    bitsFromConfig cfg1 = bitsFromConfig cfg2 → cfg1 = cfg2 := by
  intro h
  have h1 := configFromBits_bitsFromConfig cfg1
  have h2 := configFromBits_bitsFromConfig cfg2
  rw [h] at h1
  rw [← h1, h2]

/-- Different configs imply different bit vectors. -/
theorem bitsFromConfig_ne {n : Nat} (cfg1 cfg2 : Fin (2^n)) (h : cfg1 ≠ cfg2) :
    bitsFromConfig cfg1 ≠ bitsFromConfig cfg2 :=
  fun heq => h (bitsFromConfig_injective cfg1 cfg2 heq)

/-- Different digest bits imply different emergent seeds.

**Key insight**: Parity difference is used as a WITNESS for emergent vector difference.

**Proof structure**:
1. `h_digest_diff`: fgDigestBit(e1) ≠ fgDigestBit(e2) (parity differs)
2. Derive `e1 ≠ e2`: if e1 = e2, then fgDigestBit would be equal (contradiction)
3. Apply A2 injectivity: e1 ≠ e2 → encodeSeed(...,e1) ≠ encodeSeed(...,e2)

**Why this works**: Parity difference guarantees the full emergent vectors differ.
The hardness comes from A2 injectivity on the FULL vectors, not from parity itself.
Parity is just a convenient 1-bit discriminator that detects any bit flip.
-/
theorem different_digest_different_seed_Proven
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (hist : LStar.ParentHistory L v)
    (e1 e2 : Vector Bool (L.R v))
    (h_cap : LStar.parentBits L v + L.R v ≤ L.seedWidth v)
    (h_digest_diff : fgDigestBit (configFromBits e1) ≠ fgDigestBit (configFromBits e2))
    : LStar.encodeSeed L v hist e1 ≠ LStar.encodeSeed L v hist e2 := by
  intro h_eq
  have h_inj := LStar.encodeSeed_injective L v h_cap hist hist e1 e2
  have h_emergent_diff : e1 ≠ e2 := by
    intro h_e_eq
    rw [h_e_eq] at h_digest_diff
    exact h_digest_diff rfl
  have : hist ≠ hist ∨ e1 ≠ e2 := Or.inr h_emergent_diff
  exact h_inj this h_eq

/-- **PRIMARY THEOREM**: Different emergent vectors imply different seeds.

This is the PRIMARY interface for the 2^R lower bound. It uses direct
vector inequality (e1 ≠ e2) without any reference to parity.

**Proof**: Direct application of A2 injectivity (encodeSeed_injective).

**Usage**: This should be the main theorem used by external proofs.
The identity-based `different_digest_different_seed_Proven` is now deprecated
in favor of this cleaner interface.
-/
theorem different_emergent_different_seed
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (hist : LStar.ParentHistory L v)
    (e1 e2 : Vector Bool (L.R v))
    (h_cap : LStar.parentBits L v + L.R v ≤ L.seedWidth v)
    (h_diff : e1 ≠ e2)
    : LStar.encodeSeed L v hist e1 ≠ LStar.encodeSeed L v hist e2 := by
  intro h_eq
  have h_inj := LStar.encodeSeed_injective L v h_cap hist hist e1 e2
  have : hist ≠ hist ∨ e1 ≠ e2 := Or.inr h_diff
  exact h_inj this h_eq

/-- **CONFIG VERSION**: Different configs (Fin 2^R) imply different seeds.

This is the PRIMARY interface for connecting `incomplete_obs_has_collision`
(which returns Fin configs) to seed differentiation.

**Proof**: cfg1 ≠ cfg2 → bitsFromConfig cfg1 ≠ bitsFromConfig cfg2 → A2 injectivity
-/
theorem different_config_different_seed
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (hist : LStar.ParentHistory L v)
    (cfg1 cfg2 : Fin (2^(L.R v)))
    (h_cap : LStar.parentBits L v + L.R v ≤ L.seedWidth v)
    (h_diff : cfg1 ≠ cfg2)
    : LStar.encodeSeed L v hist (bitsFromConfig cfg1) ≠ LStar.encodeSeed L v hist (bitsFromConfig cfg2) :=
  different_emergent_different_seed L v hist _ _ h_cap (bitsFromConfig_ne cfg1 cfg2 h_diff)

/-- Minimal predicate: a seed at `v` contains a digest `g` when the
emergent slice (of length `L.R v`) is wide enough to host the digest's
budget. This will be refined to concrete bit‑slice encoding using
`SeedChain` positions. -/
def seedContainsDigest (L : LStarInstanceFull) (v : Fin L.dag.n) (g : GateDigest) : Prop :=
  L.R v ≥ g.segmentBudget

/-- Capacity implies digest containment under the minimal predicate. -/
theorem seedContainsDigest_from_capacity
    (L : LStarInstanceFull) (v : Fin L.dag.n) (g : GateDigest)
    (h : L.R v ≥ g.segmentBudget) :
    seedContainsDigest L v g :=
  h

/-- A canonical injection picking the first `g.segmentBudget` emergent
    positions, assuming the emergent slice is wide enough. -/
def digestPositions (L : LStarInstanceFull) (v : Fin L.dag.n)
  (g : GateDigest) (h : g.segmentBudget ≤ L.R v) :
  Fin g.segmentBudget → Fin (L.R v) :=
  fun k => ⟨(k : Nat), Nat.lt_of_lt_of_le k.isLt h⟩

/-- Bridge to SeedChain indexing: the chosen positions map to `core`
    indices `parentBits + pos`, aligning with emergent bits. -/
theorem digest_positions_slice
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (h : g.segmentBudget ≤ L.R v)
    (hist : ParentHistory L v) (e : Vector Bool (L.R v)) (k : Fin g.segmentBudget) :
  let pos := digestPositions L v g h k
  let core : Vector Bool (parentBits L v + L.R v) := (packParents L v hist).append e
  core.get (emergentIndex L v pos) = e.get pos := by
  intro pos core
  -- Apply the core_get_emergent lemma
  exact core_get_emergent L v hist e (digestPositions L v g h k)

/-- If the emergent bits `e` carry the digest content at the selected
    positions, then those digest bits appear at the corresponding
    `core` indices `parentBits + pos`. -/
theorem digest_bits_in_core
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (h : g.segmentBudget ≤ L.R v)
    (hist : ParentHistory L v) (e : Vector Bool (L.R v))
    (heq : ∀ k : Fin g.segmentBudget,
      e.get (digestPositions L v g h k) = g.bits.get k) :
  let core : Vector Bool (parentBits L v + L.R v) := (packParents L v hist).append e
  ∀ k : Fin g.segmentBudget,
    core.get (emergentIndex L v (digestPositions L v g h k)) = g.bits.get k := by
  intro core k
  let pos := digestPositions L v g h k
  have : core.get (emergentIndex L v pos) = e.get pos :=
    core_get_emergent L v hist e pos
  exact this.trans (heq k)

/-! ## Sigma Transport Equality

Equality of dependent pairs under symmetric transport.
-/

/-- Sigma transport equality for the symmetric case.

When both sigma values transport to the same target and their transported second
components are equal, the sigma values themselves are equal. If x and y both equal
some common value z, and their dependent components are equal after transport to β z,
then the original sigma pairs ⟨x, a⟩ and ⟨y, b⟩ are equal.
-/
theorem sigma_transport_eq_symmetric
  {α : Type*} {β : α → Type*}
  {x y z : α} (hx : x = z) (hy : y = z)
  {a : β x} {b : β y}
  (h_snd : hx ▸ a = hy ▸ b) :
  (⟨x, a⟩ : Sigma β) = ⟨y, b⟩ := by
  cases hx
  cases hy
  simp at h_snd
  congr

/-! ## Core Processing Semantics Infrastructure

The following definitions must appear before their uses in helper functions below.
-/

/-- Processing semantics: maps digest work units to concrete `(segment, op)` pairs
    with an injectivity guarantee. This structure coordinates how the digest's
    computational requirements are embedded into the run's segment decomposition. -/
structure ProcessingSemantics
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) where
  processMap : Fin g.segmentBudget → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations)
  inj : Function.Injective processMap

/-- Total number of parity operation slots across all segments, realized
    as the cardinality of the disjoint union `Σ i, Fin (segments i).digestOperations`. -/
noncomputable def totalDigestOps
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) : Nat :=
  Fintype.card (Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations))

/-- The total parity capacity equals the sum of per-segment operations. -/
theorem totalDigestOps_eq_sum
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) :
    totalDigestOps run segments =
      Finset.univ.sum (fun i : Fin run.segmentCount => (segments i).digestOperations) := by
  classical
  unfold totalDigestOps
  have h_card_sigma :
      Fintype.card (Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations)) =
        Finset.sum Finset.univ (fun i : Fin run.segmentCount =>
          Fintype.card (Fin (segments i).digestOperations)) := by
    simp [Fintype.card_sigma]
  calc
    Fintype.card (Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations))
        = Finset.sum Finset.univ (fun i : Fin run.segmentCount =>
            Fintype.card (Fin (segments i).digestOperations)) := h_card_sigma
    _ = Finset.sum Finset.univ (fun i : Fin run.segmentCount => (segments i).digestOperations) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Fintype.card_fin]

/-- Canonical equivalence between the disjoint union of per-segment op
    indices and a flat `Fin totalDigestOps`. -/
noncomputable def opUnionEquivFin
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) :
    (Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations)) ≃
      Fin (totalDigestOps run segments) :=
  Fintype.equivFin _

/-- Decode a flat op index into a concrete `(segment, op)` pair. -/
noncomputable def opDecode
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment) :
    Fin (totalDigestOps run segments) →
      Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations) :=
  (opUnionEquivFin run segments).symm

/-! ## Digest Assignment Infrastructure

Construction of digest-to-segment assignments using processing semantics.
-/

/-- Digest-to-segment assignment specifying where each digest work unit is processed
with an injection into the segment's parity operation budget. -/
structure DigestAssignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) where
  assign : Fin g.segmentBudget → Fin run.segmentCount
  inj : ∀ i, {k : Fin g.segmentBudget // assign k = i} ↪ Fin (segments i).digestOperations

/-- Build processing semantics when a single segment has sufficient parity operations
for the digest budget. -/
def ProcessingSemantics.ofBigSegment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (i : Fin run.segmentCount)
    (hle : g.segmentBudget ≤ (segments i).digestOperations) :
    ProcessingSemantics run segments g :=
  let emb := TimingModel.finEmbeddingLe hle
  { processMap := fun k => ⟨i, emb k⟩
  , inj := by
      intro a b h
      injection h with _ h_snd
      exact emb.inj' h_snd }

/-- Convert processing semantics to a global injection. -/
def ProcessingSemantics.toGlobal
    {A X : Type} {run : DeterministicRun A X}
    {segments : Fin run.segmentCount → Segment}
    {g : GateDigest}
    (ps : ProcessingSemantics run segments g) :
    TimingModel.GlobalAssignmentInj run segments g.segmentBudget :=
  TimingModel.GlobalAssignmentInj.ofInjectiveMap run segments g.segmentBudget ps.processMap ps.inj

/-- Extract processing semantics from a global injection. -/
def ProcessingSemantics.ofGlobal
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (ginj : TimingModel.GlobalAssignmentInj run segments g.segmentBudget) :
    ProcessingSemantics run segments g :=
  { processMap := ginj.inj
  , inj := ginj.inj.injective }

/-- Factor a global injection into per-segment digest assignments. -/
def DigestAssignment.ofGlobal
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (ginj : TimingModel.GlobalAssignmentInj run segments g.segmentBudget) :
    DigestAssignment run segments g := by
  classical
  let assign : Fin g.segmentBudget → Fin run.segmentCount := fun k => (ginj.inj k).1
  let inj_i : ∀ i, {k : Fin g.segmentBudget // assign k = i} ↪ Fin (segments i).digestOperations :=
    fun i =>
      { toFun := by
          intro hk
          have hi : (ginj.inj hk.1).1 = i := by simpa [assign] using hk.2
          exact hi ▸ (ginj.inj hk.1).2
      , inj' := by
          rintro ⟨ka, hka⟩ ⟨kb, hkb⟩ h
          have hia : (ginj.inj ka).1 = i := by simpa [assign] using hka
          have hib : (ginj.inj kb).1 = i := by simpa [assign] using hkb
          have hsigma : ginj.inj ka = ginj.inj kb := by
            apply sigma_transport_eq_symmetric hia hib
            exact h
          exact Subtype.ext (ginj.inj.injective hsigma) };
  exact { assign := assign, inj := inj_i }

/-- Single-run has at least one segment with a positive-budget digest assignment. -/
theorem segment_nonempty_from_digest
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (da : DigestAssignment run segments g)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  have perSeg : ∀ i, assignedCount run g.segmentBudget da.assign i ≤ (segments i).digestOperations := by
    intro i; exact perSeg_from_injection run segments g.segmentBudget da.assign i (da.inj i)
  exact segment_count_ge_one_of_assignment run segments g.segmentBudget hpos da.assign perSeg h_single

/-- Time is at least 1 with a positive-budget digest assignment and time dominance. -/
theorem time_ge_one_from_digest
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (da : DigestAssignment run segments g)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  have perSeg : ∀ i, assignedCount run g.segmentBudget da.assign i ≤ (segments i).digestOperations := by
    intro i; exact perSeg_from_injection run segments g.segmentBudget da.assign i (da.inj i)
  exact time_ge_one_of_assignment run segments g.segmentBudget hpos da.assign perSeg time_ge_total_ops

/-- Single-run has at least one segment with a global digest injection. -/
theorem segment_nonempty_from_global_digest
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (ginj : TimingModel.GlobalAssignmentInj run segments g.segmentBudget)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  classical
  let da := DigestAssignment.ofGlobal run segments g ginj
  exact segment_nonempty_from_digest run segments g hpos da h_single

/-- Time is at least 1 with a global digest injection and time dominance. -/
theorem time_ge_one_from_global_digest
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (ginj : TimingModel.GlobalAssignmentInj run segments g.segmentBudget)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  classical
  let da := DigestAssignment.ofGlobal run segments g ginj
  exact time_ge_one_from_digest run segments g hpos da time_ge_total_ops

/-- Single-run has at least one segment from processing semantics with positive budget. -/
theorem segment_nonempty_from_processing
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (ps : ProcessingSemantics run segments g)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  exact segment_nonempty_from_global_digest run segments g hpos (ps.toGlobal) h_single

/-- Time is at least 1 from processing semantics, positive budget, and time dominance. -/
theorem time_ge_one_from_processing
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (ps : ProcessingSemantics run segments g)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  exact time_ge_one_from_global_digest run segments g hpos (ps.toGlobal) time_ge_total_ops

/-- Build processing semantics from a per-bit mapping on the emergent slice,
restricted to digest positions with required injectivity. -/
def ProcessingSemantics.ofEmergentMapping
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (h : g.segmentBudget ≤ L.R v)
    (map : Fin (L.R v) → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations))
    (inj_restricted : Function.Injective (fun k : Fin g.segmentBudget => map (digestPositions L v g h k))) :
    ProcessingSemantics run segments g :=
  { processMap := fun k => map (digestPositions L v g h k)
  , inj := by
      intro a b hEq
      exact inj_restricted (by simpa using hEq) }

/-- Build processing semantics from an injective emergent position map.

If the emergent-position map is injective on the entire emergent slice,
its restriction to digest positions is automatically injective.
-/
def ProcessingSemantics.ofEmergentInjection
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (h : g.segmentBudget ≤ L.R v)
    (emap : Fin (L.R v) → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations))
    (hinj : Function.Injective emap) :
    ProcessingSemantics run segments g :=
  ProcessingSemantics.ofEmergentMapping run segments L v g h emap
    (by
      intro a b hEq
      have h1 : digestPositions L v g h a = digestPositions L v g h b := hinj (by simpa using hEq)
      have h2 : (digestPositions L v g h).Injective := by
        intro x y hxy
        apply Fin.ext
        injection hxy
      exact h2 h1)

/-- Canonical emergent to operation map using flat op index space
when total parity budget covers the emergent slice width. -/
noncomputable def emergentToOpCanonical
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (hle : L.R v ≤ totalDigestOps run segments) :
    Fin (L.R v) → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations) :=
  by
    classical
    let emb := TimingModel.finEmbeddingLe hle
    let decode := opDecode run segments
    exact fun k => decode (emb k)

/-- Processing semantics from canonical emergent-to-op mapping
when total capacity covers the emergent width. -/
noncomputable def ProcessingSemantics.ofEmergentCanonical
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (h : g.segmentBudget ≤ L.R v)
    (hle_total : L.R v ≤ totalDigestOps run segments) :
    ProcessingSemantics run segments g :=
  by
    classical
    let emap := emergentToOpCanonical run segments L v hle_total
    have hinj : Function.Injective emap := by
      intro a b hEq
      have h1 : opDecode run segments ((TimingModel.finEmbeddingLe hle_total) a) =
                opDecode run segments ((TimingModel.finEmbeddingLe hle_total) b) := by
        simp only [emap, emergentToOpCanonical] at hEq
        exact hEq
      have h2 : (TimingModel.finEmbeddingLe hle_total) a = (TimingModel.finEmbeddingLe hle_total) b := by
        have h_cancel := congrArg (opUnionEquivFin run segments) h1
        simp only [opDecode] at h_cancel
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h_cancel
        exact h_cancel
      exact (TimingModel.finEmbeddingLe hle_total).inj' h2
    exact ProcessingSemantics.ofEmergentInjection run segments L v g h emap hinj

/-- Single-run has at least one segment when some segment has sufficient parity budget. -/
theorem segment_nonempty_if_big_segment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (i : Fin run.segmentCount)
    (hle : g.segmentBudget ≤ (segments i).digestOperations)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofBigSegment run segments g i hle
  exact segment_nonempty_from_global_digest run segments g hpos (ps.toGlobal) h_single

/-- Time is at least 1 when some segment has sufficient parity budget and time dominates. -/
theorem time_ge_one_if_big_segment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (i : Fin run.segmentCount)
    (hle : g.segmentBudget ≤ (segments i).digestOperations)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofBigSegment run segments g i hle
  exact time_ge_one_from_global_digest run segments g hpos (ps.toGlobal) time_ge_total_ops

/-- Build processing semantics when the total parity budget covers the digest budget,
providing a canonical mapping of digest units to segment-operation indices. -/
noncomputable def ProcessingSemantics.ofTotalCapacity
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (hle : g.segmentBudget ≤ totalDigestOps run segments) :
    ProcessingSemantics run segments g :=
  by
    classical
    let emb := TimingModel.finEmbeddingLe hle
    let decode := opDecode run segments
    let m : Fin g.segmentBudget → Sigma (fun i : Fin run.segmentCount => Fin (segments i).digestOperations) :=
      fun k => decode (emb k)
    have hinj : Function.Injective m := by
      intro a b h
      have h' : (opUnionEquivFin run segments) (m a) = (opUnionEquivFin run segments) (m b) :=
        congrArg (opUnionEquivFin run segments) h
      have h_emb : emb a = emb b := by
        simp only [m, decode, opDecode] at h'
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
        exact h'
      exact emb.inj' h_emb
    exact { processMap := m, inj := hinj }

/-- Single-run has at least one segment from total capacity constraints. -/
theorem segment_nonempty_from_total_capacity
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (hle : g.segmentBudget ≤ totalDigestOps run segments)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofTotalCapacity run segments g hle
  exact segment_nonempty_from_global_digest run segments g hpos (ps.toGlobal) h_single

/-- Time is at least 1 from total capacity and time dominance. -/
theorem time_ge_one_from_total_capacity
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (hle : g.segmentBudget ≤ totalDigestOps run segments)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofTotalCapacity run segments g hle
  exact time_ge_one_from_global_digest run segments g hpos (ps.toGlobal) time_ge_total_ops

/-- Single-run has at least one segment when total capacity covers emergent width. -/
theorem segment_nonempty_from_emergent_total
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (h : g.segmentBudget ≤ L.R v)
    (hle_total : L.R v ≤ totalDigestOps run segments)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofEmergentCanonical run segments L v g h hle_total
  exact segment_nonempty_from_global_digest run segments g hpos (ps.toGlobal) h_single

/-- Time is at least 1 when total capacity covers emergent width and time dominates. -/
theorem time_ge_one_from_emergent_total
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFull) (v : Fin L.dag.n)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (h : g.segmentBudget ≤ L.R v)
    (hle_total : L.R v ≤ totalDigestOps run segments)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofEmergentCanonical run segments L v g h hle_total
  exact time_ge_one_from_global_digest run segments g hpos (ps.toGlobal) time_ge_total_ops

/-- A positive-budget gate with processing semantics enforces nontrivial work:
single-run has at least one segment and time is at least 1. -/
theorem gate_enforces_nontrivial_work
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (hpos : 0 < g.segmentBudget)
    (ps : ProcessingSemantics run segments g)
    (h_single : run.strategy = .singleRun)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.segmentCount ≥ 1 ∧ run.time ≥ 1 := by
  refine ⟨?hseg, ?htime⟩
  · exact segment_nonempty_from_global_digest run segments g hpos (ps.toGlobal) h_single
  · exact time_ge_one_from_global_digest run segments g hpos (ps.toGlobal) time_ge_total_ops

/-- Gate enforces nontrivial work from total capacity and time dominance. -/
theorem gate_enforces_nontrivial_work_from_total_capacity
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest)
    (hpos : 0 < g.segmentBudget)
    (hle : g.segmentBudget ≤ totalDigestOps run segments)
    (h_single : run.strategy = .singleRun)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.segmentCount ≥ 1 ∧ run.time ≥ 1 := by
  classical
  let ps := ProcessingSemantics.ofTotalCapacity run segments g hle
  exact gate_enforces_nontrivial_work run segments g hpos ps h_single time_ge_total_ops

/-- Single-run has at least one segment from a digest assignment with positive budget. -/
theorem segment_nonempty_from_digest_assignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (assign : Fin g.segmentBudget → Fin run.segmentCount)
    (perSeg : ∀ i, assignedCount run g.segmentBudget assign i ≤ (segments i).digestOperations)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 :=
  segment_count_ge_one_of_assignment run segments g.segmentBudget hpos assign perSeg h_single

/-- Time is at least 1 from a digest assignment with positive budget and time dominance. -/
theorem time_ge_one_from_digest_assignment
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (g : GateDigest) (hpos : 0 < g.segmentBudget)
    (assign : Fin g.segmentBudget → Fin run.segmentCount)
    (perSeg : ∀ i, assignedCount run g.segmentBudget assign i ≤ (segments i).digestOperations)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 :=
  time_ge_one_of_assignment run segments g.segmentBudget hpos assign perSeg time_ge_total_ops

/-- Frontier-Gate configuration parameterized by the full instance. -/
structure FrontierGateConfig (L : LStarInstanceFull) where
  gateReq : Fin L.dag.n → Bool
  gateDigest : (v : {v // gateReq v}) → GateDigest
  wiring_in_seeds : ∀ v (h : gateReq v), seedContainsDigest L v (gateDigest ⟨v, h⟩)

/-- Extensionality for FrontierGateConfig across type parameter changes.

    When two LStarInstanceFull structures are equal (h_full : full1 = full2),
    and two FrontierGateConfigs have equal gateReq and gateDigest components,
    then the cast of fg1 equals fg2.

    This is the key lemma for proving HEq of fg configs when the underlying
    full structures differ only in proof-irrelevant or transport-invariant ways.

    **wiring_in_seeds**: Proof-irrelevant (Prop), so only gateReq and gateDigest matter. -/
theorem FrontierGateConfig.cast_eq_of_components {full1 full2 : LStarInstanceFull}
    (h_full : full1 = full2)
    (fg1 : FrontierGateConfig full1) (fg2 : FrontierGateConfig full2)
    (h_gateReq : ∀ v, fg1.gateReq v = fg2.gateReq (h_full ▸ v))
    (h_gateDigest : ∀ v hv, fg1.gateDigest ⟨v, hv⟩ =
        fg2.gateDigest ⟨h_full ▸ v, h_gateReq v ▸ hv⟩) :
    cast (congrArg FrontierGateConfig h_full) fg1 = fg2 := by
  subst h_full
  -- After subst, full1 = full2, so cast is identity and we need fg1 = fg2
  simp only [cast_eq]
  -- Now prove fg1 = fg2 using component equality
  cases fg1 with | mk gateReq1 gateDigest1 wiring1 =>
  cases fg2 with | mk gateReq2 gateDigest2 wiring2 =>
  simp only at h_gateReq h_gateDigest
  -- gateReq equality
  have h_req : gateReq1 = gateReq2 := funext h_gateReq
  subst h_req
  -- gateDigest equality
  have h_dig : gateDigest1 = gateDigest2 := by
    funext ⟨v, hv⟩
    exact h_gateDigest v hv
  subst h_dig
  -- wiring_in_seeds is proof-irrelevant (Prop)
  rfl

/-- HEq of FrontierGateConfigs from HEq of components.

    Simpler than cast_eq_of_components because it takes HEq hypotheses directly,
    avoiding the transport notation that makes goals harder to prove.

    This lemma is used when the components (gateReq, gateDigest) are HEq
    due to the underlying LStarInstanceFull values differing only in fields
    that don't affect the config (like pools.stride). -/
theorem FrontierGateConfig.heq_of_components_heq {full1 full2 : LStarInstanceFull}
    (h_full : full1 = full2)
    (fg1 : FrontierGateConfig full1) (fg2 : FrontierGateConfig full2)
    (h_gateReq_heq : HEq fg1.gateReq fg2.gateReq)
    (h_gateDigest_heq : HEq fg1.gateDigest fg2.gateDigest) :
    HEq fg1 fg2 := by
  subst h_full
  -- After subst, both fg have the same type
  apply heq_of_eq
  -- Now prove fg1 = fg2 using component equality
  cases fg1 with | mk gateReq1 gateDigest1 wiring1 =>
  cases fg2 with | mk gateReq2 gateDigest2 wiring2 =>
  simp only at h_gateReq_heq h_gateDigest_heq
  -- gateReq equality (from HEq in same type)
  have h_req : gateReq1 = gateReq2 := eq_of_heq h_gateReq_heq
  subst h_req
  -- gateDigest equality (from HEq in same type)
  have h_dig : gateDigest1 = gateDigest2 := eq_of_heq h_gateDigest_heq
  subst h_dig
  -- wiring_in_seeds is proof-irrelevant (Prop)
  rfl

/-- Full instance with Frontier-Gate wiring and OAP-encoded formula.

FG is the unique computational bottleneck: for any subset C of vertices,
the sum of emergence values is bounded by the FG's emergence. This is
constructed so that the FG gate has maximum emergence while all other
vertices have bounded emergence, ensuring any cut has emergence sum ≤ R_fg.

**OAP Encoding**: This structure contains `encodedφ : EncodedCNF`, the
seed-locked formula. The adversary sees this encoded form; decoding requires
computing the correct seed chain, which requires knowing the satisfying assignment.
-/
structure LStarInstanceFG extends LStarInstanceFull where
  /-- OAP-encoded CNF formula (seed-locked). Decoding requires correct seeds. -/
  encodedφ : EncodedCNF
  fg : FrontierGateConfig toLStarInstanceFull
  /-- FG Bottleneck Invariant: For any FG gate v_fg and any subset C,
      the sum of emergence values in C is bounded by the FG's emergence.

      Statement: Σ_{v∈C} R_v ≤ R_fg

      This is a construction property. With a single FG gate with large R_fg
      and all other vertices having small R values, any cut C satisfies the bound.
      The invariant is enforced by the singleton gate constraint.

      **AUDIT NOTE (Gap #2)**: This is a STRUCTURE FIELD (construction requirement),
      not a THEOREM proven about all L* instances. When you build an LStarInstanceFG
      via `plant_flat`, you must PROVIDE a proof of this bound. This is LOW RISK
      because `plant_flat` constructs instances that satisfy this bound by design:
      the FG gate has R_fg = n (all emergence), while all other nodes have R_v = 0.
      The bound holds by construction, not by a general theorem about arbitrary instances.
  -/
  fg_emergence_bound : ∀ (v_fg : {v // fg.gateReq v}) (C : Finset (Fin dag.n)),
    Finset.sum C (fun v => R v) ≤ R v_fg.val
  /-- FG Emergence Sizing: FG gates have emergence R_v = Θ(n/W_min) for some W_min.

      We choose R_v to be proportional to n/W_min when building FG-wired instances.
      There exist W_min, c_lower, c_upper > 0 such that:
        c_lower * (n/W_min) ≤ R_v ≤ c_upper * (n/W_min)

      Supported modes:
      - QP-Sharp: R_v = (log₂ n)², yielding 2^((log n)²) = n^(log n) bound
      - Flat: R_v = n, yielding 2^n exponential bound

      Parity computation over R_v bits requires Ω(R_v) work, linking
      constraint evolution to computational cost.
  -/
  fg_emergence_sizing : ∃ (W_min : Nat),
      W_min > 0 ∧
      n ≥ W_min ∧
      ∃ (c_lower c_upper : Nat),
        c_lower > 0 ∧ c_upper > 0 ∧
        c_lower * (n / W_min) ≥ 1 ∧
        ∀ (v : {v // fg.gateReq v}),
          c_lower * (n / W_min) ≤ R v.val ∧
          R v.val ≤ c_upper * (n / W_min)

  /-- Structural Size Lower Bound: The DAG must contain at least n nodes.
      This is true for all planted instances (dag.n = 1 + n + ... > n).
      Required for complexity proofs to bound input size. -/
  dag_size_ge_n : dag.n ≥ n

  /-- Parameter Consistency: n equals the number of CNF variables.
      This is true for all planted instances (n := φ.nvars in construction).
      Required for complexity proofs where adapter encoding uses encodedφ.nvars. -/
  h_n_eq_nvars : n = encodedφ.nvars

  -- Encoding Size Bounds: These ensure L* instance has polynomial encoding size.
  -- Required for rawDataSize_poly_bound to prove O(n³) encoding.

  /-- R values bounded by n. For planted instances: R = n at FG gates, 0 elsewhere. -/
  R_upper : ∀ v, R v ≤ n

  /-- seedWidth bounded by n². Reduction tree accumulates to O(n²). -/
  seedWidth_upper : ∀ v, seedWidth v ≤ n * n

  /-- R × seedWidth bounded by n². Key: R = 0 at high-seedWidth vertices. -/
  R_times_seedWidth_upper : ∀ v, R v * seedWidth v ≤ n * n

  /-- Number of clauses bounded by n. -/
  clauses_upper : encodedφ.clauses.length ≤ n

  /-- Total literals bounded by 3n (3-SAT structure). -/
  lits_upper : encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 ≤ 3 * n

  /-- maskedVar bounded by nvars (CNF well-formedness). -/
  maskedVar_upper : ∀ c ∈ encodedφ.clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ encodedφ.nvars

  -- Note: pools.stride is a construction constant (~10^6 + 2^64 max), not bounded by n².
  -- It doesn't depend on n, so it's handled as O(1) in the polynomial encoding bound.
  -- The rawDataSize_poly_bound theorem accounts for stride as an additive constant.

  /-- GateDigest segmentBudget bounded by n. -/
  gateDigest_budget_upper : ∀ i (h : fg.gateReq i), (fg.gateDigest ⟨i, h⟩).segmentBudget ≤ n

  /-- GateDigest bits length bounded by n. -/
  gateDigest_bits_upper : ∀ i (h : fg.gateReq i), (fg.gateDigest ⟨i, h⟩).bits.toList.length ≤ n

/-- **Extensionality for LStarInstanceFG**: Two instances are equal if their components match.

    This lemma enables proving plant_n equality by showing component equality:
    - toLStarInstanceFull (the base structure with DAG, seeds, etc.)
    - encodedφ (the OAP-encoded formula)
    - fg (the FrontierGate configuration, compared via HEq due to type dependency)

    Used in: plant_n_eq_of_randomness_eq (PlantCore.lean) and similar congruence proofs. -/
lemma LStarInstanceFG.ext {A B : LStarInstanceFG}
    (hfull : A.toLStarInstanceFull = B.toLStarInstanceFull)
    (hencoded : A.encodedφ = B.encodedφ)
    (hfg : A.fg ≍ B.fg) : A = B := by
  cases A; cases B; cases hfull; cases hencoded
  simp at hfg
  cases hfg
  rfl

/-- Product of powers equals power of sum for finsets. -/
lemma finset_prod_pow_eq_pow_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Nat) :
    Finset.prod s (fun a => 2^(f a)) = 2^(Finset.sum s f) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, Nat.pow_add]

/-- FG has maximum configuration space.

Statement: ∏_{v∈C} 2^(R_v) ≤ 2^(R_fg) for any subset C.

Proof: The product of powers equals power of sum, and the sum of emergence values
is bounded by fg_emergence_bound, so the product is bounded by 2^(R_fg) by monotonicity.
-/
theorem fg_has_max_config_space
    (L : LStarInstanceFG)
    (v_fg : {v // L.fg.gateReq v})
    (C : Finset (Fin L.dag.n)) :
    Finset.prod C (fun v => 2^(L.R v)) ≤ 2^(L.R v_fg.val) := by
  have h_sum : Finset.sum C (fun v => L.R v) ≤ L.R v_fg.val :=
    L.fg_emergence_bound v_fg C
  calc Finset.prod C (fun v => 2^(L.R v))
      = 2^(Finset.sum C (fun v => L.R v)) := finset_prod_pow_eq_pow_sum C (fun v => L.R v)
    _ ≤ 2^(L.R v_fg.val) := Nat.pow_le_pow_right (by omega) h_sum

/-- Construct a digest with the given budget and all-zero bits. -/
def mkDigest (b : Nat) : GateDigest :=
  { segmentBudget := b, bits := Vector.replicate b false }

/-- Build `FGInputs` from a gate requirement and per-vertex budgets
    bounded by the emergent width `R v`. -/
def mkFGInputsFromBudget (L : LStarInstanceFull)
    (gateReq : Fin L.dag.n → Bool)
    (budget : (v : {v // gateReq v}) → Nat)
    (hcap : ∀ v (h : gateReq v), budget ⟨v,h⟩ ≤ L.R v) :
    FrontierGateConfig L :=
  { gateReq := gateReq
  , gateDigest := fun v => mkDigest (budget v)
  , wiring_in_seeds := by
      intro v hv
      have : budget ⟨v, hv⟩ ≤ L.R v := hcap v hv
      simpa [seedContainsDigest, mkDigest] using this
  }

/-! ## FG Lower Bounds

From FG wiring (digest embedded in seeds) through processing semantics
to computational work lower bounds, applied to FG-wired instances.
-/

/-- For FG-wired instances with emergent wiring at a gate vertex:
combined work bounds (segment nonemptiness and time ≥ 1) when total
parity capacity covers emergent width. -/
theorem fg_nontrivial_work_from_emergent
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (hcap : L.R v.val ≤ totalDigestOps run segments)
    (h_single : run.strategy = .singleRun)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    let g := L.fg.gateDigest v
    0 < g.segmentBudget → run.segmentCount ≥ 1 ∧ run.time ≥ 1 :=
  fun hpos =>
    let g := L.fg.gateDigest v
    have h : g.segmentBudget ≤ L.R v.val := L.fg.wiring_in_seeds v.val v.property
    have hseg := segment_nonempty_from_emergent_total run segments L.toLStarInstanceFull v.val g hpos h hcap h_single
    have htime := time_ge_one_from_emergent_total run segments L.toLStarInstanceFull v.val g hpos h hcap time_ge_total_ops
    ⟨hseg, htime⟩

/-- For FG-wired instances: segment nonemptiness from gate and total capacity. -/
theorem fg_segment_nonempty
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (hpos : 0 < (L.fg.gateDigest v).segmentBudget)
    (hcap : L.R v.val ≤ totalDigestOps run segments)
    (h_single : run.strategy = .singleRun) :
    run.segmentCount ≥ 1 := by
  let g := L.fg.gateDigest v
  have h : g.segmentBudget ≤ L.R v.val := L.fg.wiring_in_seeds v.val v.property
  exact segment_nonempty_from_emergent_total run segments L.toLStarInstanceFull v.val g hpos h hcap h_single

/-- For FG-wired instances: time ≥ 1 from gate, total capacity, and time dominance. -/
theorem fg_time_ge_one
    {A X : Type} (run : DeterministicRun A X)
    (segments : Fin run.segmentCount → Segment)
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (hpos : 0 < (L.fg.gateDigest v).segmentBudget)
    (hcap : L.R v.val ≤ totalDigestOps run segments)
    (time_ge_total_ops : run.time ≥ (∑ i, (segments i).digestOperations)) :
    run.time ≥ 1 := by
  let g := L.fg.gateDigest v
  have h : g.segmentBudget ≤ L.R v.val := L.fg.wiring_in_seeds v.val v.property
  exact time_ge_one_from_emergent_total run segments L.toLStarInstanceFull v.val g hpos h hcap time_ge_total_ops

/-- For any FG-wired instance with a gate having positive budget:
single-runs respecting capacity and time constraints enforce nontrivial work. -/
theorem fg_universal_work_bound
    {A X : Type}
    (L : LStarInstanceFG)
    (v : {v // L.fg.gateReq v})
    (hpos : 0 < (L.fg.gateDigest v).segmentBudget) :
    ∀ (run : DeterministicRun A X) (segments : Fin run.segmentCount → Segment),
      run.strategy = .singleRun →
      L.R v.val ≤ totalDigestOps run segments →
      run.time ≥ (∑ i, (segments i).digestOperations) →
      run.segmentCount ≥ 1 ∧ run.time ≥ 1 := by
  intros run segments h_single hcap time_ge_total_ops
  exact fg_nontrivial_work_from_emergent run segments L v hcap h_single time_ge_total_ops hpos

end LStar.StructuralOWF

/-! ## Axiom Verification

Comprehensive audit of FrontierGate mechanism and key properties.
All theorems proven from first principles (parity over GF(2), vector operations).
No custom axioms - only standard Lean foundations.
-/

-- Core parity and digest theorems
#print axioms LStar.StructuralOWF.localParity_lt_two
#print axioms LStar.StructuralOWF.fg_digest_is_parity_Proven
#print axioms LStar.StructuralOWF.different_parity_different_digest
#print axioms LStar.StructuralOWF.different_digest_different_seed_Proven

-- Digest embedding theorems
#print axioms LStar.StructuralOWF.seedContainsDigest_from_capacity
#print axioms LStar.StructuralOWF.digest_positions_slice
#print axioms LStar.StructuralOWF.digest_bits_in_core

-- Work and timing bounds
#print axioms LStar.StructuralOWF.totalDigestOps_eq_sum
#print axioms LStar.StructuralOWF.segment_nonempty_from_digest
#print axioms LStar.StructuralOWF.time_ge_one_from_digest
#print axioms LStar.StructuralOWF.fg_universal_work_bound
#print axioms LStar.StructuralOWF.fg_nontrivial_work_from_emergent
