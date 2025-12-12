import Layer0_Foundations.Base.CNF
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes
import Layer5_Applications.PvsNP.ComplexityClasses.NPDefs
import Layer1_Construction.Core.OAPEncoding
import Layer1_Construction.Core.SeedChain
import Layer1_Construction.Core.InstanceOps
import Infrastructure.Witness.VerifiedWitness
import Layer3_InformationBounds.Randomness.RanksCore

/-! ## LStarNP: L* ∈ NP Membership Proof (Logical NP)

**IMPORTANT**: This file proves `LStar_in_NP : InNP LStarLang`, where `InNP` is the
**logical/extensional NP** definition with NO resource bounds (NPDefs.lean).

**What this proves:**
- ✅ L* has witness type `Witness`
- ✅ L* has verifier relation `LStarVerifier`
- ✅ Correctness: `L x ↔ ∃ w, LStarVerifier L w`

**What this does NOT prove:**
- ❌ Polynomial-time verification (not part of `InNP` definition)
- ❌ Polynomial witness size bounds (not part of `InNP` definition)
- ❌ `InNP_Alg` membership (complexity-theoretic NP with resource bounds)

**Design Choice - Generic FNP→NP Tool (Instantiated with L*):**

The P≠NP bridge (ParametricBitstringBridge.lean) does NOT use this theorem directly.
Instead, it uses a **generic theorem as a proof tool**, then instantiates with L*:

1. **Generic tool**: `prefixLang_in_np_parametric` proves
   "ANY FNP relation → NP language with poly bounds" (standard textbook result)

2. **L*-specific instantiation**: Plug in L*'s FNP structure R_Lstar
   - R_Lstar built from: Plant, SeedChain, A1-A5, FG wiring (Layers 0-2)
   - h_R_fnp : InFNP_parametric_bits wlen_Lstar R_Lstar (L*-specific!)

3. **Result**: L* ∈ NP with polynomial bounds (via instantiation, not generic claim)

**Why this architecture:**
- More modular: Generic theorem is reusable proof machinery (like calculus)
- NOT claiming: "All NP has L* structure" or any property of generic NP languages
- Standard technique: Use general tools, instantiate with specific construction
- All hardness comes from L*-specific properties (SCL, exponential bounds)

**What's proven elsewhere (L*-specific):**
- L* verifier is polynomial-time (by construction, Layers 1-2)
- L* witness size is polynomial (by construction, Layers 1-2)
- L* has exponential lower bound (SCL + information theory, Layers 2-4)
- Generic FNP → NP tool (`prefixLang_in_np_parametric` - textbook result)

**Paper Correspondence**: §10.1 (L* ∈ NP) proves this with explicit resource bounds.
Lean uses generic parametric approach instead (same end result, different structure).

**Trust Boundary**: Axiom-free (only standard Lean foundations).

See Layer3_InformationBounds/Layer3_README.md for context.
-/

namespace LStar.StructuralOWF.Decision

open LStar
open LStar.StructuralOWF
open LStar.Complexity

/-- Helper: Extract entropy from witness for seed computation.

    **R-bit Layout**: W.digestBits is a flat list of ALL R bits for each gate:
    [gate0_bit0, gate0_bit1, ..., gate0_bitR-1, gate1_bit0, ...]

    **Note on 2^R Hardness**: The R bits at FG gates create the information-theoretic
    bottleneck, but NOT by being independent secrets. The digest is deterministically
    derived from the assignment. The 2^R lower bound comes from SCL (Layer 0), which
    proves any algorithm must maintain 2^R distinguishable states to correctly
    traverse the FG gate. See SCLNode.lean for the pigeonhole argument.

    **Profile Parameter**: Determines R computation (default: exponential). -/
def entropyFromWitness (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential)
    (v : Fin L.dag.n) : Seed (L.seedWidth v) :=
  -- R = emergence rank at FG gates (= digest bits per gate)
  -- Computed via profile-specific formula for consistency
  let R := Foundations.computeR profile L.n
  if v.val == 0 then
    -- Source
    LStar.ofBits _ (fun _ => false)
  else if h_var : v.val <= L.n then
    -- Variable: use assignment bit
    let varIdx := v.val - 1
    let bit := if h : varIdx < L.n then W.assignment ⟨varIdx, h⟩ else false
    LStar.ofBits _ (fun i => if i.val == 0 then bit else false)
  else if L.fg.gateReq v then
    -- FG Gate: use ALL R bits from digestBits
    -- (derived from assignment - consistency required for correct decoding)
    let clause_start := 1 + L.n
    let gate_idx := v.val - clause_start
    -- Use ONLY the first R bits of the seed from digestBits
    LStar.ofBits _ (fun i =>
      if i.val < R then
        let bit_idx := gate_idx * R + i.val
        if h : bit_idx < W.digestBits.length then
          W.digestBits.get ⟨bit_idx, h⟩
        else
          false
      else
        false)
  else
    -- Other
    LStar.ofBits _ (fun _ => false)

/-- Seed width function for clause indices in L*.

    Maps clause index i to the seed width of the corresponding DAG vertex. -/
def clauseSeedWidthFn (L : LStarInstanceFG) (i : Fin L.encodedφ.clauses.length) : Nat :=
  if h : 1 + L.n + i.val < L.dag.n then
    L.seedWidth ⟨1 + L.n + i.val, h⟩
  else
    0

/-- Decision language: does `L : LStarInstanceFG` admit a witness whose
assignment satisfies its CNF?

**Profile Parameter**: Determines R computation (default: exponential). -/
def LStarLang (profile : Foundations.EmergenceProfile := .exponential) : LStarInstanceFG → Prop :=
  fun L => ∃ W : Witness L.n,
    -- Compute seeds
    let entropy := entropyFromWitness L W profile
    let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull entropy
    -- Decode φ using dependent seed widths
    let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn L i) := fun i =>
      if h : 1 + L.n + i.val < L.dag.n then
        -- Cast the seed to the expected type (they have equal widths by definition of clauseSeedWidthFn)
        have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn L i := by simp [clauseSeedWidthFn, h]
        h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
      else
        LStar.ofBits _ (fun _ => false)
    let φ := LStar.OAP.decodeWithOAPDep L.encodedφ (clauseSeedWidthFn L) getSeed
    -- Check satisfaction (use infinite extension of assignment)
    φ.satisfies W.assignmentInf

/-- **Basic Verifier**: Check CNF satisfaction only.

    **Used for**: NP membership proof (simple, efficient).

    **Note**: This verifier is sufficient for showing L* ∈ NP, but not sufficient
    for OWF security (which requires digest checking).

    **Profile Parameter**: Determines R computation (default: exponential). -/
def LStarVerifier (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential) : Prop :=
  -- Compute seeds from witness
  let entropy := entropyFromWitness L W profile
  let seeds := LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull entropy

  -- Decode φ using dependent seed widths
  let getSeed : (i : Fin L.encodedφ.clauses.length) → LStar.Seed (clauseSeedWidthFn L i) := fun i =>
    if h : 1 + L.n + i.val < L.dag.n then
      have h_eq : L.seedWidth ⟨1 + L.n + i.val, h⟩ = clauseSeedWidthFn L i := by simp [clauseSeedWidthFn, h]
      h_eq ▸ seeds ⟨1 + L.n + i.val, h⟩
    else
      LStar.ofBits _ (fun _ => false)

  let φ := LStar.OAP.decodeWithOAPDep L.encodedφ (clauseSeedWidthFn L) getSeed

  -- Check satisfaction (use infinite extension of assignment)
  φ.satisfies W.assignmentInf

/-- **Canonical Verifier**: Check CNF satisfaction AND digest consistency.

    **Algorithm V from paper** (Appendix C.2.ACC-logical):
    1. Check W.digestBits = digestsFromAssignment (digest matches assignment)
    2. Check W.assignment satisfies decoded φ (using FG-aware decoding)

    **Used for**: OWF security proof (witness uniqueness).

    **Digest Consistency Check**: The digest check ensures the witness is
    well-formed: W.digestBits must match what the assignment produces.
    This is a CONSISTENCY check, not an independent search dimension.

    **Where 2^R Hardness Comes From**: The 2^R lower bound is proven by SCL
    (Semantic Conservation Law, Layer 0). SCL shows that any algorithm solving
    L* must maintain ≥2^R distinguishable states to correctly compute seeds
    at the FG gate. This is a theorem about algorithmic state complexity,
    not an extra search enforced by the verifier.

    **Key Distinction**:
    - Verifier checks: consistency (digest derived from assignment)
    - SCL proves: algorithmic complexity (2^R states needed)

    **Profile Parameter**: Determines R computation (default: exponential).
-/
def LStarCanonicalVerifier (L : LStarInstanceFG) (W : Witness L.n)
    (profile : Foundations.EmergenceProfile := .exponential) : Prop :=
  -- Digest consistency: W.digestBits must match what assignment produces
  W.digestBits = Foundations.digestsFromAssignment L W.assignment ∧
  -- Satisfiability: decoded φ (using consistent seeds) must be satisfied
  LStarVerifier L W profile

/-- **Logical NP Membership**: `LStarLang ∈ InNP` (extensional, no resource bounds).

This proves L* has the **structure** of an NP language (witness type + verifier relation)
but does NOT prove polynomial resource bounds (time/witness size).

**NOT used directly in P≠NP proof** - see file header for generic parametric approach.

For complexity-theoretic NP with resource bounds, see:
- `InNP_Alg` definition (ComplexityClasses.lean)
- `prefixLang_in_np_parametric` (ParametricBitstringBridge.lean) -/
theorem LStar_in_NP : InNP LStarLang := by
  refine ⟨?cert⟩
  -- Use Sigma type to bundle n with witness, since VerifierCert needs a fixed Type
  refine ⟨Σ n, Witness n, fun L ⟨n, W⟩ =>
    if h : n = L.n then LStarVerifier L (h ▸ W) else False, ?_⟩
  intro L
  constructor
  · intro ⟨W, hW⟩
    refine ⟨⟨L.n, W⟩, ?_⟩
    simp only [dif_pos rfl]
    exact hW
  · intro ⟨⟨n, W⟩, hW⟩
    by_cases h : n = L.n
    · simp only [h, dif_pos rfl] at hW
      exact ⟨h ▸ W, hW⟩
    · simp only [h, dif_neg h] at hW
      exact False.elim hW

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms LStar_in_NP

end LStar.StructuralOWF.Decision
