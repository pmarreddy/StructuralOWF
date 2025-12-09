import Layer0_Foundations.SCL.NodeData
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! ## Helpers: Infrastructure Lemmas for SCL_node Proof

**Purpose**: Three lemmas that decompose keyedness → exponential bound into logical steps.

**Key Lemmas**:
1. `inject_at`: Keyedness → injection Assign v ↪ State (explicit embedding)
2. `card_le_of_keyed`: Injection → |Assign| ≤ |State| (pigeonhole principle)
3. `card_assign_idx`: |Assign v| = 2^λ (boolean function space cardinality)

**Proof Chain** (used in SCL_node):
```
keyed v → inject_at → (Assign ↪ State)
        → card_le_of_keyed → |Assign| ≤ |State|
        → card_assign_idx → 2^λ ≤ |State| ∎
```

**Trust Boundary**: Pure combinatorics (Mathlib Fintype), zero axioms.

**Paper**: Lemma 7.I steps 1-5.
-/

namespace NodeData

/-- **Keyedness → Injection**: Explicit injective embedding from assignments to states.

    **Mathematical Content**:
    Given a fixed context k ∈ Known and keyedness hypothesis, construct an explicit
    injective function a ↦ state(k, a) from Assign v to v.State.

    **Paper Correspondence** (Lemma 7.I Steps 2-3):
    - Step 2: "Distinct assignments induce distinct Enc tuples → distinct Seed_v values"
    - Step 3: "By Keyedness, different Seed_v → different designated addresses"
    - Result: The partial function a ↦ state(k, a) is injective

    **Type-Theoretic Content**:
    Constructs a term of type `Assign v ↪ v.State` (bundled injection in Mathlib).
    The bundled structure packages:
    - `toFun`: The function a ↦ state(k, a)
    - `inj'`: Proof of injectivity (contrapositive: a₁ ≠ a₂ → state(k,a₁) ≠ state(k,a₂))

    **Proof Strategy**:
    By contradiction—assume h_eq: state(k,a₁) = state(k,a₂) but h_ne: a₁ ≠ a₂.
    Keyedness hypothesis h says a₁ ≠ a₂ → state(k,a₁) ≠ state(k,a₂), contradiction. ∎

    **Design Note**:
    This is a *computational witness*—we explicitly build the injection rather than
    just proving existence. This constructive approach enables later applications to
    extract algorithmic content from the proof.
-/
def inject_at (v : NodeData) (k : v.Known) (h : keyed v) : (Assign v) ↪ v.State :=
{ toFun := fun a => v.state (k, a),  -- The underlying function
  inj' := fun a₁ a₂ h_eq => by        -- Proof of injectivity
    by_contra h_ne                     -- Assume a₁ ≠ a₂ for contradiction
    exact h k a₁ a₂ h_ne h_eq }        -- Apply keyedness to derive contradiction

/-- **Injection → Cardinality**: Pigeonhole principle application.

    **Mathematical Content**:
    The existence of an injection Assign v ↪ v.State implies the cardinality
    inequality |Assign v| ≤ |State v|. This is the classical pigeonhole principle:
    if you can inject n pigeons into m holes, then n ≤ m.

    **Paper Correspondence** (Lemma 7.I Steps 4-5):
    - Step 4: "Different designated projections are simultaneously distinguishable"
    - Step 5: "2^{s_v} worlds map to 2^{s_v} distinct projections → Alt_v ≥ 2^{s_v}"
    - Our formalization: injection → cardinality bound (algebraic consequence)

    **Proof Strategy**:
    Direct application of Mathlib's `Fintype.card_le_of_injective` theorem:
    - Premise: f: A ↪ B (injective function)
    - Conclusion: |A| ≤ |B|
    - Application: Use `inject_at v k h` as the witness injection

    **Classical Reasoning**:
    Uses `classical` tactic to obtain decidability of finite types. This is standard
    in cardinality arguments—we need decidable equality to count elements effectively.

    **Mathematical Note**:
    This is the *only* step where we appeal to counting/cardinality rather than
    type-theoretic structure. The pigeonhole principle bridges pure type theory
    (injective functions) to arithmetic (cardinality inequalities).
-/
lemma card_le_of_keyed (v : NodeData) (k : v.Known) (h : keyed v)
  [Fintype (Assign v)] :
  Fintype.card (Assign v) ≤ Fintype.card v.State := by
  classical  -- Enable decidability for finite cardinality computation
  let _ : Fintype v.State := v.fin_S
  -- Apply pigeonhole: existence of injection (inject_at) implies cardinality bound
  exact Fintype.card_le_of_injective _ (inject_at v k h).inj'

/-- **Boolean Space → Exponential**: Fundamental exponential counting.

    **Mathematical Content**:
    The space of boolean-valued functions on a finite domain I has cardinality 2^|I|.
    This is the fundamental fact underlying all exponential lower bounds in the SCL framework.

    **Proof**:
    For each element i ∈ I, a function f: I → Bool makes a binary choice f(i) ∈ {true, false}.
    With |I| independent binary choices, total functions: 2 × 2 × ... × 2 (|I| times) = 2^|I|.

    **Paper Correspondence** (Lemma 7.I Step 1):
    "By the definition of q_v (first-use, RWA-credited designated reads), there are
    exactly 2^{s_v} feasible worlds consistent with the current transcript prefix at v."

    Our formalization:
    - I = UnknownIdx (the s_v = R_v - q_v unresolved coordinates)
    - f: I → Bool (assignment to unresolved bits)
    - |I → Bool| = 2^|I| (exponential count of feasible worlds)

    **Type-Theoretic Content**:
    This is a pure type-theoretic fact about function spaces—no computational content,
    just cardinality arithmetic. Mathlib's `Fintype.card_fun` provides the general theorem:

    |B^A| = |B|^|A|  (cardinality of function space)

    Specialized to Bool (|Bool| = 2):

    |Bool^I| = 2^|I|

    **Why This Matters**:
    This single equation is the source of ALL exponential lower bounds in complexity theory.
    When λ = |UnknownIdx| grows as Ω(n), we get 2^λ = 2^Ω(n) states—the exponential barrier.

    **Implementation Note**:
    Uses Mathlib's `Fintype.card_fun` theorem directly—no custom proof needed. The
    exponential counting is a built-in mathematical fact in Lean's standard library.
-/
lemma card_assign_idx (v : NodeData) [Fintype v.UnknownIdx] :
  Fintype.card (v.UnknownIdx → Bool) = 2 ^ Fintype.card v.UnknownIdx := by
  classical  -- Standard decidability for finite types
  exact Fintype.card_fun  -- Direct application of |B^A| = |B|^|A| with B = Bool

/- Axiom audits: Trust boundary verification.

   All three lemmas rely only on standard Lean foundations:
   - `propext`: Propositional extensionality
   - `Classical.choice`: Classical axiom of choice (for decidability)
   - `Quot.sound`: Quotient type soundness

   No custom axioms, sorries, or unproven assumptions. These are pure mathematical
   facts from combinatorics and type theory. -/
#print axioms inject_at
#print axioms card_le_of_keyed
#print axioms card_assign_idx

end NodeData
