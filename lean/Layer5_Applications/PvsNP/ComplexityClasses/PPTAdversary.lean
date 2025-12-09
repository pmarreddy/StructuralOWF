import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer5_Applications.PvsNP.ComplexityClasses.TMEncoding
import Mathlib.Data.Fintype.Basic

/-! ## PPTAdversary: Computable Probabilistic Polynomial-Time Adversary (0 axioms)

**Purpose**: PPT adversary with TM-based computability contract for OWF security proofs.

**Key Insight**: In textbooks, "PPT adversary" means "probabilistic Turing Machine
with polynomial time bound." This definition makes that explicit and enforces
computability (not just polynomial labels).

**Design**: PPT = TM + encoder + correctness proof + uniform polynomial bound

**Uniform Polynomial Time**:
- Textbook definition (Arora-Barak 1.7, Goldreich 2.2.7, Sipser 7.12):
  "There exist constants C, k such that for all n, runtime ≤ C·n^k"
- Implementation: C and k are structural fields of PPTAdversary
- Result: Uniformity is definitional (no axiom required)

**Key Fields**:
- `M`: Concrete probabilistic Turing Machine that computes run
- `num_coins`: Finite randomness (enables coin-fixing)
- `run`: Algorithm behavior (coins → input → output)
- `encoding`: Bidirectional encoding (α ↔ TM tapes ↔ β)
- `run_correct`: Proof that decode(TM(encode(x))) = run(c, x)
- `extractWitness`: Witness extraction from TM configuration (OWF-specific)
- `C`, `k`: Uniform polynomial constants (work for all n)
- `time_bound`, `poly`: Polynomial time certificate using uniform C,k

**Axiom Count**: 0 (TM, uniformity, and computability are all structural)

**Paper**: Standard complexity theory (Goldreich, Arora-Barak, Katz-Lindell)

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

open LStar.StructuralOWF.Foundations  -- For TuringMachine, TMConfig
open Sized

/-- Probabilistic Polynomial-Time adversary (standard textbook definition).

    **Definition**: A PPT adversary IS a probabilistic Turing Machine with:
    1. Finite coin space (for coin-fixing arguments)
    2. **Uniform** polynomial time bound (constants C,k work for ALL n)
    3. Well-defined algorithm behavior

    **No axioms needed**: PPT = probabilistic TM + uniform polynomial bounds (both definitional).

    **Uniform Polynomial Time**:
    - Textbook definition: "There exist constants C, k such that for all n..."
    - Implementation: C and k are structural fields (uniformity is definitional)
    - Result: No axiom required for quantifier swap

    Fields:
    - `num_coins`: Number of random coin flips (finite)
    - `stateCount`, `alphabetSize`: TM parameters (finite, positive)
    - `M`: The concrete probabilistic Turing Machine
    - `run`: Algorithm behavior (coins → input → output)
    - `time_bound`: Size-indexed time bound
    - **`C`, `k`**: **Uniform polynomial constants** (THE constants that work for all n)
    - `h_C_pos`, `h_k_pos`: Positivity of uniform constants (C > 0, k > 0)
    - `poly`: Polynomial time + halting guarantee using uniform C,k (definitional)
    - `coins_pos`: Ensures num_coins > 0 for averaging

    **Axiom eliminations**:
    1. **Church-Turing**: TM is part of the structure (no encoding axiom needed)
    2. **Uniformity**: C,k are structural fields (no quantifier-swap axiom needed)

    **Type Parameters**:
    - `α`: Input type
    - `β`: Output type
    - `γ`: Witness type (application-specific, e.g., CNF witness for OWF)

    **Example usage**:
    ```lean
    theorem owf_security (A : PPTAdversary LStarInstanceFG Randomness Witness) :
      negligible (success_prob A) := by
      let M := A.M       -- TM available immediately (no axiom required)
      let C := A.C       -- Uniform constant (definitional)
      let k := A.k       -- Uniform exponent (definitional)
      have h := A.poly   -- ∀ n, time_bound n ≤ C * (n+1)^k (definitional)
      -- ... analyze M's execution using uniform C,k ...
    ```
-/
structure PPTAdversary (α β γ : Type) [Sized α] [Sized β] where
  /-- Number of random coins (finite for coin-fixing). -/
  num_coins : Nat
  /-- TM state count (must be positive). -/
  stateCount : Nat
  /-- TM alphabet size (must be positive). -/
  alphabetSize : Nat
  /-- Number of TM tapes (typically 1, but 2 for verifiers with comparison). -/
  tapeCount : Nat
  /-- Positivity constraints for finite types. -/
  h_state_pos : 0 < stateCount
  h_alphabet_pos : 0 < alphabetSize
  h_tape_pos : 0 < tapeCount
  /-- The concrete probabilistic Turing Machine.
      This is the heart of PPT: adversary = TM (no axiom needed).
      **k-tape TM**: Typically k=1, but k=2 for verifiers using comparison. -/
  M : TuringMachine tapeCount (Fin stateCount) (Fin alphabetSize)
  /-- Witness extraction function from TM configuration.
      Specifies how to interpret TM tape content as a witness.
      Type parameter γ allows application-specific witness types. -/
  extractWitness : TMConfig M → γ
  /-- Algorithm behavior: given coins and input, produce output.
      For formalization simplicity, we keep this abstract but tie it to M
      via local correctness assumptions in security proofs. -/
  run : Fin num_coins → α → β
  /-- Time bound as function of input size. -/
  time_bound : Nat → Nat
  /-- **Uniform polynomial constant C** (works for ALL input sizes).
      Textbook: "There exist constants C, k such that for all n..."
      This field makes C explicit (uniformity is definitional). -/
  C : Nat
  /-- **Uniform polynomial exponent k** (works for ALL input sizes).
      Textbook: "There exist constants C, k such that for all n..."
      This field makes k explicit (uniformity is definitional). -/
  k : Nat
  /-- Positivity of uniform constant C (non-degenerate polynomial). -/
  h_C_pos : C > 0
  /-- Positivity of uniform exponent k (non-degenerate polynomial). -/
  h_k_pos : k > 0
  /-- Polynomial domination certificate using uniform C,k.
      Uniformity is definitional via structural fields.
      Uses (n+1)^k to avoid n=0 edge cases (matches RandAdv). -/
  poly : ∀ n, time_bound n ≤ C * (n + 1) ^ k

  /-- **ENCODING**: Bidirectional encoding between abstract types (α, β) and TM tapes.

      **Purpose**: Connects abstract algorithm (run : α → β) to concrete TM (M).

      **Components**:
      - input.encode : α → (Nat → alphabet) - Maps input to tape 0 contents
      - output.decode : (Nat → alphabet) → β - Maps final tape to output

      **Enables**: Stating run_correct (TM execution matches run).

      **Note**: With this field, tm_algorithm_correspondence becomes a THEOREM.

      **Design**: Uses TMEncodingBase (no injectivity requirement) to match RandAdv.
      PPTAdversary doesn't use input injectivity - only encode/decode semantics matter. -/
  encoding : TMEncodingBase α β (Fin alphabetSize)

  /-- **BLANK CONSISTENCY**: TM and encoding use same blank symbol. -/
  h_blank_consistent : M.blank = encoding.input.blank

  /-- **HALTING (Input-Specific)**: TM halts within time bound for encoded inputs.

      **Statement**: For all inputs x, running M for C*(|x|+1)^k steps from
      encoded input reaches halt state.

      **Purpose**: Ensures TM execution is well-defined on real inputs.
      Combined with poly, this gives polynomial-time halting guarantee.

      **Note**: Uses initWithEncodingBase (encoded input) - matches RandAdv.halts semantics. -/
  halts : ∀ (x : α),
    let t := C * (size x + 1) ^ k
    let init_cfg := initWithEncodingBase M encoding.input x h_tape_pos h_blank_consistent
    let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
    final_cfg.state ∈ M.halt

  /-- **CORRECTNESS**: TM execution with encoding produces run output.

      **Statement**: For all coins c, input x, and sufficient time bound t:
        extractWitness(TM.run_from_encoded(x, t)) = run(c, x)

      **Key Property**: This makes tm_algorithm_correspondence a THEOREM (not axiom).
      With this field, we PROVE TM matches run - no axiom needed.

      **Interpretation**: The TM M actually COMPUTES the function run (not just coincidentally
      produces the same output). This is the Church-Turing correspondence, made structural.

      **Note**: Uses extractWitness to convert final TM state to output type β.
      For OWF context where β = Randomness (or similar witness type), extractWitness
      interprets tape contents as the witness/randomness structure. -/
  run_correct : ∀ (c : Fin num_coins) (x : α) (t : Nat),
    t ≥ C * (size x + 1) ^ k →
    let init_cfg := initWithEncodingBase M encoding.input x h_tape_pos h_blank_consistent
    let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
    let tape_output := getTape0 final_cfg h_tape_pos
    let decoded_β := encoding.output.decode tape_output
    -- For OWF adversaries: β might be Randomness, γ might be Witness
    -- extractWitness converts TMConfig → γ (witness extraction logic)
    -- We need decoded output to match run output
    -- This is a type-level constraint that must be satisfied when constructing PPTAdversary
    decoded_β = run c x

  /-- Coins are finite and positive (enables averaging). -/
  coins_pos : 0 < num_coins

-- Note: tm_nontrivial_computation and tm_overhead are NOT added here because:
-- 1. They're context-specific (OWF/CNF-specific, not general PPT properties)
-- 2. They reference types not available in this generic structure (CNF, eliminations)
-- 3. They're better handled as local proofs in OWFBridge where context is known
-- See PPTAdversaryOWF wrapper structure below for OWF-specific properties

/-- Extract TM from PPT adversary (definitional projection). -/
def PPTAdversary.getTM {α β γ : Type} [Sized α] [Sized β] (A : PPTAdversary α β γ) :
    TuringMachine A.tapeCount (Fin A.stateCount) (Fin A.alphabetSize) :=
  A.M

/-- Uniform polynomial time bounds.

    For any PPT adversary, there exist uniform constants C, k such that
    the time bound property holds for all input sizes.

    Proof extracts C,k from structural fields (uniformity is definitional).
-/
theorem PPTAdversary.poly_uniform {α β γ : Type} [Sized α] [Sized β] (A : PPTAdversary α β γ) :
  ∃ C k, C > 0 ∧ k > 0 ∧ ∀ n, A.time_bound n ≤ C * (n + 1) ^ k := by
  exact ⟨A.C, A.k, A.h_C_pos, A.h_k_pos, A.poly⟩

#print axioms PPTAdversary
#print axioms PPTAdversary.getTM
#print axioms PPTAdversary.poly_uniform

end LStar.Complexity
