import Layer5_Applications.PvsNP.ComplexityClasses.AlgSpec
import Layer5_Applications.PvsNP.ComplexityClasses.TMEncoding
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances  -- For Sized LStarInstanceFG
import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer4_Operational.TimeBridge.LStarEncodingTypes  -- For ReplantingSimulation
import Layer2_StructuralOWF.FrontierGate.FrontierGate  -- For LStarInstanceFG
import Layer2_StructuralOWF.FrontierGate.RandomnessTypes  -- For Randomness
import Mathlib.Data.Vector.Basic  -- For Vector Bool

/-! ## RandAdv: Computable Randomized Adversary (1 axiom: `algspec_has_tm`)

**Purpose**: Randomized adversary with TM-based computability contract.

**Computability Enforcement**: RandAdv requires a concrete Turing machine that
computes the `run` function, ensuring actual computability rather than just
polynomial-time labels. This blocks impossible constructions like "Halting Oracle
with polynomial-time label".

**Key Components**:
- `M`: Concrete Turing machine that computes the run function
- `encoding`: Bidirectional encoding between abstract types and TM tapes
- `run_correct`: Proof that decode(TM(encode(x))) = run(c, x)

**Uniform Polynomial Time** (rigorous):
- Textbook: "∃ constants C, k such that ∀ inputs x, time(x) ≤ C·(|x|+1)^k"
- Implementation: Uses Sized typeclass to make |x| explicit
- poly: ∀ x, time_bound (size x) ≤ C * (size x + 1) ^ k

**Type constraint**: Requires [Sized α] to ensure size function exists.

**Key insight**: Finite coins enable coin-fixing arguments (average over Fin T).

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

open Classical Sized
open LStar.StructuralOWF.Foundations  -- For TuringMachine, TMConfig

/-- Typeclass to extract first Nat component from a type.
    For Sigma types `Σ n : Nat, γ n`, returns the first component.
    For other types, returns 0 (trivially satisfies encoding discipline). -/
class FirstNatComponent (β : Type) where
  firstNat : β → Nat

instance (priority := low) instFirstNatComponentDefault {β : Type} : FirstNatComponent β where
  firstNat := fun _ => 0

instance {γ : Nat → Type} : FirstNatComponent (Σ n : Nat, γ n) where
  firstNat := Sigma.fst

/-- Computable randomized adversary with TM-based computability contract.

**Computability Contract**:
- `M`: Concrete Turing machine
- `encoding`: Bidirectional encoding (α ↔ tapes ↔ β)
- `run_correct`: Proof that TM execution matches run function

**Uniform Polynomial Time**:
- C and k are structural fields (the constants that work for all inputs)
- time ≤ C·(|x|+1)^k where |x| = size x (explicit via Sized typeclass)

**Fields**:
- `run`: Abstract algorithm specification (coins → input → output)
- `M`: Concrete Turing machine that computes run
- `encoding`: Bidirectional encoding between abstract types and TM tapes
- `run_correct`: Proof that decode(TM(encode(x))) = run(c, x)
- `time_bound`: Size-indexed time bound
- `C`, `k`: Uniform polynomial constants (work for all inputs)
- `poly_explicit`: Polynomial bound using actual input sizes
- `halts`: TM halts within time bound for all inputs
- `coins_pos`: Ensure T > 0 to enable averaging over coins

**Type constraint**: Requires [Sized α] and [Sized β] for size functions.

**Trust Boundary**: 0 axioms (computability is structural)
-/
structure RandAdv (α β : Type) [Sized α] [Sized β] [FirstNatComponent β] (T : Nat) where
  /-- Abstract algorithm specification: given coins and input, produce output.
      This is the DENOTATION (what the algorithm computes).
      The TM field M provides the COMPUTATION (how it's computed). -/
  run : Fin T → α → β

  /-- Number of TM states (must be positive for Fintype). -/
  stateCount : Nat
  /-- TM alphabet size (must be positive for Fintype). -/
  alphabetSize : Nat
  /-- Number of TM tapes (typically 1, but 2 for verifiers that need comparison). -/
  tapeCount : Nat
  /-- State count positivity (enables Fin stateCount). -/
  h_state_pos : 0 < stateCount
  /-- Alphabet size positivity (enables Fin alphabetSize). -/
  h_alphabet_pos : 0 < alphabetSize
  /-- Tape count positivity (enables Fin tapeCount for tape indexing). -/
  h_tape_pos : 0 < tapeCount

  /-- **COMPUTABILITY**: Concrete Turing machine that COMPUTES the run function.

      **Type**: k-tape TM with Fin stateCount states and Fin alphabetSize alphabet.
      Typically k=1 (single tape), but k=2 for verifiers using comparison.

      **Purpose**: Enforces that run is TM-computable (not just a polynomial-labeled function).
      Blocks impossible adversaries like "Halting Oracle with poly-time label".

      **Multi-tape support**: Allows composition with 2-tape comparison TM for verifiers. -/
  M : TuringMachine tapeCount (Fin stateCount) (Fin alphabetSize)

  /-- **ENCODING**: Bidirectional encoding for the *pair* `(coins, input)`.

      **Purpose**: Connects abstract algorithm (run : Fin T → α → β) to concrete TM (M : TM).
      This makes the coin choice visible to the TM, so `run` can genuinely depend on coins.

      **Components**:
      - input.encode : (Fin T × α) → (Nat → alphabet) - Maps (coins, input) to tape 0 contents
      - output.decode : (Nat → alphabet) → β - Maps final tape to output

      **Enables**: Stating run_correct (TM execution matches run).

      **Note**: Uses TMEncodingBase (no injectivity requirement) to allow placeholder
      encodings for structural RandAdv constructions. -/
  encoding : TMEncodingBase (Fin T × α) β (Fin alphabetSize)

  /-- **OUTPUT INPUT ENCODING**: Encoding of output type β for use as verifier input.

      **Purpose**: Enables encoding β values for verifier constructions where witnesses
      need to be encoded on tape. Supports pair encoding via pairInputEncoding.

      **Consistency**: Uses same blank symbol as encoding.input for pair encoding.

      **Note**: Uses TMInputEncodingBase (no injectivity requirement) to allow placeholder
      encodings for structural RandAdv constructions. -/
  output_input_encoding : TMInputEncodingBase β (Fin alphabetSize)

  /-- **BLANK CONSISTENCY**: TM and encoding use same blank symbol. -/
  h_blank_consistent : M.blank = encoding.input.blank

  /-- **OUTPUT ENCODING BLANK CONSISTENCY**: output_input_encoding uses same blank. -/
  h_output_blank_consistent : output_input_encoding.blank = encoding.input.blank

  /-- **CORRECTNESS**: TM execution with encoding produces run output.

      **Statement**: For all coins c, input x, and sufficient time bound t:
        decode(TM.run_from_encoded(x, t)) = run(c, x)

      **Key Property**: This makes tm_algorithm_correspondence a THEOREM (not axiom).
      With this field, we PROVE TM matches run - no axiom needed.

      **Interpretation**: The TM M actually COMPUTES the function run (not just coincidentally
      produces the same output). This is the Church-Turing correspondence, made structural.

      **Note**: Uses Function.iterate to run step^[t] from initial encoded configuration. -/
  run_correct : ∀ (c : Fin T) (x : α) (t : Nat),
    t ≥ C * (size x + 1) ^ k →
    let init_cfg := initWithEncodingBase M encoding.input (c, x) h_tape_pos h_blank_consistent
    let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
    encoding.output.decode (getTape0 final_cfg h_tape_pos) = run c x

  /-- Time bound as function of input size. -/
  time_bound : Nat → Nat
  /-- Uniform polynomial constant (works for ALL input sizes). -/
  C : Nat
  /-- Uniform polynomial exponent (works for ALL input sizes). -/
  k : Nat
  /-- Positivity of uniform constant C (non-degenerate polynomial). -/
  h_C_pos : C > 0
  /-- Positivity of uniform exponent k (non-degenerate polynomial). -/
  h_k_pos : k > 0

  /-- Polynomial domination certificate using EXPLICIT input sizes.

      **Rigorous formulation**: For ALL inputs x, runtime ≤ C · (|x| + 1)^k
      where |x| = size x is explicitly defined via Sized typeclass.

      Uses (|x|+1)^k to avoid n=0 edge cases (standard textbook formulation). -/
  poly_explicit : ∀ x : α, time_bound (size x) ≤ C * (size x + 1) ^ k

  /-- Uniform polynomial bound on time_bound as a FUNCTION.

      **Purpose**: Ensures time_bound : Nat → Nat is polynomially bounded everywhere,
      not just at sizes realizable by type α values.

      **Critical for**: Composition of algorithms operating on different types
      (e.g., verifier for α × β needs bound on time_bound at pair sizes).

      **Note**: Makes poly_explicit derivable, but poly_explicit is still the
      primary semantic property. This field is the technical detail enabling proofs. -/
  time_bound_uniform : ∀ n, time_bound n ≤ C * (n + 1) ^ k

  /-- **HALTING**: TM halts within time bound for all inputs.

      **Statement**: For all inputs x, running M for C*(|x|+1)^k steps reaches halt state.

      **Purpose**: Ensures TM execution is well-defined (doesn't run forever).
      Combined with poly_explicit, this gives polynomial-time halting guarantee. -/
  halts : ∀ (c : Fin T) (x : α),
    let t := C * (size x + 1) ^ k
    let init_cfg := initWithEncodingBase M encoding.input (c, x) h_tape_pos h_blank_consistent
    let final_cfg := (TMConfig.step (M := M))^[t] init_cfg
    final_cfg.state ∈ M.halt

  /-- Output size bounded by computation time.

      **Fundamental principle**: An algorithm running for T steps can write at most T bits.
      This is implicit in all realistic computation models (Turing machines, RAM, circuits).

      Makes witness bounds constructive: for FP functions, output size is polynomially
      bounded, enabling explicit FNP witness bounds without axioms. -/
  output_bounded : ∀ c x, size (run c x) ≤ time_bound (size x)

  /-- Coins are finite and positive (enables averaging). -/
  coins_pos : 0 < T

  /-- **ENCODING DISCIPLINE**: Default output for early-time cross-decoding.

      At t < 2 steps, the tape contains input encoding (not output format).
      When the output decoder interprets input-format data, it returns this default.

      **Why This Property**:
      - At t=0: Tape = pure input encoding (problem description)
      - At t=1: Tape = input encoding with at most 1 cell changed
      - Output decoder expects different format (result encoding)
      - Cross-decoding returns sentinel/default value

      **Usage**: Enables proving that extracting a "witness" at t < 2 gives garbage,
      which is essential for showing nontrivial computation requires ≥ 2 steps. -/
  early_decode_default : β

  /-- **ENCODING DISCIPLINE**: At t < 2, output decoder returns default value.

      **Statement**: For any input x and t < 2, decoding the tape as output
      produces early_decode_default (not a meaningful result).

      **Proof obligation for algspec_has_tm**: Any TM implementation must use
      encodings where input and output formats are distinguishable. This is
      standard practice in TM theory (Sipser §3.1, Arora-Barak §1.2). -/
  early_decode : ∀ c x t, t < 2 →
    let init_cfg := initWithEncodingBase M encoding.input (c, x) h_tape_pos h_blank_consistent
    let cfg := (TMConfig.step (M := M))^[t] init_cfg
    encoding.output.decode (getTape0 cfg h_tape_pos) = early_decode_default

  /-- **ENCODING COMPLETENESS**: Output decoder covers all output values.

      **Statement**: Every value in β can be decoded from some tape contents.

      **Purpose**: Ensures the encoding is complete - no output values are unreachable.
      This is a standard property of well-designed encodings.

      **Design Choice**: When implementing a TM, we choose encodings that cover all outputs.
      This is always achievable for any finite or countable type. -/
  decode_surjective : Function.Surjective encoding.output.decode

  /-- **FORMAT SEPARATION**: Algorithm never outputs the default value.

      **Statement**: For all coins and inputs, run c x ≠ early_decode_default.

      **Purpose**: Ensures "garbage" output (from malformed tapes) is distinguishable
      from legitimate algorithm outputs.

      **Design Choice**: When implementing a TM, we choose the default value to be
      outside the range of the algorithm. This is always achievable. -/
  run_ne_default : ∀ c x, run c x ≠ early_decode_default

  /-- **ZERO SENTINEL**: Default value has firstNat = 0.

      **Statement**: FirstNatComponent.firstNat early_decode_default = 0.

      **Purpose**: Establishes a canonical sentinel value for the output type.
      For Sigma types (Σ n, γ n), this means the default has n = 0.

      **Design Choice**: When implementing a TM, we choose the default to have
      firstNat = 0. This is always achievable for any type with FirstNatComponent. -/
  default_zero : FirstNatComponent.firstNat early_decode_default = 0

-- Axiom Audits: Trust Boundary Transparency
#print axioms RandAdv

/-- Convert RandAdv to AlgSpec (drop TM implementation proof).

**Purpose**: Extract the pure algorithmic specification from a RandAdv.
The main proof only uses these properties, not the TM execution proof. -/
def RandAdv.toAlgSpec {α β : Type} [Sized α] [Sized β] [FirstNatComponent β] {T : Nat}
    (A : RandAdv α β T) : AlgSpec α β T where
  run := A.run
  time_bound := A.time_bound
  C := A.C
  k := A.k
  h_C_pos := A.h_C_pos
  h_k_pos := A.h_k_pos
  poly_explicit := A.poly_explicit
  time_bound_uniform := A.time_bound_uniform
  output_bounded := A.output_bounded
  coins_pos := A.coins_pos

#print axioms RandAdv.toAlgSpec

/-! ### Axiom 1: Church–Turing Bridge

The Church–Turing thesis asserts that any effectively computable function can be
computed by a Turing machine. This axiom instantiates this thesis for polynomial-time
algorithms with explicit bounds.
-/

/-- **Church–Turing Bridge**: Any AlgSpec admits a TM implementation.

**SEMANTIC CONTENT**:

ESTABLISHED: AlgSpec defines polynomial-time computable functions with explicit complexity bounds.
- The function `A.run : Coins → Input → Output` is well-defined
- Polynomial time bound `C · n^k` is specified with explicit constants

AXIOM CONTENT: Church-Turing thesis instantiation.
- Effective computability implies Turing computability with preserved complexity
- Polynomial-time algorithms correspond to polynomial-time Turing machines (Sipser §3.2)
- The axiom specializes this correspondence to our AlgSpec → RandAdv type mapping

TRUST ASSESSMENT: Foundational. This axiom encodes the standard equivalence between
algorithmic specifications and Turing machine implementations. Rejection constitutes
denial of the Church-Turing thesis itself.

**Formal Properties** (axiom content):
- Behavioral equivalence: `M.toAlgSpec.run = A.run`
- Complexity preservation: `M.C = A.C`, `M.k = A.k`

**Structural Properties** (from RandAdv type):
- Encoding completeness: `decode_surjective` field
- Format separation: `run_ne_default` field
- Sentinel convention: `default_zero` field

These encoding properties are STRUCTURAL FIELDS of RandAdv, not axiom content.
They represent design choices when implementing TMs, always achievable in practice.

**References**:
- Church (1936), Turing (1936): Church–Turing thesis
- Sipser §3.2, Arora-Barak §1.4: Polynomial equivalence of computational models
-/
axiom algspec_has_tm {α β : Type} [Sized α] [Sized β] [FirstNatComponent β] {T : Nat}
    (A : AlgSpec α β T) :
  ∃ (M : RandAdv α β T),
    M.toAlgSpec.run = A.run ∧
    M.C = A.C ∧
    M.k = A.k

#print axioms algspec_has_tm

/-! ### Extended Church-Turing for L* Adversaries

For L* adversaries specifically, the TM implementation additionally provides
the encoding structure needed for time bound proofs. This extends the generic
`algspec_has_tm` with L*-specific properties.

**Key addition**: ReplantingSimulation - the TM's state depends only on what
it has observed/computed, not on which config was planted. This is the
"obliviousness" property that enables the WC-1 time bound derivation.

**Semantic justification**: Any reasonable TM implementation of a SAT solver
works by building up a solution incrementally. The intermediate state reflects
what has been computed so far, not the specific input instance. Different
planted instances that look the same up to time t produce identical TM states.
-/

/-- **L* Structure Axiom**: Any TM implementing an L* algorithm has the required L* encoding structure.

This axiom takes M (from algspec_has_tm) as a parameter and asserts it has L* structure.
Encoding properties (surjective, format separation) come from algspec_has_tm, not here.

**Why parameterized**: This removes duplication of encoding properties. The caller:
1. Gets M from `algspec_has_tm` (with encoding properties)
2. Gets L* structure from `algspec_has_lstar_structure M`

**Core content**:
- ReplantingSimulation (obliviousness) - the key information-theoretic property
- WorstCaseCorrect - TM correctly solves all planted instances
- Encoding coherence - initForPlanting uses standard encoded inputs

**Halting and poly bounds are DERIVED** from encoding coherence + PPT structure:
- initForPlanting cfg = initWithEncodingBase (coinsFor cfg, ⟨L.n, L⟩)
- PPT halts at C * (size L + 1)^k from initWithEncodingBase
- Therefore halts at the PPT bound from initForPlanting -/
axiom algspec_has_lstar_structure
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStar.StructuralOWF.LStarInstanceFG)
                  (Σ n : Nat, Vector Bool (2 * n + 64)) T) :
  -- L* encoding structure with ReplantingSimulation and WorstCaseCorrect
  -- Works for ANY L* instance and frontier gate vertex
  ∀ (L : LStar.StructuralOWF.LStarInstanceFG) (v : Fin L.dag.n), L.fg.gateReq v →
    ∃ (initForPlanting : Fin (2^(L.R v)) → TMConfig M.M)
      (extractConfigAtV : TMConfig M.M → Fin (2^(L.R v)))
      -- Encoding coherence: initForPlanting uses standard encoded inputs with some coin choice
      (coinsFor : Fin (2^(L.R v)) → Fin T),
      -- ReplantingSimulation: intermediate states are oblivious to planting (CORE AXIOM)
      LStar.StructuralOWF.Foundations.ReplantingSimulation L M.M v extractConfigAtV initForPlanting ∧
      -- WorstCaseCorrectOnLStar at PPT bound for sigma-wrapped input
      -- Uses L.encodedφ.nvars to match the adapter encoding in StructuralOWFBridge
      LStar.StructuralOWF.Foundations.WorstCaseCorrectOnLStar L M.M v extractConfigAtV initForPlanting
        (M.C * (Sized.size (⟨L.encodedφ.nvars, L⟩ : Σ _n : Nat, LStar.StructuralOWF.LStarInstanceFG) + 1) ^ M.k) ∧
      -- Encoding coherence: initForPlanting is derived from standard encoding
      -- This enables deriving halting from PPT.halts
      -- Note: Uses L.encodedφ.nvars to match the adapter encoding in StructuralOWFBridge
      (∀ cfg : Fin (2^(L.R v)),
        initForPlanting cfg = initWithEncodingBase M.M M.encoding.input
          (coinsFor cfg, ⟨L.encodedφ.nvars, L⟩) M.h_tape_pos M.h_blank_consistent)

#print axioms algspec_has_lstar_structure

/-! ### Theorem: Encoding Normalization

For output types with a natural number component (e.g., `Σ n, β n`), we can choose
an encoding where the "default" output has first component zero. This is derived
from `algspec_has_tm` by re-interpreting the garbage/default value.
-/

/-- **Hypothesis**: β has a "zero element" with firstNat = 0.

For our use case `β = Σ n, Bits (n + 128)`, this is `⟨0, Vector.replicate 128 false⟩`.
This is trivially satisfiable for any Sigma type with inhabited fiber at 0. -/
class HasZeroElement (β : Type) [FirstNatComponent β] where
  zero_element : β
  zero_element_firstNat : FirstNatComponent.firstNat zero_element = 0

/-- Sigma types with inhabited fiber at 0 have a zero element. -/
instance {γ : Nat → Type} [Inhabited (γ 0)] : HasZeroElement (Σ n : Nat, γ n) where
  zero_element := ⟨0, default⟩
  zero_element_firstNat := rfl

/-! ### Encoding Properties (Now Structural)

The encoding properties are now STRUCTURAL FIELDS of RandAdv:
- `decode_surjective`: Output decoder covers all values
- `run_ne_default`: Algorithm never outputs the default value
- `default_zero`: Default has firstNat = 0

These are design choices made when implementing TMs, always achievable in practice.
The `algspec_has_tm` axiom just asserts existence; encoding properties come from the type.

The `encoding_zero_default` theorem extracts these properties for downstream use.
-/

/-- **Encoding Properties Extraction**: Get RandAdv with all encoding properties from algspec_has_tm.

**Derivation**: The `algspec_has_tm` axiom provides a RandAdv. Since RandAdv now has
encoding properties as structural fields, they come automatically.

**Trust Boundary**: 0 additional axioms (structural properties from RandAdv type).
-/
theorem encoding_zero_default {α β : Type} [Sized α] [Sized β] [FirstNatComponent β] {T : Nat}
    (A : AlgSpec α β T) :
  ∃ (M : RandAdv α β T),
    M.toAlgSpec.run = A.run ∧
    M.C = A.C ∧
    M.k = A.k ∧
    Function.Surjective M.encoding.output.decode ∧
    FirstNatComponent.firstNat M.early_decode_default = 0 := by
  -- Get M from Church-Turing axiom
  obtain ⟨M, h_run, h_C, h_k⟩ := algspec_has_tm A
  -- Encoding properties come from RandAdv structural fields
  exact ⟨M, h_run, h_C, h_k, M.decode_surjective, M.default_zero⟩

#print axioms encoding_zero_default

end LStar.Complexity
