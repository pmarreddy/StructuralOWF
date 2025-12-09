import Layer4_Operational.TuringMachine.TuringMachineSemantics
import Layer5_Applications.PvsNP.ComplexityClasses.Sized

/-! ## TMEncoding: Input/Output Encoding for Turing Machines (0 axioms)

**Purpose**: Connect abstract types to TM tape representations.

**Problem**: RandAdv operates on abstract types α, β, but TuringMachines work with
tape alphabets. To enforce computability, we need explicit encoding/decoding.

**Solution**: TMEncoding structure provides:
- encode: α → initial tape configuration
- decode: final tape configuration → β
- Enables stating run_correct: decode(TM(encode(x))) = run(x)

**Design**:
- Generic over TM parameters (states, alphabet)
- Size-preserving: encoded size ≤ C * original size (polynomial overhead)
- Two-tier encoding: Base (no injectivity) and Full (with injectivity)

**Two-Tier Interface**:
- `TMInputEncodingBase`: Core encoding without injectivity requirement
- `TMInputEncoding`: Extends Base with injectivity (for proofs that need it)

This split allows placeholder encodings (constant functions) to satisfy the type
without requiring injectivity proofs, while real algorithms can provide injectivity
when needed for correctness proofs.

**Trust Boundary**: 0 axioms (pure interface definition)

See Layer5_Applications/Layer5_README.md §ComplexityClasses.
-/

namespace LStar.Complexity

open LStar.StructuralOWF.Foundations  -- For TuringMachine, TMConfig
open Sized

/-- Base encoding of type α to TM tape 0 contents (NO injectivity requirement).

    Maps an input value to its tape representation (position → symbol).

    **Properties**:
    - Finite support: Only finitely many positions are non-blank
    - Polynomial overhead: encoding size ≤ C * (size x + 1)^k
    - Deterministic: same input always produces same encoding

    **Usage**: For placeholder/structural encodings where injectivity is not needed.
    Real algorithms that need injectivity should use `TMInputEncoding` instead.
-/
structure TMInputEncodingBase (α : Type) [Sized α] (alphabet : Type) where
  /-- Blank symbol for empty tape positions. -/
  blank : alphabet
  /-- Encode input to tape contents (position → symbol). -/
  encode : α → (Nat → alphabet)
  /-- Minimal support bound: first position where encoding becomes blank. -/
  min_support : α → Nat
  /-- Minimal support specification: encoding is non-blank before min_support, blank after. -/
  min_support_spec : ∀ x i,
    (i < min_support x → encode x i ≠ blank) ∧
    (i ≥ min_support x → encode x i = blank)
  /-- Encoding has finite support (derived from min_support). -/
  finite_support : ∀ x, ∃ N, ∀ i ≥ N, encode x i = blank := by
    intro x
    exists min_support x
    intro i hi
    exact (min_support_spec x i).2 hi
  /-- Encoding overhead is polynomial in input size. -/
  C_encode : Nat
  k_encode : Nat
  size_bounded : ∀ x, min_support x ≤ C_encode * (size x + 1) ^ k_encode

/-- Full encoding of type α to TM tape 0 contents (WITH injectivity).

    Extends `TMInputEncodingBase` with injectivity requirement.

    **Properties** (inherited from Base):
    - Finite support: Only finitely many positions are non-blank
    - Polynomial overhead: encoding size ≤ C * (size x + 1)^k
    - Deterministic: same input always produces same encoding

    **Additional Property**:
    - Injective: different values have different encodings

    **Usage**: For real algorithms where injectivity is needed in correctness proofs
    (e.g., PairEncoding composition, TMComparison, adapter encoding proofs).
-/
structure TMInputEncoding (α : Type) [Sized α] (alphabet : Type)
    extends TMInputEncodingBase α alphabet where
  /-- Encoding is injective: equal encodings imply equal values. -/
  injective : ∀ x y, (∀ i, encode x i = encode y i) → x = y

/-- Convert TMInputEncoding to TMInputEncodingBase (forget injectivity). -/
def TMInputEncoding.toBase {α : Type} [Sized α] {alphabet : Type}
    (enc : TMInputEncoding α alphabet) : TMInputEncodingBase α alphabet :=
  enc.toTMInputEncodingBase

/-- Decoding of TM tape 0 contents to type β.

    Extracts output value from final tape configuration.

    **Properties**:
    - Reads finite prefix: only examines first N positions
    - Deterministic: same tape always produces same output
-/
structure TMOutputDecoding (β : Type) [Sized β] (alphabet : Type) where
  /-- Blank symbol (should match encoder's blank). -/
  blank : alphabet
  /-- Decode tape contents to output. -/
  decode : (Nat → alphabet) → β
  /-- Decoding reads only finite prefix. -/
  reads_finite : ∃ N, ∀ (tape1 tape2 : Nat → alphabet),
    (∀ i < N, tape1 i = tape2 i) → decode tape1 = decode tape2

/-- Base bidirectional encoding for types α and β (NO injectivity requirement).

    Combines base input encoding and output decoding for a TM alphabet.

    **Usage**: For placeholder/structural encodings where injectivity is not needed.
-/
structure TMEncodingBase (α β : Type) [Sized α] [Sized β] (alphabet : Type) where
  input : TMInputEncodingBase α alphabet
  output : TMOutputDecoding β alphabet
  /-- Input and output use same blank symbol. -/
  blank_consistent : input.blank = output.blank

/-- Full bidirectional encoding for types α and β (WITH injectivity).

    Combines input encoding (with injectivity) and output decoding for a TM alphabet.

    **Usage**: For real algorithms where injectivity is needed in correctness proofs.
-/
structure TMEncoding (α β : Type) [Sized α] [Sized β] (alphabet : Type) where
  input : TMInputEncoding α alphabet
  output : TMOutputDecoding β alphabet
  /-- Input and output use same blank symbol. -/
  blank_consistent : input.blank = output.blank

/-- Convert TMEncoding to TMEncodingBase (forget injectivity). -/
def TMEncoding.toBase {α β : Type} [Sized α] [Sized β] {alphabet : Type}
    (enc : TMEncoding α β alphabet) : TMEncodingBase α β alphabet :=
  { input := enc.input.toBase
    output := enc.output
    blank_consistent := enc.blank_consistent }

/-- Extract tape contents from TM configuration (tape 0).

    Helper for stating run_correct property.
-/
def getTape0 {k : Nat} {states alphabet : Type}
    {M : TuringMachine k states alphabet}
    (cfg : TMConfig M)
    (h_k_pos : 0 < k) : (Nat → alphabet) :=
  cfg.tapes ⟨0, h_k_pos⟩

/-- Initialize TM configuration with encoded input on tape 0 (base encoding).

    **Design**: Places encoded input on tape 0, blank on other tapes.
    Uses TMInputEncodingBase to allow placeholder encodings.
-/
def initWithEncodingBase {α : Type} [Sized α] {k : Nat} {states alphabet : Type}
    (M : TuringMachine k states alphabet)
    (enc : TMInputEncodingBase α alphabet)
    (x : α)
    (h_k_pos : 0 < k)
    (h_blank : M.blank = enc.blank) : TMConfig M where
  state := M.q0
  tapes := fun tape_idx =>
    if tape_idx.val = 0 then enc.encode x
    else fun _ => M.blank
  heads := fun _ => 0

/-- Initialize TM configuration with encoded input on tape 0 (full encoding).

    **Design**: Places encoded input on tape 0, blank on other tapes.
    Wrapper around initWithEncodingBase for full TMInputEncoding.
-/
def initWithEncoding {α : Type} [Sized α] {k : Nat} {states alphabet : Type}
    (M : TuringMachine k states alphabet)
    (enc : TMInputEncoding α alphabet)
    (x : α)
    (h_k_pos : 0 < k)
    (h_blank : M.blank = enc.blank) : TMConfig M where
  state := M.q0
  tapes := fun tape_idx =>
    if tape_idx.val = 0 then enc.encode x
    else fun _ => M.blank
  heads := fun _ => 0

-- Axiom Audits
#print axioms TMInputEncodingBase
#print axioms TMInputEncoding
#print axioms TMOutputDecoding
#print axioms TMEncodingBase
#print axioms TMEncoding
#print axioms getTape0
#print axioms initWithEncodingBase
#print axioms initWithEncoding

end LStar.Complexity
