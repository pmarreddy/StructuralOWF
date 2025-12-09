import Mathlib.Data.List.Basic

/-! ## EncodedCNF: OAP-Encoded SAT Instance

**Purpose**: Represents a CNF formula where all literals are masked (seed-locked).
This is the "ciphertext" form of the problem instance used in L*.

**OAP Mechanism**:
- Plaintext: φ = C₁ ∧ ... ∧ Cₘ
- Encoded: encodedφ = Enc(C₁) ∧ ... ∧ Enc(Cₘ)
- Literal masking: l_encoded = l_plaintext ⊕ mask(seed)

**Security**:
The structure contains NO plaintext information about the formula.
To decode a literal, one must derive the correct seed for the vertex,
which requires knowing the satisfying assignment (circular dependency).
-/

namespace LStar

/-- **Encoded Literal**: A literal masked with OAP.
    
    Contains `maskedVar` and `maskedPolarity` instead of raw values.
    Decoding requires the correct seed to compute the mask. -/
structure EncodedLiteral where
  maskedVar : Nat       -- var ⊕ mask_var
  maskedPolarity : Bool -- polarity ⊕ mask_pol
  deriving DecidableEq, Repr

/-- **Encoded Clause**: A list of encoded literals. -/
structure EncodedClause where
  literals : List EncodedLiteral
  deriving DecidableEq, Repr

/-- **Encoded CNF**: The OAP-encoded formula.
    
    Structurally similar to CNF but with encoded clauses.
    Preserves `nvars` to allow defining the search space size,
    but hides the constraints. -/
structure EncodedCNF where
  nvars : Nat
  nvars_pos : nvars > 0
  clauses : List EncodedClause
  deriving DecidableEq, Repr

end LStar
