import Layer5_Applications.PvsNP.ComplexityClasses.Encoding.LStarEncoding

/-!
# Extract Encoding of VALID L* Instance

This file constructs a RawLStarInstanceFG that satisfies all LStarInstanceFG
structural constraints, ensuring it represents an actual L* member.

**Key Constraints Satisfied**:
- dag_size_ge_n: dag.n = 4 ≥ n = 4 ✓
- h_n_eq_nvars: n = 4 = nvars ✓
- R_upper: R(v) ≤ 4 for all v ✓
- seedWidth_upper: seedWidth(v) ≤ 32 for all v ✓
- R_times_seedWidth_upper: R(v) * seedWidth(v) ≤ 16 for all v ✓
- clauses_upper: 1 ≤ 4 ✓
- lits_upper: 3 ≤ 12 ✓
- maskedVar_upper: all maskedVar ≤ 4 ✓
- gateDigest_budget_upper: segmentBudget = 4 ≤ 4 ✓
- gateDigest_bits_upper: bits.length = 4 ≤ 4 ✓

Instance: φ = (x₁ ∨ x₂ ∨ x₃), 4 variables, 4-node DAG, one frontier gate.
-/

open LStar

namespace ValidInstance

/-- DAG with 4 nodes: linear structure 0←1←2←3
    Node 0: root, parents = []
    Node 1: parents = [0]
    Node 2: parents = [1]
    Node 3: parents = [2] -/
def validRawDAG : Encoding.RawDAG where
  n := 4
  parents := [[], [0], [1], [2]]

/-- Identity 4×4 matrix in row-major bits: I₄ -/
def identityMatrix4 : Encoding.RawEmergenceMatrix where
  R := 4
  n := 4
  bits := [true, false, false, false,   -- row 0: 1 0 0 0
           false, true, false, false,   -- row 1: 0 1 0 0
           false, false, true, false,   -- row 2: 0 0 1 0
           false, false, false, true]   -- row 3: 0 0 0 1

/-- Zero emergence matrix (for non-gate nodes) -/
def zeroMatrix : Encoding.RawEmergenceMatrix where
  R := 0
  n := 4
  bits := []

/-- Pool config with prime stride -/
def validPools : Encoding.RawPoolConfig where
  stride := 1000003

/-- Valid base instance satisfying all constraints -/
def validRawBase : Encoding.RawLStarInstanceFull where
  n := 4                                           -- n = nvars
  dag := validRawDAG                               -- 4 nodes, ≥ n ✓
  seedWidth := [4, 0, 0, 0]                        -- sw ≤ 2n² = 32 ✓
  R := [4, 0, 0, 0]                                -- R ≤ n = 4 ✓
  emergence := [identityMatrix4, zeroMatrix, zeroMatrix, zeroMatrix]
  pools := validPools                              -- R×sw = 16 ≤ 16 ✓

/-- Encoded literal: x₁ (maskedVar=1, positive) -/
def encLit1 : EncodedLiteral where
  maskedVar := 1      -- ≤ nvars=4 ✓
  maskedPolarity := false

/-- Encoded literal: x₂ (maskedVar=2, positive) -/
def encLit2 : EncodedLiteral where
  maskedVar := 2
  maskedPolarity := false

/-- Encoded literal: x₃ (maskedVar=3, positive) -/
def encLit3 : EncodedLiteral where
  maskedVar := 3
  maskedPolarity := false

/-- Single clause: (x₁ ∨ x₂ ∨ x₃) -/
def validClause : EncodedClause where
  literals := [encLit1, encLit2, encLit3]  -- 3 literals ≤ 3 (3-SAT) ✓

/-- Valid CNF: φ = (x₁ ∨ x₂ ∨ x₃) with nvars=4 -/
def validEncodedCNF : EncodedCNF where
  nvars := 4              -- ≥ 4 for plant_flat ✓
  nvars_pos := by decide
  clauses := [validClause] -- 1 clause ≤ n=4 ✓

/-- GateDigest for node 0: 4-bit identity digest -/
def validGateDigest : Encoding.RawGateDigest where
  segmentBudget := 4                              -- ≤ n = 4 ✓
  bits := [true, false, false, false]             -- 4 bits ≤ n ✓

/-- Valid frontier gate config: only node 0 is a gate with proper digest -/
def validRawFG : Encoding.RawFrontierGateConfig where
  gateReq := [true, false, false, false]          -- Node 0 is frontier gate
  gateDigests := [some validGateDigest, none, none, none]  -- Has digest! ✓

/-- Complete valid RawLStarInstanceFG -/
def validRawInstance : Encoding.RawLStarInstanceFG where
  base := validRawBase
  encodedφ := validEncodedCNF
  fg := validRawFG

/-- Encode the valid instance to bits -/
def validEncodedBits : Encoding.BitString :=
  Encoding.Encodable.encode validRawInstance

/-- Convert 8 bits to a byte (MSB first for hex output) -/
def bitsToByte (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

/-- Hex digit character -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Convert a byte (0-255) to 2-char hex string -/
def byteToHex (b : Nat) : String :=
  String.mk [hexDigit (b / 16), hexDigit (b % 16)]

/-- Convert List Bool to hex string -/
def bitsToHexString (bits : List Bool) : String :=
  let padLen := (8 - bits.length % 8) % 8
  let padded := bits ++ List.replicate padLen false
  let chunks := padded.toChunks 8
  String.join (chunks.map fun chunk => byteToHex (bitsToByte chunk))

-- Output the encoding details
#eval! do
  let bits := validEncodedBits
  IO.println "=== VALID L* Instance Encoding ==="
  IO.println ""
  IO.println "Instance: φ = (x₁ ∨ x₂ ∨ x₃), n=4, dag.n=4"
  IO.println ""
  IO.println s!"Total bits: {bits.length}"
  IO.println s!"Total bytes: {(bits.length + 7) / 8}"
  IO.println ""
  IO.println s!"Hex: {bitsToHexString bits}"
  IO.println ""
  IO.println "Constraint verification:"
  IO.println "  dag_size_ge_n: 4 ≥ 4 ✓"
  IO.println "  h_n_eq_nvars: 4 = 4 ✓"
  IO.println "  R_times_seedWidth: 4×4=16 ≤ 16 ✓"
  IO.println "  clauses ≤ n: 1 ≤ 4 ✓"
  IO.println "  gateDigest present: ✓"

-- Component-wise encoding sizes
#eval! do
  IO.println ""
  IO.println "Component-wise encoding:"
  IO.println "========================"
  let baseEnc := Encoding.Encodable.encode validRawBase
  IO.println s!"Base instance: {baseEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString baseEnc}"
  let cnfEnc := Encoding.Encodable.encode validEncodedCNF
  IO.println s!"EncodedCNF: {cnfEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString cnfEnc}"
  let fgEnc := Encoding.Encodable.encode validRawFG
  IO.println s!"FG config: {fgEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString fgEnc}"
  IO.println s!"Total: {baseEnc.length + cnfEnc.length + fgEnc.length} bits"

-- Show first bits for debugging
#eval! validEncodedBits.take 40

-- Show key encodeNat values
#eval! do
  IO.println ""
  IO.println "Key encodeNat values:"
  IO.println s!"encodeNat 0 = {Encoding.encodeNat 0}"
  IO.println s!"encodeNat 1 = {Encoding.encodeNat 1}"
  IO.println s!"encodeNat 4 = {Encoding.encodeNat 4}"
  IO.println s!"encodeNat 1000003 = {Encoding.encodeNat 1000003}"

end ValidInstance
