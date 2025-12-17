import Layer5_Applications.PvsNP.ComplexityClasses.Encoding.LStarEncoding

/-!
# Extract Encoding of Minimal L* Instance

This file constructs a minimal LStarInstanceFG and extracts its canonical
bitstring encoding for use in the paper's D.5.2 specification.

Minimal instance: φ₀ = (x₁ ∨ x₂ ∨ x₃), single node, I₃ emergence matrix.
-/

open LStar

namespace MinimalInstance

/-- Minimal DAG: 1 node, no parents -/
def minimalRawDAG : Encoding.RawDAG where
  n := 1
  parents := [[]]  -- Node 0 has no parents

/-- I₃ identity matrix in row-major bits: [1,0,0, 0,1,0, 0,0,1] -/
def identityMatrix3 : Encoding.RawEmergenceMatrix where
  R := 3
  n := 3
  bits := [true, false, false,   -- row 0: 1 0 0
           false, true, false,   -- row 1: 0 1 0
           false, false, true]   -- row 2: 0 0 1

/-- Minimal pool config -/
def minimalPools : Encoding.RawPoolConfig where
  stride := 1000003  -- Prime stride

/-- Minimal base instance -/
def minimalRawBase : Encoding.RawLStarInstanceFull where
  n := 3                           -- n_core = 3 variables
  dag := minimalRawDAG
  seedWidth := [6]                 -- seedWidth for node 0
  R := [3]                         -- Emergence rank for node 0
  emergence := [identityMatrix3]   -- One emergence matrix
  pools := minimalPools

/-- Encoded literal: x₁ with maskedVar=1, positive polarity -/
def encLit1 : EncodedLiteral where
  maskedVar := 1
  maskedPolarity := false

/-- Encoded literal: x₂ with maskedVar=2, positive polarity -/
def encLit2 : EncodedLiteral where
  maskedVar := 2
  maskedPolarity := false

/-- Encoded literal: x₃ with maskedVar=3, positive polarity -/
def encLit3 : EncodedLiteral where
  maskedVar := 3
  maskedPolarity := false

/-- Single clause: (x₁ ∨ x₂ ∨ x₃) -/
def minimalClause : EncodedClause where
  literals := [encLit1, encLit2, encLit3]

/-- Minimal CNF: φ₀ = (x₁ ∨ x₂ ∨ x₃) -/
def minimalEncodedCNF : EncodedCNF where
  nvars := 3
  nvars_pos := by decide
  clauses := [minimalClause]

/-- Minimal frontier gate config: node 0 is a gate, no digest needed for minimal -/
def minimalRawFG : Encoding.RawFrontierGateConfig where
  gateReq := [true]      -- Node 0 is a frontier gate
  gateDigests := [none]  -- No digest for minimal instance

/-- Complete minimal RawLStarInstanceFG -/
def minimalRawInstance : Encoding.RawLStarInstanceFG where
  base := minimalRawBase
  encodedφ := minimalEncodedCNF
  fg := minimalRawFG

/-- Encode the minimal instance to bits using LStar's Encodable -/
def minimalEncodedBits : Encoding.BitString :=
  Encoding.Encodable.encode minimalRawInstance

/-- Convert 8 bits to a byte (MSB first) -/
def bitsToByte (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

/-- Hex digit character -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Convert a byte (0-255) to 2-char hex string -/
def byteToHex (b : Nat) : String :=
  String.mk [hexDigit (b / 16), hexDigit (b % 16)]

/-- Convert List Bool to hex string for output (non-recursive) -/
def bitsToHexString (bits : List Bool) : String :=
  let padLen := (8 - bits.length % 8) % 8
  let padded := bits ++ List.replicate padLen false
  let chunks := padded.toChunks 8
  String.join (chunks.map fun chunk => byteToHex (bitsToByte chunk))

-- Output the encoding details
#eval! do
  let bits := minimalEncodedBits
  IO.println s!"Minimal L* Instance Encoding"
  IO.println s!"============================"
  IO.println s!"Total bits: {bits.length}"
  IO.println s!"Total bytes: {(bits.length + 7) / 8}"
  IO.println s!""
  IO.println s!"Hex: {bitsToHexString bits}"
  IO.println s!""
  IO.println s!"First 80 bits:"
  IO.println s!"{bits.take 80}"

-- Also output the raw bit list for verification
#eval! minimalEncodedBits.length
#eval! bitsToHexString minimalEncodedBits

-- Show breakdown of each component's encoding
#eval! do
  IO.println "Component-wise encoding:"
  IO.println "========================"
  -- Base instance encoding
  let baseEnc := Encoding.Encodable.encode minimalRawBase
  IO.println s!"Base instance: {baseEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString baseEnc}"
  -- EncodedCNF encoding
  let cnfEnc := Encoding.Encodable.encode minimalEncodedCNF
  IO.println s!"EncodedCNF: {cnfEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString cnfEnc}"
  -- FG config encoding
  let fgEnc := Encoding.Encodable.encode minimalRawFG
  IO.println s!"FG config: {fgEnc.length} bits"
  IO.println s!"  Hex: {bitsToHexString fgEnc}"
  -- Total
  IO.println s!"Total: {baseEnc.length + cnfEnc.length + fgEnc.length} bits"

-- Show encodeNat examples
#eval! do
  IO.println ""
  IO.println "encodeNat examples:"
  IO.println s!"encodeNat 0 = {Encoding.encodeNat 0}"
  IO.println s!"encodeNat 1 = {Encoding.encodeNat 1}"
  IO.println s!"encodeNat 2 = {Encoding.encodeNat 2}"
  IO.println s!"encodeNat 3 = {Encoding.encodeNat 3}"
  IO.println s!"encodeNat 6 = {Encoding.encodeNat 6}"
  IO.println s!"encodeNat 1000003 = {Encoding.encodeNat 1000003}"

end MinimalInstance
