import Layer0_Foundations.Base.CNF
import Layer0_Foundations.Base.EncodedCNF
import Layer0_Foundations.Base.FiniteEncoding
import Layer1_Construction.Core.Pools

/-! ## OAPEncoding: Overlay-as-Problem Encoding Logic

**Purpose**: Implements the OAP masking mechanism that hides the CNF structure.

**Mechanism**:
- Each literal is masked using a seed-dependent value.
- The mask is derived deterministically from the seed, clause index, and literal index.
- Uses bounded additive masking: `maskedVar = (lit.var + mask) % (nvars + 1)`
- This ensures `maskedVar ≤ nvars` for polynomial encoding bounds.

**Dependencies**:
- Depends on `Pools.hashSeed` for the PRF/Hash primitive.
- Independent of `LStarInstance` to avoid circular imports.
-/

namespace LStar.OAP

open LStar

/-- Compute the mask for a literal at a specific position.
    
    **Inputs**:
    - `seed`: The seed for the clause (from the DAG).
    - `clauseIdx`: Index of the clause in the CNF.
    - `litIdx`: Index of the literal within the clause.
    
    **Output**:
    - `(maskVar, maskPol)`: Masks for the variable index and polarity.
    
    **Derivation**:
    - Uses `PoolConfig.hashSeed` (simple integer value of seed).
    - Mixes with indices using large primes to scatter bits.
    - `maskVar`: `hash + clauseIdx * 997 + litIdx * 991`
    - `maskPol`: `maskVar` parity (odd = true, even = false)
-/
def computeLiteralMask {w : Nat} (seed : Seed w) (clauseIdx litIdx : Nat) : (Nat × Bool) :=
  let h := PoolConfig.hashSeed seed
  -- Deterministic mixing
  let mix := h + clauseIdx * 997 + litIdx * 991
  (mix, (mix % 2) == 1)

/-- Encode a single literal using OAP masking.

    Uses bounded additive masking: `maskedVar = (lit.var + mask) % (nvars + 1)`.
    This ensures `maskedVar ≤ nvars` for polynomial encoding bounds.

    **Precondition**: `lit.var < nvars` for correct roundtrip. -/
def encodeLiteral {w : Nat} (lit : Literal) (seed : Seed w) (clauseIdx litIdx : Nat) (nvars : Nat) : EncodedLiteral :=
  let (maskVar, maskPol) := computeLiteralMask seed clauseIdx litIdx
  let bound := nvars + 1
  { maskedVar := (lit.var + maskVar) % bound
    maskedPolarity := xor lit.polarity maskPol }

/-- Decode a single literal using the correct seed.

    Uses modular subtraction to recover the original variable index:
    `var = (maskedVar + (nvars + 1) - (mask % (nvars + 1))) % (nvars + 1)` -/
def decodeLiteral {w : Nat} (enc : EncodedLiteral) (seed : Seed w) (clauseIdx litIdx : Nat) (nvars : Nat) : Literal :=
  let (maskVar, maskPol) := computeLiteralMask seed clauseIdx litIdx
  let bound := nvars + 1
  let maskMod := maskVar % bound
  { var := (enc.maskedVar + bound - maskMod) % bound
    polarity := xor enc.maskedPolarity maskPol }

/-! ### Involution Lemmas

These lemmas establish that bounded additive masking is invertible. -/

/-- Bool.xor is self-inverse: (a ⊕ m) ⊕ m = a -/
theorem Bool.xor_self_inverse (a m : Bool) : xor (xor a m) m = a := by
  cases a <;> cases m <;> rfl

/-- Modular additive masking roundtrip: ((v + m) % b + b - (m % b)) % b = v when v < b.

    This is the key arithmetic lemma for the bounded OAP encoding. -/
theorem mod_add_sub_roundtrip (v m b : Nat) (hv : v < b) (hb : 0 < b) :
    ((v + m) % b + b - (m % b)) % b = v := by
  have h_mod_lt : (v + m) % b < b := Nat.mod_lt _ hb
  have h_maskMod_lt : m % b < b := Nat.mod_lt _ hb
  have h_ge : (v + m) % b + b ≥ m % b := by omega
  -- Key insight: (v + m) % b = (v % b + m % b) % b = (v + m % b) % b (since v < b)
  have h_mod_add : (v + m) % b = (v + m % b) % b := by
    have h1 : (v + m) % b = ((v % b) + (m % b)) % b := Nat.add_mod v m b
    have h2 : v % b = v := Nat.mod_eq_of_lt hv
    rw [h1, h2]
  rw [h_mod_add]
  -- Now: ((v + m % b) % b + b - m % b) % b = v
  -- Case split: v + m % b < b or v + m % b ≥ b
  by_cases h_case : v + m % b < b
  · -- Case: v + m % b < b, so (v + m % b) % b = v + m % b
    have h_inner : (v + m % b) % b = v + m % b := Nat.mod_eq_of_lt h_case
    rw [h_inner]
    -- Now: (v + m % b + b - m % b) % b = v
    have h_simp : v + m % b + b - m % b = v + b := by omega
    rw [h_simp]
    -- (v + b) % b = v % b = v since v < b
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hv]
  · -- Case: v + m % b ≥ b, so (v + m % b) % b = v + m % b - b
    push_neg at h_case
    have h_lt : v + m % b < b + b := by
      have : m % b < b := Nat.mod_lt m hb
      omega
    -- When b ≤ x < 2*b, x % b = x - b
    have h_inner : (v + m % b) % b = v + m % b - b := by
      have h_ge : v + m % b ≥ b := h_case
      have h_sub_lt : v + m % b - b < b := by omega
      rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt h_sub_lt]
    rw [h_inner]
    -- Now: (v + m % b - b + b - m % b) % b = v
    have h_simp : v + m % b - b + b - m % b = v := by omega
    rw [h_simp, Nat.mod_eq_of_lt hv]

/-- Literal roundtrip: decode(encode(lit)) = lit when lit.var < nvars.

    **Precondition**: `lit.var < nvars` ensures the modular arithmetic roundtrip works. -/
theorem literal_roundtrip {w : Nat} (lit : Literal) (seed : Seed w) (clauseIdx litIdx : Nat)
    (nvars : Nat) (h_valid : lit.var < nvars) :
    decodeLiteral (encodeLiteral lit seed clauseIdx litIdx nvars) seed clauseIdx litIdx nvars = lit := by
  simp only [encodeLiteral, decodeLiteral, computeLiteralMask]
  cases lit with
  | mk var pol =>
    simp only [Literal.mk.injEq]
    constructor
    · -- Variable roundtrip via mod_add_sub_roundtrip
      have hb : 0 < nvars + 1 := Nat.succ_pos nvars
      have hv : var < nvars + 1 := Nat.lt_succ_of_lt h_valid
      exact mod_add_sub_roundtrip var _ (nvars + 1) hv hb
    · exact Bool.xor_self_inverse pol _

/-- EncodedLiteral equality is decidable by components -/
theorem EncodedLiteral.eq_iff (a b : EncodedLiteral) :
    a = b ↔ a.maskedVar = b.maskedVar ∧ a.maskedPolarity = b.maskedPolarity := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; cases a; cases b; simp_all

/-- Literal equality is decidable by components -/
theorem Literal.eq_iff (a b : Literal) :
    a = b ↔ a.var = b.var ∧ a.polarity = b.polarity := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; cases a; cases b; simp_all

/-- Encode a clause with bounded masking. -/
def encodeClause {w : Nat} (c : Clause) (seed : Seed w) (clauseIdx : Nat) (nvars : Nat) : EncodedClause :=
  let encLits := (List.range c.literals.length).map fun i =>
    match c.literals[i]? with
    | some lit => encodeLiteral lit seed clauseIdx i nvars
    | none => { maskedVar := 0, maskedPolarity := false } -- unreachable
  { literals := encLits }

/-- Decode a clause with bounded masking. -/
def decodeClause {w : Nat} (enc : EncodedClause) (seed : Seed w) (clauseIdx : Nat) (nvars : Nat) : Clause :=
  let lits := (List.range enc.literals.length).map fun i =>
    match enc.literals[i]? with
    | some lit => decodeLiteral lit seed clauseIdx i nvars
    | none => { var := 0, polarity := false } -- unreachable
  { literals := lits }

/-- encodeClause preserves literal count -/
theorem encodeClause_literals_length {w : Nat} (c : Clause) (seed : Seed w) (clauseIdx : Nat) (nvars : Nat) :
    (encodeClause c seed clauseIdx nvars).literals.length = c.literals.length := by
  simp only [encodeClause, List.length_map, List.length_range]

/-- Helper: accessing encoded clause literal at valid index -/
theorem encodeClause_getElem {w : Nat} (c : Clause) (seed : Seed w) (clauseIdx : Nat) (nvars : Nat)
    (i : Nat) (h : i < c.literals.length) :
    (encodeClause c seed clauseIdx nvars).literals[i]'(by rw [encodeClause_literals_length]; exact h) =
    encodeLiteral c.literals[i] seed clauseIdx i nvars := by
  unfold encodeClause
  simp only [List.getElem_map, List.getElem_range, h, List.getElem?_eq_getElem]

/-- Clause roundtrip: decode(encode(clause)) = clause when all literals are valid.

    **Precondition**: All literals in the clause have `lit.var < nvars`. -/
theorem clause_roundtrip {w : Nat} (c : Clause) (seed : Seed w) (clauseIdx : Nat) (nvars : Nat)
    (h_valid : ∀ lit ∈ c.literals, lit.var < nvars) :
    decodeClause (encodeClause c seed clauseIdx nvars) seed clauseIdx nvars = c := by
  -- Expand definitions
  unfold decodeClause
  -- Show { literals := decoded_list } = c
  cases c with
  | mk lits =>
    simp only [Clause.mk.injEq]
    -- Need to show decoded list = lits
    have h_len : (encodeClause ⟨lits⟩ seed clauseIdx nvars).literals.length = lits.length :=
      encodeClause_literals_length ⟨lits⟩ seed clauseIdx nvars
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, h_len]
    · intro i h1 h2
      simp only [List.length_map, List.length_range, h_len] at h1
      simp only [List.getElem_map, List.getElem_range]
      -- The match on getElem?: since h_bound holds, getElem? returns some
      have h_bound : i < (encodeClause ⟨lits⟩ seed clauseIdx nvars).literals.length := by
        rw [h_len]; exact h1
      have h_getElem? : (encodeClause ⟨lits⟩ seed clauseIdx nvars).literals[i]? =
          some ((encodeClause ⟨lits⟩ seed clauseIdx nvars).literals[i]'h_bound) :=
        List.getElem?_eq_getElem h_bound
      rw [h_getElem?]
      -- Now the match evaluates to the some branch
      simp only
      -- Use encodeClause_getElem to rewrite the encoded literal
      have h_enc : (encodeClause ⟨lits⟩ seed clauseIdx nvars).literals[i]'h_bound =
          encodeLiteral lits[i] seed clauseIdx i nvars := encodeClause_getElem ⟨lits⟩ seed clauseIdx nvars i h1
      rw [h_enc]
      -- Apply literal roundtrip - need to show lits[i].var < nvars
      have h_lit_valid : lits[i].var < nvars := h_valid lits[i] (List.getElem_mem h1)
      exact literal_roundtrip lits[i] seed clauseIdx i nvars h_lit_valid

/-- Clause equality by literals equality -/
theorem Clause.eq_iff (a b : Clause) : a = b ↔ a.literals = b.literals := by
  constructor
  · intro h; subst h; rfl
  · intro h; cases a; cases b; simp_all

/-- Helper: computeLiteralMask only depends on seed.val -/
theorem computeLiteralMask_val_eq {w1 w2 : Nat} (s1 : Seed w1) (s2 : Seed w2)
    (clauseIdx litIdx : Nat) (h : s1.val = s2.val) :
    computeLiteralMask s1 clauseIdx litIdx = computeLiteralMask s2 clauseIdx litIdx := by
  simp only [computeLiteralMask, PoolConfig.hashSeed, h]

/-- Helper: encodeLiteral only depends on seed.val -/
theorem encodeLiteral_val_eq {w1 w2 : Nat} (lit : Literal) (s1 : Seed w1) (s2 : Seed w2)
    (clauseIdx litIdx nvars : Nat) (h : s1.val = s2.val) :
    encodeLiteral lit s1 clauseIdx litIdx nvars = encodeLiteral lit s2 clauseIdx litIdx nvars := by
  simp only [encodeLiteral, computeLiteralMask_val_eq s1 s2 clauseIdx litIdx h]

/-- Helper: decodeLiteral only depends on seed.val -/
theorem decodeLiteral_val_eq {w1 w2 : Nat} (enc : EncodedLiteral) (s1 : Seed w1) (s2 : Seed w2)
    (clauseIdx litIdx nvars : Nat) (h : s1.val = s2.val) :
    decodeLiteral enc s1 clauseIdx litIdx nvars = decodeLiteral enc s2 clauseIdx litIdx nvars := by
  simp only [decodeLiteral, computeLiteralMask_val_eq s1 s2 clauseIdx litIdx h]

/-- **Key Lemma**: encodeClause only depends on seed.val, not the type parameter.

    This enables working with seeds of provably-equal-but-differently-typed widths. -/
theorem encodeClause_val_eq {w1 w2 : Nat} (c : Clause) (s1 : Seed w1) (s2 : Seed w2)
    (clauseIdx nvars : Nat) (h : s1.val = s2.val) :
    encodeClause c s1 clauseIdx nvars = encodeClause c s2 clauseIdx nvars := by
  simp only [encodeClause]
  congr 1
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    cases hlit : c.literals[i]?
    · rfl
    · exact encodeLiteral_val_eq _ s1 s2 clauseIdx i nvars h

/-- **Key Lemma**: decodeClause only depends on seed.val, not the type parameter.

    This enables working with seeds of provably-equal-but-differently-typed widths.
    Together with clause_roundtrip, this shows:
    decodeClause (encodeClause c s1 i nvars) s2 i nvars = c when s1.val = s2.val -/
theorem decodeClause_val_eq {w1 w2 : Nat} (enc : EncodedClause) (s1 : Seed w1) (s2 : Seed w2)
    (clauseIdx nvars : Nat) (h : s1.val = s2.val) :
    decodeClause enc s1 clauseIdx nvars = decodeClause enc s2 clauseIdx nvars := by
  simp only [decodeClause]
  congr 1
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    cases hlit : enc.literals[i]?
    · rfl
    · exact decodeLiteral_val_eq _ s1 s2 clauseIdx i nvars h

/-- **Clause roundtrip with different seed widths**: If encode and decode seeds have equal values,
    the roundtrip holds even with different type parameters. -/
theorem clause_roundtrip_val_eq {w1 w2 : Nat} (c : Clause) (encode_seed : Seed w1) (decode_seed : Seed w2)
    (clauseIdx nvars : Nat) (h : encode_seed.val = decode_seed.val)
    (h_valid : ∀ lit ∈ c.literals, lit.var < nvars) :
    decodeClause (encodeClause c encode_seed clauseIdx nvars) decode_seed clauseIdx nvars = c := by
  -- First rewrite encodeClause to use decode_seed (via val equality)
  have h_enc := encodeClause_val_eq c encode_seed decode_seed clauseIdx nvars h
  rw [h_enc]
  exact clause_roundtrip c decode_seed clauseIdx nvars h_valid

/-- **Encode CNF**: Transform plaintext CNF into OAP-encoded EncodedCNF.

    **Inputs**:
    - `φ`: The plaintext CNF.
    - `getSeed`: Function mapping clause index to its seed (with uniform width w).

    **Output**: `EncodedCNF`

    **Note**: Uses uniform seed width. For dependent seed widths, use `encodeWithOAPDep`.
    Uses bounded additive masking to ensure `maskedVar ≤ nvars`.
-/
def encodeWithOAP {w : Nat} (φ : CNF) (getSeed : Fin φ.clauses.length → Seed w) : EncodedCNF :=
  let encClauses := (List.range φ.clauses.length).map fun i =>
    if h : i < φ.clauses.length then
      match φ.clauses[i]? with
      | some c => encodeClause c (getSeed ⟨i, h⟩) i φ.nvars
      | none => { literals := [] } -- unreachable since i < length
    else
      { literals := [] } -- unreachable
  { nvars := φ.nvars
    nvars_pos := φ.nvars_pos
    clauses := encClauses }

/-- **Encode CNF with Dependent Seed Widths**: Transform plaintext CNF into OAP-encoded EncodedCNF.

    **Inputs**:
    - `φ`: The plaintext CNF.
    - `seedWidthFn`: Function mapping clause index to its seed width.
    - `getSeed`: Dependent function mapping clause index to its seed of appropriate width.

    **Output**: `EncodedCNF`

    **Rationale**: In the L* construction, different DAG vertices have different seed widths
    based on their position in the dependency structure. FG clause nodes have width (log₂ n)²,
    while other nodes may have different widths. This function handles the heterogeneous case.
    Uses bounded additive masking to ensure `maskedVar ≤ nvars`.
-/
def encodeWithOAPDep (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i)) : EncodedCNF :=
  let encClauses := (List.range φ.clauses.length).map fun i =>
    if h : i < φ.clauses.length then
      match φ.clauses[i]? with
      | some c => encodeClause c (getSeed ⟨i, h⟩) i φ.nvars
      | none => { literals := [] } -- unreachable since i < length
    else
      { literals := [] } -- unreachable
  { nvars := φ.nvars
    nvars_pos := φ.nvars_pos
    clauses := encClauses }

/-- **Decode CNF**: Recover plaintext CNF from OAP-encoded EncodedCNF.

    **Inputs**:
    - `enc`: The encoded CNF.
    - `getSeed`: Function mapping clause index to its seed (with uniform width w).

    **Output**: `CNF`

    **Note**: Uses uniform seed width. For dependent seed widths, use `decodeWithOAPDep`.
-/
def decodeWithOAP {w : Nat} (enc : EncodedCNF) (getSeed : Fin enc.clauses.length → Seed w) : CNF :=
  let clauses := (List.range enc.clauses.length).map fun i =>
    if h : i < enc.clauses.length then
      match enc.clauses[i]? with
      | some c => decodeClause c (getSeed ⟨i, h⟩) i enc.nvars
      | none => { literals := [] } -- unreachable
    else
      { literals := [] } -- unreachable
  { nvars := enc.nvars
    nvars_pos := enc.nvars_pos
    clauses := clauses }

/-- **Decode CNF with Dependent Seed Widths**: Recover plaintext CNF from OAP-encoded EncodedCNF.

    **Inputs**:
    - `enc`: The encoded CNF.
    - `seedWidthFn`: Function mapping clause index to its seed width.
    - `getSeed`: Dependent function mapping clause index to its seed of appropriate width.

    **Output**: `CNF`
-/
def decodeWithOAPDep (enc : EncodedCNF)
    (seedWidthFn : Fin enc.clauses.length → Nat)
    (getSeed : (i : Fin enc.clauses.length) → Seed (seedWidthFn i)) : CNF :=
  let clauses := (List.range enc.clauses.length).map fun i =>
    if h : i < enc.clauses.length then
      match enc.clauses[i]? with
      | some c => decodeClause c (getSeed ⟨i, h⟩) i enc.nvars
      | none => { literals := [] } -- unreachable
    else
      { literals := [] } -- unreachable
  { nvars := enc.nvars
    nvars_pos := enc.nvars_pos
    clauses := clauses }

/-- encodeWithOAP preserves clause count -/
theorem encodeWithOAP_clauses_length {w : Nat} (φ : CNF) (getSeed : Fin φ.clauses.length → Seed w) :
    (encodeWithOAP φ getSeed).clauses.length = φ.clauses.length := by
  simp [encodeWithOAP]

/-- encodeWithOAP preserves nvars -/
theorem encodeWithOAP_nvars {w : Nat} (φ : CNF) (getSeed : Fin φ.clauses.length → Seed w) :
    (encodeWithOAP φ getSeed).nvars = φ.nvars := by
  simp [encodeWithOAP]

/-- encodeWithOAPDep preserves clause count -/
theorem encodeWithOAPDep_clauses_length (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i)) :
    (encodeWithOAPDep φ seedWidthFn getSeed).clauses.length = φ.clauses.length := by
  simp [encodeWithOAPDep]

/-- encodeWithOAPDep preserves nvars -/
theorem encodeWithOAPDep_nvars (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i)) :
    (encodeWithOAPDep φ seedWidthFn getSeed).nvars = φ.nvars := by
  simp [encodeWithOAPDep]

/-- **Extensionality for encodeWithOAPDep**: Equal seeds produce equal encoded CNFs.

    This is the key congruence lemma enabling proofs that two plant constructions
    produce equal encodedφ when their seed chains are equal. -/
theorem encodeWithOAPDep_ext (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed1 getSeed2 : (i : Fin φ.clauses.length) → Seed (seedWidthFn i))
    (h_eq : ∀ i, getSeed1 i = getSeed2 i) :
    encodeWithOAPDep φ seedWidthFn getSeed1 = encodeWithOAPDep φ seedWidthFn getSeed2 := by
  have h_seeds_eq : getSeed1 = getSeed2 := funext h_eq
  rw [h_seeds_eq]

/-- Helper: Fin equality from List.getElem_range -/
theorem fin_eq_of_range_getElem (n i : Nat) (h : i < n) (h' : i < (List.range n).length) :
    (⟨(List.range n)[i]'h', (by simp only [List.getElem_range]; exact h)⟩ : Fin n) = ⟨i, h⟩ := by
  ext
  simp only [List.getElem_range]

/-- Helper: accessing encoded CNF clause at valid index (dependent version) -/
theorem encodeWithOAPDep_getElem (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i))
    (i : Nat) (h : i < φ.clauses.length) :
    (encodeWithOAPDep φ seedWidthFn getSeed).clauses[i]'(by rw [encodeWithOAPDep_clauses_length]; exact h) =
    encodeClause φ.clauses[i] (getSeed ⟨i, h⟩) i φ.nvars := by
  unfold encodeWithOAPDep
  simp only [List.getElem_map, List.getElem_range, h, List.getElem?_eq_getElem, ↓reduceDIte]
  -- After simp, we need to show encodeClause with Fin ⟨(range n)[i], _⟩ equals that with ⟨i, h⟩
  -- The Fin values are equal: (range n)[i] = i (by List.getElem_range)
  -- Since Fin is a subtype, and vals are equal, the Fins are equal (proof irrelevance)
  have h_range_len : i < (List.range φ.clauses.length).length := by simp only [List.length_range]; exact h
  have h_fin_eq : (⟨(List.range φ.clauses.length)[i]'h_range_len, (by rw [List.getElem_range]; exact h)⟩ : Fin φ.clauses.length) = ⟨i, h⟩ := by
    ext
    simp only [List.getElem_range]
  rw [h_fin_eq]

/-- Helper: accessing encoded CNF clause at valid index -/
theorem encodeWithOAP_getElem {w : Nat} (φ : CNF) (getSeed : Fin φ.clauses.length → Seed w)
    (i : Nat) (h : i < φ.clauses.length) :
    (encodeWithOAP φ getSeed).clauses[i]'(by rw [encodeWithOAP_clauses_length]; exact h) =
    encodeClause φ.clauses[i] (getSeed ⟨i, h⟩) i φ.nvars := by
  unfold encodeWithOAP
  simp only [List.getElem_map, List.getElem_range, h, List.getElem?_eq_getElem, ↓reduceDIte]

/-- CNF equality by components -/
theorem CNF.eq_iff (a b : CNF) :
    a = b ↔ a.nvars = b.nvars ∧ a.clauses = b.clauses := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; cases a; cases b; simp_all

/-- **Roundtrip Theorem**: Decoding the encoded CNF with the same seeds yields the original CNF.

    **Precondition**: All literals in the CNF have `lit.var < nvars`. -/
theorem oap_roundtrip {w : Nat} (φ : CNF) (getSeed : Fin φ.clauses.length → Seed w)
    (h_valid : ∀ c ∈ φ.clauses, ∀ lit ∈ c.literals, lit.var < φ.nvars) :
    decodeWithOAP (encodeWithOAP φ getSeed) (fun i =>
      -- We need to cast the index because encodeWithOAP preserves length
      let idx : Fin φ.clauses.length := ⟨i.val, by
        have h_len : (encodeWithOAP φ getSeed).clauses.length = φ.clauses.length := by
          simp [encodeWithOAP]
        rw [←h_len]
        exact i.isLt⟩
      getSeed idx) = φ := by
  -- Prove CNF equality by components
  rw [CNF.eq_iff]
  constructor
  · -- nvars are preserved
    simp only [decodeWithOAP, encodeWithOAP]
  · -- clauses are the same
    unfold decodeWithOAP
    have h_len : (encodeWithOAP φ getSeed).clauses.length = φ.clauses.length :=
      encodeWithOAP_clauses_length φ getSeed
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, h_len]
    · intro i h1 h2
      simp only [List.length_map, List.length_range, h_len] at h1
      simp only [List.getElem_map, List.getElem_range]
      -- Establish bounds for dite
      have h_bound : i < (encodeWithOAP φ getSeed).clauses.length := by
        rw [h_len]; exact h1
      simp only [h_bound, ↓reduceDIte]
      have h_getElem? : (encodeWithOAP φ getSeed).clauses[i]? =
          some ((encodeWithOAP φ getSeed).clauses[i]'h_bound) :=
        List.getElem?_eq_getElem h_bound
      rw [h_getElem?]
      simp only
      -- Use encodeWithOAP_getElem to rewrite the encoded clause
      have h_enc : (encodeWithOAP φ getSeed).clauses[i]'h_bound =
          encodeClause φ.clauses[i] (getSeed ⟨i, h1⟩) i φ.nvars := encodeWithOAP_getElem φ getSeed i h1
      rw [h_enc]
      -- Apply clause roundtrip - need validity for this clause
      have h_clause_mem : φ.clauses[i] ∈ φ.clauses := List.getElem_mem h1
      have h_clause_valid : ∀ lit ∈ (φ.clauses[i]).literals, lit.var < φ.nvars := h_valid _ h_clause_mem
      exact clause_roundtrip φ.clauses[i] (getSeed ⟨i, h1⟩) i φ.nvars h_clause_valid

/-- **Roundtrip Theorem (Dependent Version)**: Decoding the encoded CNF with the same seeds yields the original CNF.

    This is the version for dependent seed widths, used in the L* construction where different
    DAG vertices have different seed widths. Uses bounded additive masking for polynomial encoding.

    **Precondition**: All literals in the CNF have `lit.var < nvars`. -/
theorem oap_roundtrip_dep (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i))
    (h_valid : ∀ c ∈ φ.clauses, ∀ lit ∈ c.literals, lit.var < φ.nvars) :
    decodeWithOAPDep (encodeWithOAPDep φ seedWidthFn getSeed)
      (fun i => seedWidthFn ⟨i.val, by
        have h_len := encodeWithOAPDep_clauses_length φ seedWidthFn getSeed
        rw [← h_len]; exact i.isLt⟩)
      (fun i => getSeed ⟨i.val, by
        have h_len := encodeWithOAPDep_clauses_length φ seedWidthFn getSeed
        rw [← h_len]; exact i.isLt⟩) = φ := by
  -- Prove CNF equality by components
  rw [CNF.eq_iff]
  constructor
  · -- nvars are preserved
    simp only [decodeWithOAPDep, encodeWithOAPDep]
  · -- clauses are the same
    unfold decodeWithOAPDep
    have h_len : (encodeWithOAPDep φ seedWidthFn getSeed).clauses.length = φ.clauses.length :=
      encodeWithOAPDep_clauses_length φ seedWidthFn getSeed
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, h_len]
    · intro i h1 h2
      simp only [List.length_map, List.length_range, h_len] at h1
      simp only [List.getElem_map, List.getElem_range]
      -- Establish bounds for dite
      have h_bound : i < (encodeWithOAPDep φ seedWidthFn getSeed).clauses.length := by
        rw [h_len]; exact h1
      simp only [h_bound, ↓reduceDIte]
      have h_getElem? : (encodeWithOAPDep φ seedWidthFn getSeed).clauses[i]? =
          some ((encodeWithOAPDep φ seedWidthFn getSeed).clauses[i]'h_bound) :=
        List.getElem?_eq_getElem h_bound
      rw [h_getElem?]
      simp only
      -- Use encodeWithOAPDep_getElem to rewrite the encoded clause
      have h_enc : (encodeWithOAPDep φ seedWidthFn getSeed).clauses[i]'h_bound =
          encodeClause φ.clauses[i] (getSeed ⟨i, h1⟩) i φ.nvars := encodeWithOAPDep_getElem φ seedWidthFn getSeed i h1
      rw [h_enc]
      -- The Fin values have the same underlying Nat value i
      -- After simp with List.getElem_range, the index becomes i
      -- So we need to prove getSeed on two Fins with the same val gives equal results
      have h_bound'' : i < (encodeWithOAPDep φ seedWidthFn getSeed).clauses.length := h_bound
      have h_fin_eq : (⟨(List.range (encodeWithOAPDep φ seedWidthFn getSeed).clauses.length)[i]'(by
            simp only [List.length_range]; exact h_bound), by rw [← h_len]; simp only [List.getElem_range]; exact h_bound''⟩ : Fin φ.clauses.length) = ⟨i, h1⟩ := by
        apply Fin.ext; simp only [List.getElem_range]
      -- Rewrite using Fin equality (this works because getSeed applied to equal Fins gives equal results)
      rw [h_fin_eq]
      -- Apply clause roundtrip - need validity for this clause
      have h_clause_mem : φ.clauses[i] ∈ φ.clauses := List.getElem_mem h1
      have h_clause_valid : ∀ lit ∈ (φ.clauses[i]).literals, lit.var < φ.nvars := h_valid _ h_clause_mem
      exact clause_roundtrip φ.clauses[i] (getSeed ⟨i, h1⟩) i φ.nvars h_clause_valid

/-- **Simple Roundtrip Theorem (Dependent Version)**: Direct form without index casting.

    This is a convenience alias for `oap_roundtrip_dep` that makes it clearer in proofs
    that the fundamental OAP property is: encode then decode with the same seeds = identity.

    The theorem `oap_roundtrip_dep` handles the necessary index casting internally.

    **Precondition**: All literals in the CNF have `lit.var < nvars`. -/
theorem encodeWithOAPDep_decode_roundtrip (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i))
    (h_valid : ∀ c ∈ φ.clauses, ∀ lit ∈ c.literals, lit.var < φ.nvars) :
    decodeWithOAPDep (encodeWithOAPDep φ seedWidthFn getSeed)
      (fun i => seedWidthFn ⟨i.val, by
        have h_len := encodeWithOAPDep_clauses_length φ seedWidthFn getSeed
        rw [← h_len]; exact i.isLt⟩)
      (fun i => getSeed ⟨i.val, by
        have h_len := encodeWithOAPDep_clauses_length φ seedWidthFn getSeed
        rw [← h_len]; exact i.isLt⟩) = φ :=
  oap_roundtrip_dep φ seedWidthFn getSeed h_valid

/-! ### Encoding Bounds

Key properties for polynomial encoding size bounds. -/

/-- maskedVar is bounded by nvars (from modular arithmetic construction).

    This is the key property that enables polynomial encoding size bounds. -/
theorem encodeLiteral_maskedVar_le {w : Nat} (lit : Literal) (seed : Seed w)
    (clauseIdx litIdx nvars : Nat) :
    (encodeLiteral lit seed clauseIdx litIdx nvars).maskedVar ≤ nvars := by
  simp only [encodeLiteral, computeLiteralMask]
  -- maskedVar = (lit.var + maskVar) % (nvars + 1)
  -- By Nat.mod_lt, (x % (nvars + 1)) < nvars + 1, so (x % (nvars + 1)) ≤ nvars
  have h : (lit.var + (PoolConfig.hashSeed seed + clauseIdx * 997 + litIdx * 991)) % (nvars + 1) < nvars + 1 :=
    Nat.mod_lt _ (Nat.succ_pos nvars)
  omega

/-- All maskedVar values in an encoded clause are bounded by nvars. -/
theorem encodeClause_maskedVar_le {w : Nat} (c : Clause) (seed : Seed w)
    (clauseIdx nvars : Nat) :
    ∀ lit ∈ (encodeClause c seed clauseIdx nvars).literals, lit.maskedVar ≤ nvars := by
  intro lit h_mem
  unfold encodeClause at h_mem
  simp only [List.mem_map, List.mem_range] at h_mem
  obtain ⟨i, h_i_lt, h_eq⟩ := h_mem
  cases h_opt : c.literals[i]? with
  | none =>
    simp only [h_opt] at h_eq
    rw [← h_eq]
    exact Nat.zero_le _
  | some lit' =>
    simp only [h_opt] at h_eq
    rw [← h_eq]
    exact encodeLiteral_maskedVar_le lit' seed clauseIdx i nvars

/-- All maskedVar values in an encoded CNF (via encodeWithOAPDep) are bounded by nvars. -/
theorem encodeWithOAPDep_maskedVar_le (φ : CNF)
    (seedWidthFn : Fin φ.clauses.length → Nat)
    (getSeed : (i : Fin φ.clauses.length) → Seed (seedWidthFn i)) :
    ∀ c ∈ (encodeWithOAPDep φ seedWidthFn getSeed).clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ φ.nvars := by
  intro c h_c_mem lit h_lit_mem
  unfold encodeWithOAPDep at h_c_mem
  simp only [List.mem_map, List.mem_range] at h_c_mem
  obtain ⟨i, h_i_lt, h_c_eq⟩ := h_c_mem
  simp only [h_i_lt, ↓reduceDIte] at h_c_eq
  cases h_opt : φ.clauses[i]? with
  | none =>
    simp only [h_opt] at h_c_eq
    rw [← h_c_eq] at h_lit_mem
    simp only [List.not_mem_nil] at h_lit_mem
  | some clause =>
    simp only [h_opt] at h_c_eq
    rw [← h_c_eq] at h_lit_mem
    exact encodeClause_maskedVar_le clause (getSeed ⟨i, h_i_lt⟩) i φ.nvars lit h_lit_mem

end LStar.OAP
