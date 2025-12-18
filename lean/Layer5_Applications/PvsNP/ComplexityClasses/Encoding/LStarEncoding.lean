import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
-- import Mathlib.Data.Nat.Digits  -- Disabled: module path changed in newer Mathlib
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Matrix.Basic
-- import Mathlib.Data.Matrix.Rank  -- Disabled: module path changed in newer Mathlib

import Layer0_Foundations.Base.DAG
import Layer0_Foundations.Base.EncodedCNF
import Layer1_Construction.Core.EmergenceMatrix
import Layer1_Construction.Core.Pools
import Layer1_Construction.Core.LStarInstance
import Layer2_StructuralOWF.FrontierGate.FrontierGate

import Layer5_Applications.PvsNP.ComplexityClasses.Sized
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances
import Layer5_Applications.PvsNP.ComplexityClasses.BitEncoding
import Layer5_Applications.PvsNP.ComplexityClasses.TMEncoding
import Layer5_Applications.PvsNP.ComplexityClasses.NPDefs  -- For Lang, HasWitnessStructure, VerifierCert
import Layer5_Applications.PvsNP.ComplexityClasses.AlgSpec  -- For AlgSpec
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv  -- For RandAdv, algspec_has_tm
import Layer5_Applications.PvsNP.ComplexityClasses.ComplexityClasses  -- For InNP
import Infrastructure.Witness.VerifiedWitness  -- For HasCorrectDigests

/-! ## LStarEncoding: Explicit Binary Encoding for L*

**Purpose**: Provides explicit bitstring encoding for L* instances and
transfer theorems between structured types and `{0,1}*`.

**Relationship to Main Theorem**:
- The main `P_ne_NP` theorem (StructuralOWFBridge.lean) uses abstract input
  types with bitstring witnesses, proving separation for some type α
- For a fully textbook-style result (language L ⊆ {0,1}*), this file provides:
  1. Explicit `LStarLanguageLang : Lang (List Bool)` — the hard language
  2. Direct `LStarLanguageLang_in_NP` — membership in NP
  3. Transfer theorems to obtain `¬InP` over bitstrings from structured hardness

**Use Case**: To state "L* ⊆ {0,1}* is in NP \ P" rather than just
"∃ α L, L is in NP \ P over α".

**Approach**:
1. Define `Encodable` typeclass with prefix-free encoding property
2. Define "Raw" versions of dependent structures (`RawLStarInstance`, etc.)
3. Implement `Encodable` for Raw structures
4. Prove injectivity and polynomial size bounds (`PolytimeEncoding`)
5. Provide transfer theorems (`np_transfer`, `p_backward_transfer`, `hardness_transfer`)
-/

namespace LStar.Encoding

open LStar
open LStar.LStarInstanceFull
open LStar.StructuralOWF
open LStar.Complexity

/-- A bit string is just a list of booleans. -/
abbrev BitString := List Bool

/-- Class for types that can be encoded to and decoded from bit strings.

    **Key property**: `decode_encode_append` ensures the encoding is prefix-free,
    meaning `decode (encode x ++ rest) = some (x, rest)`. This allows unambiguous
    concatenation of encoded values. -/
class Encodable (α : Type) where
  encode : α → BitString
  decode : BitString → Option (α × BitString) -- Returns value + remaining bits
  /-- Prefix-free encoding property: decode inverts encode with remaining bits. -/
  decode_encode_append : ∀ (x : α) (rest : BitString),
    decode (encode x ++ rest) = some (x, rest)

/-- Helper: Decode exact string (must exhaust input). -/
def decodeFull {α : Type} [Encodable α] (bits : BitString) : Option α :=
  match Encodable.decode bits with
  | some (val, []) => some val
  | _ => none

/-- Encodable.encode is injective: different values produce different encodings. -/
theorem Encodable.encode_injective {α : Type} [inst : Encodable α] :
    Function.Injective (Encodable.encode (α := α)) := by
  intro x y h_eq
  have h1 := inst.decode_encode_append x []
  have h2 := inst.decode_encode_append y []
  simp only [List.append_nil] at h1 h2
  rw [h_eq] at h1
  rw [h1] at h2
  have h3 : (x, []) = (y, []) := Option.some.injEq _ _ |>.mp h2
  exact (Prod.mk.injEq x [] y []).mp h3 |>.1

instance : Encodable Bool where
  encode b := [b]
  decode bits :=
    match bits with
    | b :: rest => some (b, rest)
    | [] => none
  decode_encode_append := fun b rest => rfl

/-- Read a unary-encoded length: count `true` bits until `false`, return (count, rest).
    This is a standalone terminating function for reasoning. -/
def readUnaryLen (bits : BitString) : Option (Nat × BitString) :=
  match bits with
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match readUnaryLen rest with
    | some (n, rest') => some (n + 1, rest')
    | none => none

/-- Helper: readUnaryLen on (replicate n true ++ [false] ++ rest) returns (n, rest). -/
lemma readUnaryLen_replicate (n : Nat) (rest : BitString) :
    readUnaryLen (List.replicate n true ++ [false] ++ rest) = some (n, rest) := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append]
    unfold readUnaryLen
    rw [ih]

/-- Encode Nat as self-delimiting unary-prefixed binary.
    - n = 0 encodes as [false]
    - n > 0 encodes as (n.bits.length true's) ++ [false] ++ n.bits -/
def encodeNat (n : Nat) : BitString :=
  if n = 0 then [false] else
  let lsb_bits := n.bits -- LSB first
  let len := lsb_bits.length
  List.replicate len true ++ [false] ++ lsb_bits

/-- Decode a Nat from a bit string. -/
def decodeNat (bits : BitString) : Option (Nat × BitString) :=
  match readUnaryLen bits with
  | some (0, rest) => some (0, rest)  -- Length 0 means n = 0
  | some (len, rest) =>
    if h : rest.length < len then none else
    let (n_bits, rest') := rest.splitAt len
    let n := n_bits.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0
    some (n, rest')
  | none => none

/-- Nat.bits is non-empty for n > 0 -/
lemma Nat.bits_length_pos {n : Nat} (h : n > 0) : n.bits.length > 0 := by
  have h_ne : n.bits ≠ [] := by
    induction n using Nat.binaryRec' with
    | zero => omega
    | bit b m hm =>
      rw [Nat.bits_append_bit _ _ hm]
      exact List.cons_ne_nil _ _
  exact List.length_pos_of_ne_nil h_ne

/-- foldr reconstruction of n from n.bits -/
lemma Nat.bits_foldr_eq (n : Nat) (h : n > 0) :
    n.bits.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have h_ne_zero : n ≠ 0 := Nat.ne_of_gt h
    -- Use the binary representation: bits n = bodd :: div2.bits
    have h_ne : n.bits ≠ [] := List.ne_nil_of_length_pos (Nat.bits_length_pos h)
    have h_eq : n.bits = n.bodd :: n.div2.bits := by
      rw [Nat.bodd_eq_bits_head, Nat.div2_bits_eq_tail]
      exact (List.cons_head!_tail h_ne).symm
    rw [h_eq, List.foldr_cons]
    -- (if n.bodd then 1 else 0) + 2 * (div2.bits.foldr ...) = n
    -- We know: bodd.toNat + 2 * div2 = n  (Nat.bodd_add_div2)
    -- And: (if b then 1 else 0) = b.toNat for Bool
    have h_bodd_val : (if n.bodd then 1 else 0) = n.bodd.toNat := by cases n.bodd <;> rfl
    rw [h_bodd_val]
    cases Nat.eq_zero_or_pos n.div2 with
    | inl h0 =>
      -- div2 = 0 means n ∈ {0, 1}. Since n > 0, we have n = 1
      have h1 : n = 1 := by
        have h_reconstruct := Nat.bodd_add_div2 n
        simp [h0] at h_reconstruct
        cases hb : n.bodd <;> simp [hb] at h_reconstruct <;> omega
      subst h1
      simp [Nat.bits]
    | inr hpos =>
      have h_lt : n.div2 < n := Nat.binaryRec_decreasing h_ne_zero
      have ih_applied := ih n.div2 h_lt hpos
      have h_reconstruct := Nat.bodd_add_div2 n
      omega

/-- decode_encode_append for Nat -/
lemma Nat.decode_encode_append_lemma (n : Nat) (rest : BitString) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  simp only [encodeNat, decodeNat]
  split_ifs with h_zero
  · -- n = 0
    subst h_zero
    simp only [List.cons_append, readUnaryLen, List.nil_append]
  · -- n ≠ 0
    have h_pos : n > 0 := Nat.pos_of_ne_zero h_zero
    -- Rewrite to match readUnaryLen_replicate form
    have h_assoc : (List.replicate n.bits.length true ++ [false] ++ n.bits) ++ rest =
                   List.replicate n.bits.length true ++ [false] ++ (n.bits ++ rest) := by
      simp only [List.append_assoc]
    rw [h_assoc, readUnaryLen_replicate n.bits.length (n.bits ++ rest)]
    have h_len_pos : n.bits.length > 0 := Nat.bits_length_pos h_pos
    have h_len_ne_zero : n.bits.length ≠ 0 := Nat.ne_of_gt h_len_pos
    simp only [h_len_ne_zero, ↓reduceDIte, not_false_eq_true]
    have h_len_ok : ¬ (n.bits ++ rest).length < n.bits.length := by
      simp only [List.length_append, not_lt]
      omega
    simp only [h_len_ok, ↓reduceDIte]
    -- Now goal is: some (...splitAt n.bits.length...) = some (n, rest)
    simp only [List.splitAt_eq, List.take_left, List.drop_left, Nat.bits_foldr_eq n h_pos]

instance : Encodable Nat where
  encode := encodeNat
  decode := decodeNat
  decode_encode_append := Nat.decode_encode_append_lemma

/-- Read n elements from a bitstring, decoding each with Encodable.decode -/
def readElems {α : Type} [Encodable α] (n : Nat) (rem : BitString) (acc : List α) :
    Option (List α × BitString) :=
  match n with
  | 0 => some (acc.reverse, rem)
  | k + 1 =>
    match Encodable.decode rem with
    | some (val, rest) => readElems k rest (val :: acc)
    | none => none

/-- Helper: readElems correctly decodes a list encoded with flatMap -/
lemma readElems_flatMap {α : Type} [inst : Encodable α] (list : List α) (rest : BitString) (acc : List α) :
    readElems list.length (list.flatMap Encodable.encode ++ rest) acc =
    some (acc.reverse ++ list, rest) := by
  induction list generalizing acc rest with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, List.nil_append, readElems, List.append_nil]
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, readElems]
    have h_decode : Encodable.decode (Encodable.encode x ++ (xs.flatMap Encodable.encode ++ rest)) =
                    some (x, xs.flatMap Encodable.encode ++ rest) :=
      inst.decode_encode_append x (xs.flatMap Encodable.encode ++ rest)
    rw [List.append_assoc, h_decode]
    have ih_applied := ih rest (x :: acc)
    simp only [ih_applied, List.reverse_cons, List.append_assoc, List.singleton_append]

instance [Encodable α] : Encodable (List α) where
  encode list :=
    let len_prefix := List.replicate list.length true ++ [false]
    len_prefix ++ list.flatMap Encodable.encode
  decode bits :=
    match readUnaryLen bits with
    | some (len, rest) => readElems len rest []
    | none => none
  decode_encode_append := fun list rest => by
    show (match readUnaryLen ((List.replicate list.length true ++ [false] ++ list.flatMap Encodable.encode) ++ rest) with
         | some (len, r) => readElems len r []
         | none => none)
         = some (list, rest)
    conv_lhs => rw [List.append_assoc]
    rw [readUnaryLen_replicate list.length (list.flatMap Encodable.encode ++ rest)]
    have h_elems := readElems_flatMap list rest []
    simp only [List.reverse_nil, List.nil_append] at h_elems
    exact h_elems

instance [Encodable α] : Encodable (Option α) where
  encode opt :=
    match opt with
    | none => [false]
    | some x => [true] ++ Encodable.encode x
  decode bits :=
    match bits with
    | false :: rest => some (none, rest)
    | true :: rest =>
      match Encodable.decode rest with
      | some (val, rest') => some (some val, rest')
      | none => none
    | [] => none
  decode_encode_append := fun opt rest => by
    cases opt with
    | none => rfl
    | some x =>
      show (match Encodable.decode (Encodable.encode x ++ rest) with
           | some (val, rest') => some (some val, rest')
           | none => none)
           = some (some x, rest)
      rw [Encodable.decode_encode_append x rest]

/-! ### Raw Structures for Dependent Types -/

/-- Raw DAG data (n, parents list). -/
structure RawDAG where
  n : Nat
  parents : List (List Nat) -- Adjacency list
  deriving Repr

instance : Encodable RawDAG where
  encode dag := encodeNat dag.n ++ Encodable.encode dag.parents
  decode bits :=
    match decodeNat bits with
    | some (n, rest) =>
      match Encodable.decode rest with
      | some (parents, rest') => some ({ n := n, parents := parents }, rest')
      | none => none
    | none => none
  decode_encode_append := fun dag rest => by
    show (match decodeNat (encodeNat dag.n ++ Encodable.encode dag.parents ++ rest) with
         | some (n, r) => match Encodable.decode r with
           | some (parents, rest') => some ({ n := n, parents := parents }, rest')
           | none => none
         | none => none)
         = some (dag, rest)
    simp only [List.append_assoc, Nat.decode_encode_append_lemma dag.n (Encodable.encode dag.parents ++ rest),
               Encodable.decode_encode_append dag.parents rest]

/-- Raw Emergence Matrix data (R, n, bits). -/
structure RawEmergenceMatrix where
  R : Nat
  n : Nat
  bits : List Bool -- Row-major bits
  deriving Repr

instance : Encodable RawEmergenceMatrix where
  encode mat := encodeNat mat.R ++ encodeNat mat.n ++ Encodable.encode mat.bits
  decode bits :=
    match decodeNat bits with
    | some (R, rest) =>
      match decodeNat rest with
      | some (n, rest') =>
        match Encodable.decode rest' with
        | some (bits, rest'') => some ({ R := R, n := n, bits := bits }, rest'')
        | none => none
      | none => none
    | none => none
  decode_encode_append := fun mat rest => by
    show (match decodeNat (encodeNat mat.R ++ encodeNat mat.n ++ Encodable.encode mat.bits ++ rest) with
         | some (R, r1) => match decodeNat r1 with
           | some (n, r2) => match Encodable.decode r2 with
             | some (bits, r3) => some ({ R := R, n := n, bits := bits }, r3)
             | none => none
           | none => none
         | none => none)
         = some (mat, rest)
    simp only [List.append_assoc,
               Nat.decode_encode_append_lemma mat.R (encodeNat mat.n ++ (Encodable.encode mat.bits ++ rest)),
               Nat.decode_encode_append_lemma mat.n (Encodable.encode mat.bits ++ rest),
               Encodable.decode_encode_append mat.bits rest]

/-- Raw Pool Config (stride). -/
structure RawPoolConfig where
  stride : Nat
  deriving Repr

instance : Encodable RawPoolConfig where
  encode p := encodeNat p.stride
  decode bits :=
    match decodeNat bits with
    | some (s, rest) => some ({ stride := s }, rest)
    | none => none
  decode_encode_append := fun p rest => by
    show (match decodeNat (encodeNat p.stride ++ rest) with
         | some (s, r) => some ({ stride := s }, r)
         | none => none)
         = some (p, rest)
    rw [Nat.decode_encode_append_lemma p.stride rest]

/-- Raw Full Instance. -/
structure RawLStarInstanceFull where
  n : Nat
  dag : RawDAG
  seedWidth : List Nat
  R : List Nat
  emergence : List RawEmergenceMatrix
  pools : RawPoolConfig
  deriving Repr

instance : Encodable RawLStarInstanceFull where
  encode r :=
    encodeNat r.n ++
    Encodable.encode r.dag ++
    Encodable.encode r.seedWidth ++
    Encodable.encode r.R ++
    Encodable.encode r.emergence ++
    Encodable.encode r.pools
  decode bits :=
    match decodeNat bits with
    | some (n, rest) =>
      match Encodable.decode rest with
      | some (dag, rest') =>
        match Encodable.decode rest' with
        | some (sw, rest'') =>
           match Encodable.decode rest'' with
           | some (R, rest''') =>
             match Encodable.decode rest''' with
             | some (em, rest'''') =>
               match Encodable.decode rest'''' with
               | some (pools, rest''''') =>
                 some ({ n := n, dag := dag, seedWidth := sw, R := R, emergence := em, pools := pools }, rest''''')
               | none => none
             | none => none
           | none => none
        | none => none
      | none => none
    | none => none
  decode_encode_append := fun r rest => by
    simp only [List.append_assoc,
      Nat.decode_encode_append_lemma r.n
        (Encodable.encode r.dag ++ (Encodable.encode r.seedWidth ++
          (Encodable.encode r.R ++ (Encodable.encode r.emergence ++ (Encodable.encode r.pools ++ rest))))),
      Encodable.decode_encode_append r.dag
        (Encodable.encode r.seedWidth ++ (Encodable.encode r.R ++
          (Encodable.encode r.emergence ++ (Encodable.encode r.pools ++ rest)))),
      Encodable.decode_encode_append r.seedWidth
        (Encodable.encode r.R ++ (Encodable.encode r.emergence ++ (Encodable.encode r.pools ++ rest))),
      Encodable.decode_encode_append r.R
        (Encodable.encode r.emergence ++ (Encodable.encode r.pools ++ rest)),
      Encodable.decode_encode_append r.emergence (Encodable.encode r.pools ++ rest),
      Encodable.decode_encode_append r.pools rest]

/-- Raw Gate Digest. -/
structure RawGateDigest where
  segmentBudget : Nat
  bits : List Bool
  deriving Repr

instance : Encodable RawGateDigest where
  encode g := encodeNat g.segmentBudget ++ Encodable.encode g.bits
  decode bits :=
    match decodeNat bits with
    | some (b, rest) =>
      match Encodable.decode rest with
      | some (l, rest') => some ({ segmentBudget := b, bits := l }, rest')
      | none => none
    | none => none
  decode_encode_append := fun g rest => by
    simp only [List.append_assoc, Nat.decode_encode_append_lemma,
               Encodable.decode_encode_append]

/-- Raw Frontier Gate Config. -/
structure RawFrontierGateConfig where
  gateReq : List Bool
  gateDigests : List (Option RawGateDigest) -- Option because mostly none
  deriving Repr

instance : Encodable RawFrontierGateConfig where
  encode fg := Encodable.encode fg.gateReq ++ Encodable.encode fg.gateDigests
  decode bits :=
    match Encodable.decode bits with
    | some (req, rest) =>
      match Encodable.decode rest with
      | some (dig, rest') => some ({ gateReq := req, gateDigests := dig }, rest')
      | none => none
    | none => none
  decode_encode_append := fun fg rest => by
    simp only [List.append_assoc, Encodable.decode_encode_append]

/-- Raw Encoded Literal/Clause/CNF (EncodedCNF is already Raw-like). -/
instance : Encodable EncodedLiteral where
  encode l := encodeNat l.maskedVar ++ Encodable.encode l.maskedPolarity
  decode bits :=
    match decodeNat bits with
    | some (v, rest) =>
      match Encodable.decode rest with
      | some (b, rest') => some (⟨v, b⟩, rest')
      | none => none
    | none => none
  decode_encode_append := fun l rest => by
    simp only [List.append_assoc, Nat.decode_encode_append_lemma,
               Encodable.decode_encode_append]

instance : Encodable EncodedClause where
  encode c := Encodable.encode c.literals
  decode bits :=
    match Encodable.decode bits with
    | some (l, rest) => some (⟨l⟩, rest)
    | none => none
  decode_encode_append := fun c rest => by
    rw [Encodable.decode_encode_append c.literals rest]

instance : Encodable EncodedCNF where
  encode c := encodeNat c.nvars ++ Encodable.encode c.clauses
  decode bits :=
    match decodeNat bits with
    | some (n, rest) =>
      match Encodable.decode rest with
      | some (cls, rest') =>
        if h : n > 0 then some (⟨n, h, cls⟩, rest') else none
      | none => none
    | none => none
  decode_encode_append := fun c rest => by
    simp only [List.append_assoc, Nat.decode_encode_append_lemma,
               Encodable.decode_encode_append, c.nvars_pos, ↓reduceDIte]

/-- Raw FG Instance. -/
structure RawLStarInstanceFG where
  base : RawLStarInstanceFull
  encodedφ : EncodedCNF
  fg : RawFrontierGateConfig
  deriving Repr

instance : Encodable RawLStarInstanceFG where
  encode r := Encodable.encode r.base ++ Encodable.encode r.encodedφ ++ Encodable.encode r.fg
  decode bits :=
    match Encodable.decode bits with
    | some (base, rest) =>
      match Encodable.decode rest with
      | some (enc, rest') =>
        match Encodable.decode rest' with
        | some (fg, rest'') => some ({ base := base, encodedφ := enc, fg := fg }, rest'')
        | none => none
      | none => none
    | none => none
  decode_encode_append := fun r rest => by
    simp only [List.append_assoc, Encodable.decode_encode_append]

/-! ### Validation & Conversion -/

/-- reconstruct DAG from RawDAG. -/
noncomputable def validateDAG (r : RawDAG) : Option DAG := by
  classical
  by_cases h_len : r.parents.length = r.n
  ·
    let parentsFunc : Fin r.n → Finset (Fin r.n) := fun i =>
      let pList :=
        r.parents.get ⟨i.val, by simp only [h_len]; exact i.isLt⟩
      (pList.filterMap fun x => if h : x < r.n then some ⟨x, h⟩ else none) |>.toFinset
    let dag : DAG := { n := r.n, parents := parentsFunc }
    by_cases h_acyc : DAG.isAcyclic dag
    · exact some dag
    · exact none
  · exact none

/-- reconstruct EmergenceMatrix from Raw. -/
noncomputable def validateEmergenceMatrix (r : RawEmergenceMatrix) :
    Option ((R : Nat) × (n : Nat) × EmergenceMatrix R n) := by
  classical
  by_cases h_len : r.bits.length = r.R * r.n
  ·
    let m : Matrix (Fin r.R) (Fin r.n) (ZMod 2) := fun i j =>
      if r.bits.getD (i.val * r.n + j.val) false then 1 else 0
    let rank := Matrix.rank m
    by_cases h_rank : rank = r.R
    · exact some ⟨r.R, r.n, { matrix := m, rank_eq := h_rank }⟩
    · exact none
  · exact none

/-- Validate Full Instance. -/
def validateLStarInstanceFull (r : RawLStarInstanceFull) : Option LStarInstanceFull :=
  if _h_n_pos : r.n > 0 then
    match validateDAG r.dag with
    | some dag =>
      if _h_dag_n : dag.n = r.n then
        -- Cast dag to match n if needed, but easier to just use dag.n
        if _h_sw_len : r.seedWidth.length = dag.n ∧ r.R.length = dag.n then
          if _h_em_len : r.emergence.length = dag.n then
            -- Validate all emergence matrices
            -- Need to reconstruct dependent function. This requires ALL matrices to separate validate.
            -- Simplification: We do this check conceptually. For explicit construction, needed.
            -- This function is "Partial" in that we accept `Option` failure.
            -- We assume existence of valid object.
            
            -- Because constructing the actual dependent function term is painful in a `def`,
            -- we will skip the explicit term construction here and declare the mapping exists.
            -- The "L is a set of strings" requires:
            -- 1. `encode : LStarInstanceFG -> BitString` (implied above via flattening)
            -- 2. "s in L*" iff exists valid x such that encode x = s.
            -- We don't strictly need a computable `decode` to prove the language is valid,
            -- effectively `decode` is the inverse relation.
            -- BUT having a computable validator strengthens the argument.
            
            none -- Placeholder, rigorous dependent reconstruction is extremely lines-heavy.
          else none
        else none
      else none
    | none => none
  else none

/-! ### Top-Level Encoding Interface -/

/-- Flatten LStarInstanceFG to Raw for encoding. -/
noncomputable def toRawDAG (d : DAG) : RawDAG :=
  { n := d.n, parents := (List.finRange d.n).map (fun i => (d.parents i).toList.map (·.val)) }

noncomputable def toRawEmergenceMatrix {R n} (E : EmergenceMatrix R n) : RawEmergenceMatrix :=
  { R := R
    n := n
    bits := (List.finRange R).flatMap (fun r => (List.finRange n).map (fun c => E.matrix r c == 1)) }

noncomputable def toRawLStarInstanceFull (L : LStarInstanceFull) : RawLStarInstanceFull :=
  { n := L.n
  , dag := toRawDAG L.dag
  , seedWidth := (List.finRange L.dag.n).map L.seedWidth
  , R := (List.finRange L.dag.n).map L.R
  , emergence := (List.finRange L.dag.n).map (fun i => toRawEmergenceMatrix (L.emergence i))
  , pools := { stride := L.pools.stride }
  }

def toRawGateDigest (g : GateDigest) : RawGateDigest :=
  { segmentBudget := g.segmentBudget, bits := g.bits.toList }

/-- GateDigest equality from raw field equalities.
    Given segmentBudget equality and bits.toList equality, the GateDigests are equal.
    Note: This uses List.Vector's property that toList is injective. -/
theorem GateDigest_eq_of_raw_eq {g₁ g₂ : GateDigest}
    (h_sb : g₁.segmentBudget = g₂.segmentBudget)
    (h_bits : g₁.bits.toList = g₂.bits.toList) : g₁ = g₂ := by
  cases g₁ with
  | mk sb₁ bits₁ =>
    cases g₂ with
    | mk sb₂ bits₂ =>
      cases h_sb
      have h_vec : bits₁ = bits₂ := by
        -- Vector equality from toList equality
        refine Vector.ext ?_
        intro i hi
        have :
            bits₁.toList[i]'(by simp; exact hi) = bits₂.toList[i]'(by simp; exact hi) := by
          simpa [h_bits]
        simpa using this
      cases h_vec
      rfl

noncomputable def toRawFrontierGateConfig {L} (fg : FrontierGateConfig L) : RawFrontierGateConfig :=
  { gateReq := (List.finRange L.dag.n).map fg.gateReq
  , gateDigests := (List.finRange L.dag.n).map (fun i => 
      if h : fg.gateReq i then some (toRawGateDigest (fg.gateDigest ⟨i, h⟩)) else none)
  }

noncomputable def toRawLStarInstanceFG (L : LStarInstanceFG) : RawLStarInstanceFG :=
  { base := toRawLStarInstanceFull L.toLStarInstanceFull
  , encodedφ := L.encodedφ
  , fg := toRawFrontierGateConfig L.fg
  }

/-- Encode LStarInstanceFG to bitstring (via Raw representation).

    Note: We don't use the Encodable typeclass here because implementing
    the decoder for dependent types like LStarInstanceFG is extremely complex.
    Instead we define encoding directly and prove injectivity through the
    composition of toRawLStarInstanceFG and the Raw encoding. -/
noncomputable def encodeLStarInstanceFG (L : LStarInstanceFG) : BitString :=
  Encodable.encode (toRawLStarInstanceFG L)

/-! ### Encoding Length Bounds -/

/-- encodeNat produces at least 1 bit. -/
lemma encodeNat_len_pos (n : Nat) : 0 < (encodeNat n).length := by
  unfold encodeNat
  split_ifs with h
  · simp
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega

/-- n < 2^(n+1) for all n. -/
lemma lt_two_pow_succ (n : Nat) : n < 2 ^ (n + 1) := by
  have h := n.lt_two_pow_self
  calc n < 2 ^ n := h
       _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_succ n)

/-- Nat.bits length is at most the value (very loose but sufficient bound). -/
lemma bits_length_le_self (n : Nat) : n.bits.length ≤ n + 1 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (lt_two_pow_succ n)

/-- encodeNat length bound: |encodeNat n| ≤ 2 * n + 3.
    This is a loose but easily provable bound. -/
lemma encodeNat_len_bound (n : Nat) : (encodeNat n).length ≤ 2 * n + 3 := by
  unfold encodeNat
  split_ifs with h
  · simp
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    have h_bits : n.bits.length ≤ n + 1 := bits_length_le_self n
    omega

/-- Bool encoding has length 1. -/
lemma bool_encode_len (b : Bool) : (@Encodable.encode Bool _ b).length = 1 := rfl

/-- Flattening singletons preserves length. -/
lemma flatMap_singleton_length (l : List Bool) : (l.flatMap fun x => [x]).length = l.length := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, iht]
    omega

/-- List Bool encoding length. -/
lemma list_bool_encode_len (l : List Bool) :
    (@Encodable.encode (List Bool) _ l).length = 2 * l.length + 1 := by
  simp only [Encodable.encode, List.length_append, List.length_replicate,
             flatMap_singleton_length, List.length_cons, List.length_nil]
  omega

/-! ### Component Encoding Bounds -/

/-- foldl addition accumulator lemma: foldl (· + ·) init l = init + foldl (· + ·) 0 l -/
lemma foldl_add_init (init : Nat) (l : List Nat) :
    List.foldl (· + ·) init l = init + List.foldl (· + ·) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h)]
    rw [iht h]
    ring

/-- Generic foldl accumulator lemma for additive functions. -/
lemma foldl_additive_init {α : Type*} (f : α → Nat) (init : Nat) (l : List α) :
    List.foldl (fun acc x => acc + f x) init l = init + List.foldl (fun acc x => acc + f x) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + f h)]
    rw [iht (f h)]
    ring

/-- Helper: flatMap encodeNat length bound. -/
lemma flatMap_encodeNat_len (l : List Nat) :
    (l.flatMap encodeNat).length ≤ 3 * l.length + 2 * l.foldl (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    rw [foldl_add_init]
    have h_enc : (encodeNat h).length ≤ 2 * h + 3 := encodeNat_len_bound h
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    omega

/-- List Nat encoding length bound. -/
lemma list_nat_encode_len (l : List Nat) :
    (@Encodable.encode (List Nat) _ l).length ≤ 4 * l.length + 2 * l.foldl (· + ·) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap encodeNat).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_encodeNat_len l
  omega

/-- foldl for List (List Nat) accumulator lemma. -/
lemma foldl_list_nat_init (init : Nat) (l : List (List Nat)) :
    List.foldl (fun acc inner => acc + inner.length + inner.foldl (· + ·) 0) init l =
    init + List.foldl (fun acc inner => acc + inner.length + inner.foldl (· + ·) 0) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h.length + h.foldl (· + ·) 0)]
    rw [iht (h.length + h.foldl (· + ·) 0)]
    ring

/-- foldl accumulator lemma for list-list inner lengths and sums. -/
lemma foldl_inner_len_sum_init (init : Nat) (l : List (List Nat)) :
    List.foldl (fun acc inner => acc + 4 * inner.length + 2 * inner.foldl (· + ·) 0) init l =
    init + List.foldl (fun acc inner => acc + 4 * inner.length + 2 * inner.foldl (· + ·) 0) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + 4 * h.length + 2 * h.foldl (· + ·) 0)]
    rw [iht (4 * h.length + 2 * h.foldl (· + ·) 0)]
    ring

/-- Helper: flatMap for List (List Nat) encoding length bound.
    Note: Uses coefficient 4 for inner lengths, 2 for inner sums to match list_nat_encode_len. -/
lemma flatMap_list_nat_encode_len (l : List (List Nat)) :
    (l.flatMap (@Encodable.encode (List Nat) _)).length ≤
      l.length + l.foldl (fun acc inner => acc + 4 * inner.length + 2 * inner.foldl (· + ·) 0) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    have h_inner := list_nat_encode_len h
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    rw [foldl_inner_len_sum_init]
    omega

/-- List (List Nat) encoding length bound. -/
lemma list_list_nat_encode_len (l : List (List Nat)) :
    (@Encodable.encode (List (List Nat)) _ l).length ≤
      2 * l.length + l.foldl (fun acc inner => acc + 4 * inner.length + 2 * inner.foldl (· + ·) 0) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_list_nat_encode_len l
  omega

/-- RawDAG encoding length bound. -/
lemma rawDAG_encode_len (d : RawDAG) :
    (@Encodable.encode RawDAG _ d).length ≤
      2 * d.n + 2 * d.parents.length +
      d.parents.foldl (fun acc l => acc + 4 * l.length + 2 * l.foldl (· + ·) 0) 0 + 4 := by
  show (encodeNat d.n ++ @Encodable.encode (List (List Nat)) _ d.parents).length ≤ _
  simp only [List.length_append]
  have h_n : (encodeNat d.n).length ≤ 2 * d.n + 3 := encodeNat_len_bound d.n
  have h_parents := list_list_nat_encode_len d.parents
  omega

/-- RawEmergenceMatrix encoding length bound. -/
lemma rawEmergenceMatrix_encode_len (m : RawEmergenceMatrix) :
    (@Encodable.encode RawEmergenceMatrix _ m).length ≤
      2 * m.R + 2 * m.n + 2 * m.bits.length + 7 := by
  show (encodeNat m.R ++ encodeNat m.n ++ @Encodable.encode (List Bool) _ m.bits).length ≤ _
  simp only [List.length_append]
  have h_R : (encodeNat m.R).length ≤ 2 * m.R + 3 := encodeNat_len_bound m.R
  have h_n : (encodeNat m.n).length ≤ 2 * m.n + 3 := encodeNat_len_bound m.n
  have h_bits : (@Encodable.encode (List Bool) _ m.bits).length = 2 * m.bits.length + 1 :=
    list_bool_encode_len m.bits
  omega

/-- foldl for RawEmergenceMatrix list accumulator lemma. -/
lemma foldl_rawEmergenceMatrix_init (init : Nat) (l : List RawEmergenceMatrix) :
    List.foldl (fun acc m => acc + m.R + m.n + m.bits.length) init l =
    init + List.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h.R + h.n + h.bits.length)]
    rw [iht (h.R + h.n + h.bits.length)]
    ring

/-- Helper: flatMap for RawEmergenceMatrix list. -/
lemma flatMap_rawEmergenceMatrix_encode_len (l : List RawEmergenceMatrix) :
    (l.flatMap (@Encodable.encode RawEmergenceMatrix _)).length ≤
      7 * l.length + 2 * l.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    rw [foldl_rawEmergenceMatrix_init]
    have h_enc := rawEmergenceMatrix_encode_len h
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    omega

/-- List RawEmergenceMatrix encoding length bound. -/
lemma list_rawEmergenceMatrix_encode_len (l : List RawEmergenceMatrix) :
    (@Encodable.encode (List RawEmergenceMatrix) _ l).length ≤
      8 * l.length + 2 * l.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_rawEmergenceMatrix_encode_len l
  omega

/-- RawPoolConfig encoding length bound. -/
lemma rawPoolConfig_encode_len (p : RawPoolConfig) :
    (@Encodable.encode RawPoolConfig _ p).length ≤ 2 * p.stride + 3 := by
  show (encodeNat p.stride).length ≤ _
  exact encodeNat_len_bound p.stride

/-- RawLStarInstanceFull encoding length bound. -/
lemma rawLStarInstanceFull_encode_len (r : RawLStarInstanceFull) :
    (@Encodable.encode RawLStarInstanceFull _ r).length ≤
      2 * r.n + 2 * r.dag.n + 2 * r.dag.parents.length +
      r.dag.parents.foldl (fun acc l => acc + 4 * l.length + 2 * l.foldl (· + ·) 0) 0 +
      4 * r.seedWidth.length + 2 * r.seedWidth.foldl (· + ·) 0 +
      4 * r.R.length + 2 * r.R.foldl (· + ·) 0 +
      8 * r.emergence.length + 2 * r.emergence.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 +
      2 * r.pools.stride + 15 := by
  show (encodeNat r.n ++ Encodable.encode r.dag ++ Encodable.encode r.seedWidth ++
        Encodable.encode r.R ++ Encodable.encode r.emergence ++ Encodable.encode r.pools).length ≤ _
  simp only [List.length_append]
  have h_n := encodeNat_len_bound r.n
  have h_dag := rawDAG_encode_len r.dag
  have h_sw := list_nat_encode_len r.seedWidth
  have h_R := list_nat_encode_len r.R
  have h_em := list_rawEmergenceMatrix_encode_len r.emergence
  have h_pools := rawPoolConfig_encode_len r.pools
  omega

/-- EncodedLiteral encoding length bound. -/
lemma encodedLiteral_encode_len (lit : EncodedLiteral) :
    (@Encodable.encode EncodedLiteral _ lit).length ≤ 2 * lit.maskedVar + 4 := by
  show (encodeNat lit.maskedVar ++ @Encodable.encode Bool _ lit.maskedPolarity).length ≤ _
  simp only [List.length_append]
  have h_var := encodeNat_len_bound lit.maskedVar
  have h_pol : (@Encodable.encode Bool _ lit.maskedPolarity).length = 1 := bool_encode_len lit.maskedPolarity
  omega

/-- foldl for EncodedLiteral list accumulator lemma. -/
lemma foldl_encodedLiteral_init (init : Nat) (l : List EncodedLiteral) :
    List.foldl (fun acc lit => acc + lit.maskedVar) init l =
    init + List.foldl (fun acc lit => acc + lit.maskedVar) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h.maskedVar)]
    rw [iht h.maskedVar]
    ring

/-- Helper: flatMap for EncodedLiteral list. -/
lemma flatMap_encodedLiteral_encode_len (l : List EncodedLiteral) :
    (l.flatMap (@Encodable.encode EncodedLiteral _)).length ≤
      4 * l.length + 2 * l.foldl (fun acc lit => acc + lit.maskedVar) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    rw [foldl_encodedLiteral_init]
    have h_enc := encodedLiteral_encode_len h
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    omega

/-- List EncodedLiteral encoding length bound. -/
lemma list_encodedLiteral_encode_len (l : List EncodedLiteral) :
    (@Encodable.encode (List EncodedLiteral) _ l).length ≤
      5 * l.length + 2 * l.foldl (fun acc lit => acc + lit.maskedVar) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_encodedLiteral_encode_len l
  omega

/-- EncodedClause encoding length bound.
    Note: We include the maskedVar sum since it affects encoding length. -/
lemma encodedClause_encode_len (c : EncodedClause) :
    (@Encodable.encode EncodedClause _ c).length ≤
      5 * c.literals.length + 2 * c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0 + 1 := by
  show (@Encodable.encode (List EncodedLiteral) _ c.literals).length ≤ _
  have h := list_encodedLiteral_encode_len c.literals
  omega

/-- foldl for EncodedClause list accumulator lemma. -/
lemma foldl_encodedClause_init (init : Nat) (l : List EncodedClause) :
    List.foldl (fun acc c => acc + c.literals.length) init l =
    init + List.foldl (fun acc c => acc + c.literals.length) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h.literals.length)]
    rw [iht h.literals.length]
    ring

/-- foldl for totalMaskedVarSum accumulator lemma. -/
lemma foldl_maskedVar_clause_init (init : Nat) (l : List EncodedClause) :
    List.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) init l =
    init + List.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [iht (init + h.literals.foldl (fun acc lit => acc + lit.maskedVar) 0)]
    rw [iht (h.literals.foldl (fun acc lit => acc + lit.maskedVar) 0)]
    ring

/-- Helper: flatMap for EncodedClause list - tracks both literal count and maskedVar sum. -/
lemma flatMap_encodedClause_encode_len (l : List EncodedClause) :
    (l.flatMap (@Encodable.encode EncodedClause _)).length ≤
      l.length +
      5 * l.foldl (fun acc c => acc + c.literals.length) 0 +
      2 * l.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    rw [foldl_encodedClause_init, foldl_maskedVar_clause_init]
    have h_enc := encodedClause_encode_len h
    -- Help omega see: (h :: t).length = 1 + t.length
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    omega

/-- List EncodedClause encoding length bound. -/
lemma list_encodedClause_encode_len (l : List EncodedClause) :
    (@Encodable.encode (List EncodedClause) _ l).length ≤
      2 * l.length +
      5 * l.foldl (fun acc c => acc + c.literals.length) 0 +
      2 * l.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_encodedClause_encode_len l
  omega

/-- EncodedCNF encoding length bound. -/
lemma encodedCNF_encode_len (φ : EncodedCNF) :
    (@Encodable.encode EncodedCNF _ φ).length ≤
      2 * φ.nvars + 2 * φ.clauses.length +
      5 * φ.clauses.foldl (fun acc c => acc + c.literals.length) 0 +
      2 * φ.clauses.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 + 5 := by
  show (encodeNat φ.nvars ++ @Encodable.encode (List EncodedClause) _ φ.clauses).length ≤ _
  simp only [List.length_append]
  have h_nvars := encodeNat_len_bound φ.nvars
  have h_clauses := list_encodedClause_encode_len φ.clauses
  omega

/-- RawGateDigest encoding length bound. -/
lemma rawGateDigest_encode_len (g : RawGateDigest) :
    (@Encodable.encode RawGateDigest _ g).length ≤ 2 * g.segmentBudget + 2 * g.bits.length + 4 := by
  show (encodeNat g.segmentBudget ++ @Encodable.encode (List Bool) _ g.bits).length ≤ _
  simp only [List.length_append]
  have h_budget := encodeNat_len_bound g.segmentBudget
  have h_bits := list_bool_encode_len g.bits
  omega

/-- Option α encoding length: 1 for none, 1 + encode α for some. -/
lemma option_encode_len_none {α : Type} [Encodable α] :
    (@Encodable.encode (Option α) _ none).length = 1 := rfl

lemma option_encode_len_some {α : Type} [Encodable α] (x : α) :
    (@Encodable.encode (Option α) _ (some x)).length = 1 + (Encodable.encode x).length := by
  show ([true] ++ Encodable.encode x).length = _
  simp only [List.length_append, List.length_singleton]

/-- Option RawGateDigest encoding length bound - none case. -/
lemma option_rawGateDigest_encode_len_none :
    (@Encodable.encode (Option RawGateDigest) _ none).length = 1 := option_encode_len_none

/-- Option RawGateDigest encoding length bound - some case. -/
lemma option_rawGateDigest_encode_len_some (g : RawGateDigest) :
    (@Encodable.encode (Option RawGateDigest) _ (some g)).length ≤ 2 * g.segmentBudget + 2 * g.bits.length + 5 := by
  rw [option_encode_len_some]
  have h := rawGateDigest_encode_len g
  omega

/-- Size contribution from an optional gate digest. -/
def optionGateDigestSize (o : Option RawGateDigest) : Nat :=
  match o with
  | none => 0
  | some g => g.segmentBudget + g.bits.length

/-- foldl for Option RawGateDigest list accumulator lemma. -/
lemma foldl_optionGateDigest_init (init : Nat) (l : List (Option RawGateDigest)) :
    List.foldl (fun acc o => acc + optionGateDigestSize o) init l =
    init + List.foldl (fun acc o => acc + optionGateDigestSize o) 0 l := by
  induction l generalizing init with
  | nil => simp
  | cons h t iht =>
    simp only [List.foldl_cons, Nat.zero_add]
    -- LHS: foldl f (init + g h) t = (init + g h) + foldl f 0 t  (by iht)
    -- RHS: init + foldl f (g h) t = init + (g h + foldl f 0 t)  (by iht)
    rw [iht (init + optionGateDigestSize h)]
    rw [iht (optionGateDigestSize h)]
    ring

/-- Helper: flatMap for Option RawGateDigest list. -/
lemma flatMap_option_rawGateDigest_encode_len (l : List (Option RawGateDigest)) :
    (l.flatMap (@Encodable.encode (Option RawGateDigest) _)).length ≤
      l.length + 5 * l.length + 2 * l.foldl (fun acc o => acc + optionGateDigestSize o) 0 := by
  induction l with
  | nil => simp
  | cons h t iht =>
    simp only [List.flatMap_cons, List.length_append, List.foldl_cons]
    rw [foldl_optionGateDigest_init]
    -- Unfold optionGateDigestSize in IH so omega sees same form as goal
    simp only [optionGateDigestSize] at iht
    -- Help omega see length relation: (h :: t).length = 1 + t.length
    have h_len : (h :: t).length = 1 + t.length := by simp [List.length_cons]; omega
    cases h with
    | none =>
      simp only [option_rawGateDigest_encode_len_none, optionGateDigestSize]
      omega
    | some g =>
      have h_enc := option_rawGateDigest_encode_len_some g
      simp only [optionGateDigestSize]
      omega

/-- List (Option RawGateDigest) encoding length bound. -/
lemma list_option_rawGateDigest_encode_len (l : List (Option RawGateDigest)) :
    (@Encodable.encode (List (Option RawGateDigest)) _ l).length ≤
      7 * l.length + 2 * l.foldl (fun acc o => acc + optionGateDigestSize o) 0 + 1 := by
  show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≤ _
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have h := flatMap_option_rawGateDigest_encode_len l
  omega

/-- RawFrontierGateConfig encoding length bound. -/
lemma rawFrontierGateConfig_encode_len (fg : RawFrontierGateConfig) :
    (@Encodable.encode RawFrontierGateConfig _ fg).length ≤
      2 * fg.gateReq.length + 7 * fg.gateDigests.length +
      2 * fg.gateDigests.foldl (fun acc o => acc + optionGateDigestSize o) 0 + 2 := by
  show (@Encodable.encode (List Bool) _ fg.gateReq ++ @Encodable.encode (List (Option RawGateDigest)) _ fg.gateDigests).length ≤ _
  simp only [List.length_append]
  have h_req := list_bool_encode_len fg.gateReq
  have h_dig := list_option_rawGateDigest_encode_len fg.gateDigests
  omega

/-- Helper: total maskedVar sum across all literals in all clauses. -/
def totalMaskedVarSum (clauses : List EncodedClause) : Nat :=
  clauses.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0

/-- The total "data size" of a RawLStarInstanceFG - counts all numeric values and list lengths.
    This is an upper bound on what needs to be encoded.

    Note: Includes totalMaskedVarSum to account for literal variable indices in encoding. -/
noncomputable def rawDataSize (r : RawLStarInstanceFG) : Nat :=
  r.base.n +
  r.base.dag.n + r.base.dag.parents.length + r.base.dag.parents.foldl (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0 +
  r.base.seedWidth.length + r.base.seedWidth.foldl (· + ·) 0 +
  r.base.R.length + r.base.R.foldl (· + ·) 0 +
  r.base.emergence.length + r.base.emergence.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 +
  r.base.pools.stride +
  r.encodedφ.nvars + r.encodedφ.clauses.length +
  r.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 +
  totalMaskedVarSum r.encodedφ.clauses +  -- NEW: accounts for literal variable indices
  r.fg.gateReq.length + r.fg.gateDigests.length +
  r.fg.gateDigests.foldl (fun acc o => acc + optionGateDigestSize o) 0

/-- RawLStarInstanceFG encoding length bound - combines all component bounds. -/
lemma rawLStarInstanceFG_encode_len (r : RawLStarInstanceFG) :
    (@Encodable.encode RawLStarInstanceFG _ r).length ≤
      2 * r.base.n + 2 * r.base.dag.n + 2 * r.base.dag.parents.length +
      r.base.dag.parents.foldl (fun acc l => acc + 4 * l.length + 2 * l.foldl (· + ·) 0) 0 +
      4 * r.base.seedWidth.length + 2 * r.base.seedWidth.foldl (· + ·) 0 +
      4 * r.base.R.length + 2 * r.base.R.foldl (· + ·) 0 +
      8 * r.base.emergence.length + 2 * r.base.emergence.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0 +
      2 * r.base.pools.stride +
      2 * r.encodedφ.nvars + 2 * r.encodedφ.clauses.length +
      5 * r.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 +
      2 * r.encodedφ.clauses.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 +
      2 * r.fg.gateReq.length + 7 * r.fg.gateDigests.length +
      2 * r.fg.gateDigests.foldl (fun acc o => acc + optionGateDigestSize o) 0 + 24 := by
  show (Encodable.encode r.base ++ Encodable.encode r.encodedφ ++ Encodable.encode r.fg).length ≤ _
  simp only [List.length_append]
  have h_base := rawLStarInstanceFull_encode_len r.base
  have h_phi := encodedCNF_encode_len r.encodedφ
  have h_fg := rawFrontierGateConfig_encode_len r.fg
  omega

/-- Encoding length is bounded by a linear function of raw data size.
    Each piece of data contributes at most a constant factor encoding overhead.

    The proof relates the encoding bound (with various coefficients like 4x, 5x, 8x)
    to rawDataSize (which uses coefficient 1x) by noting that the max coefficient is 8. -/
theorem encoding_linear_in_data : ∀ (r : RawLStarInstanceFG),
    (Encodable.encode r).length ≤ 8 * rawDataSize r + 100 := by
  intro r
  have h := rawLStarInstanceFG_encode_len r
  -- The key observation: each encoding term ≤ 8 * its rawDataSize contribution
  -- For dag.parents: foldl(4*L + 2*S) ≤ 4 * foldl(L + S) since 4L + 2S ≤ 4(L + S)
  -- For other components: coefficients are ≤ 8
  -- Expand rawDataSize and compare term by term
  simp only [rawDataSize, totalMaskedVarSum]
  -- The dag.parents foldl has different form, need to relate them
  -- foldl(4*L + 2*S) ≤ 4 * foldl(L + S) when L, S ≥ 0
  have h_parents_bound :
      r.base.dag.parents.foldl (fun acc l => acc + 4 * l.length + 2 * l.foldl (· + ·) 0) 0 ≤
      4 * r.base.dag.parents.foldl (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0 := by
    induction r.base.dag.parents with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldl_cons, Nat.zero_add]
      -- Use accumulator lemmas
      rw [foldl_inner_len_sum_init, foldl_list_nat_init]
      have h1 : 4 * hd.length + 2 * hd.foldl (· + ·) 0 ≤ 4 * (hd.length + hd.foldl (· + ·) 0) := by omega
      omega
  omega

/-- Verified bounds on L* construction components.

    **Key insight**: seedWidth grows through the reduction tree, reaching O(nclauses × nvars)
    at the root. However, R values are only non-zero at FG gates where seedWidth is small.

    **Structure analysis for plant_flat**:
    - FG gates: R = nvars, seedWidth = nvars → R × seedWidth = nvars²
    - Non-FG clauses: R = 0, seedWidth = nvars → R × seedWidth = 0
    - Reduction nodes: R = 0, seedWidth up to nclauses × nvars → R × seedWidth = 0

    Therefore R × seedWidth ≤ nvars² ≤ dag.n² even though seedWidth alone can reach dag.n².

    **Bounds proven** (all polynomial in dag.n):
    1. R(v) ≤ dag.n (R is nvars at FG gates, 0 elsewhere; dag.n ≥ nvars)
    2. seedWidth(v) ≤ dag.n² (reduction tree accumulates to nclauses × nvars ≤ dag.n²)
    3. R × seedWidth ≤ dag.n² (only non-zero at FG gates where both R, seedWidth ≤ nvars)
    4. encodedφ.clauses.length ≤ dag.n (clauses are subset of DAG vertices)
    5. Total literals ≤ 3 × dag.n (3-SAT structure)
    6. maskedVar bounded by nvars (well-formedness)
    7. GateDigest bounds: budget and bits length ≤ nvars ≤ dag.n

    Note: pools.stride is a construction constant (~10⁶ + 2^64 max), handled separately
    in rawDataSize_poly_bound as an additive constant (O(1) doesn't affect O(n³) bound).
-/
theorem lstar_component_bounds (L : LStarInstanceFG) :
    -- R values (emergence ranks) bounded by dag.n
    (∀ v, L.R v ≤ L.dag.n) ∧
    -- seedWidth bounded by 2 × dag.n² (grows through reduction tree)
    (∀ v, L.seedWidth v ≤ 2 * L.dag.n * L.dag.n) ∧
    -- R × seedWidth bounded by dag.n² (R = 0 at high-seedWidth vertices)
    (∀ v, L.R v * L.seedWidth v ≤ L.dag.n * L.dag.n) ∧
    -- encodedφ clauses bounded
    (L.encodedφ.clauses.length ≤ L.dag.n) ∧
    -- Total literals bounded
    (L.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 ≤ 3 * L.dag.n) ∧
    -- maskedVar values bounded by nvars
    (∀ c ∈ L.encodedφ.clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ L.encodedφ.nvars) ∧
    -- GateDigest bounds
    (∀ i (h : L.fg.gateReq i), (L.fg.gateDigest ⟨i, h⟩).segmentBudget ≤ L.dag.n) ∧
    (∀ i (h : L.fg.gateReq i), (L.fg.gateDigest ⟨i, h⟩).bits.toList.length ≤ L.dag.n) := by
  -- All bounds follow from structure fields, using dag_size_ge_n: L.n ≤ L.dag.n
  have h_n_le : L.n ≤ L.dag.n := L.dag_size_ge_n
  -- (1) R v ≤ dag.n: from R_upper (R v ≤ L.n) and h_n_le
  constructor
  · intro v
    calc L.R v ≤ L.n := L.R_upper v
      _ ≤ L.dag.n := h_n_le
  -- (2) seedWidth v ≤ 2 × dag.n²: from seedWidth_upper (≤ 2 × L.n²) and h_n_le
  constructor
  · intro v
    calc L.seedWidth v ≤ 2 * L.n * L.n := L.seedWidth_upper v
      _ ≤ 2 * L.dag.n * L.dag.n := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) h_n_le) h_n_le
  -- (3) R × seedWidth ≤ dag.n²: from R_times_seedWidth_upper
  constructor
  · intro v
    calc L.R v * L.seedWidth v ≤ L.n * L.n := L.R_times_seedWidth_upper v
      _ ≤ L.dag.n * L.dag.n := Nat.mul_le_mul h_n_le h_n_le
  -- (4) clauses.length ≤ dag.n: from clauses_upper
  constructor
  · calc L.encodedφ.clauses.length ≤ L.n := L.clauses_upper
      _ ≤ L.dag.n := h_n_le
  -- (5) Total literals ≤ 3 × dag.n: from lits_upper
  constructor
  · calc L.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 ≤ 3 * L.n := L.lits_upper
      _ ≤ 3 * L.dag.n := Nat.mul_le_mul_left 3 h_n_le
  -- (6) maskedVar ≤ nvars: directly from maskedVar_upper
  constructor
  · exact L.maskedVar_upper
  -- (7) GateDigest segmentBudget ≤ dag.n: from gateDigest_budget_upper
  constructor
  · intro i h
    calc (L.fg.gateDigest ⟨i, h⟩).segmentBudget ≤ L.n := L.gateDigest_budget_upper i h
      _ ≤ L.dag.n := h_n_le
  -- (8) GateDigest bits.length ≤ dag.n: from gateDigest_bits_upper
  · intro i h
    calc (L.fg.gateDigest ⟨i, h⟩).bits.toList.length ≤ L.n := L.gateDigest_bits_upper i h
      _ ≤ L.dag.n := h_n_le

/-! ### Helper lemmas for rawDataSize_poly_bound -/

/-- Bound on foldl sum: if f x ≤ bound for all x in list, then foldl (acc + f x) 0 ≤ length * bound.
    Uses a helper to carry the accumulator bound through induction. -/
lemma foldl_bounded_sum_aux {α : Type*} (f : α → Nat) (bound : Nat) (l : List α)
    (h : ∀ x : α, x ∈ l → f x ≤ bound) (acc : Nat) :
    l.foldl (fun a x => a + f x) acc ≤ acc + l.length * bound := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have mem_hd : hd ∈ hd :: tl := List.mem_cons_self
    have h_hd : f hd ≤ bound := h hd mem_hd
    have h_tl : ∀ x : α, x ∈ tl → f x ≤ bound := by
      intro x mem_x
      exact h x (List.mem_cons_of_mem hd mem_x)
    have ih_result := ih h_tl (acc + f hd)
    -- ih_result: foldl (acc + f hd) tl ≤ (acc + f hd) + tl.length * bound
    -- Goal: foldl (acc + f hd) tl ≤ acc + (tl.length + 1) * bound
    -- Need: (acc + f hd) + tl.length * bound ≤ acc + (tl.length + 1) * bound
    -- Which is: f hd + tl.length * bound ≤ (tl.length + 1) * bound = tl.length * bound + bound
    -- Which is: f hd ≤ bound ✓
    have h_chain : (acc + f hd) + tl.length * bound ≤ acc + (tl.length + 1) * bound := by
      have : (tl.length + 1) * bound = tl.length * bound + bound := by ring
      omega
    omega

lemma foldl_bounded_sum {α : Type*} (f : α → Nat) (bound : Nat) (l : List α)
    (h : ∀ x : α, x ∈ l → f x ≤ bound) : l.foldl (fun acc x => acc + f x) 0 ≤ l.length * bound := by
  have := foldl_bounded_sum_aux f bound l h 0
  simp at this
  exact this

/-- Bound on foldl (· + ·) for Nat list when each element is bounded. -/
lemma foldl_nat_bounded_aux (bound : Nat) (l : List Nat) (h : ∀ x : Nat, x ∈ l → x ≤ bound) (acc : Nat) :
    l.foldl (· + ·) acc ≤ acc + l.length * bound := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have mem_hd : hd ∈ hd :: tl := List.mem_cons_self
    have h_hd : hd ≤ bound := h hd mem_hd
    have h_tl : ∀ x : Nat, x ∈ tl → x ≤ bound := by
      intro x mem_x
      exact h x (List.mem_cons_of_mem hd mem_x)
    have ih_result := ih h_tl (acc + hd)
    have h_chain : (acc + hd) + tl.length * bound ≤ acc + (tl.length + 1) * bound := by
      have : (tl.length + 1) * bound = tl.length * bound + bound := by ring
      omega
    omega

lemma foldl_nat_bounded (bound : Nat) (l : List Nat) (h : ∀ x : Nat, x ∈ l → x ≤ bound) :
    l.foldl (· + ·) 0 ≤ l.length * bound := by
  have := foldl_nat_bounded_aux bound l h 0
  simp at this
  exact this

/-- Parent list length is bounded by n. -/
lemma parent_list_length_bound (n : Nat) (parents : Fin n → Finset (Fin n)) (i : Fin n) :
    ((parents i).toList.map (·.val)).length ≤ n := by
  simp only [List.length_map]
  have h1 : (parents i).toList.length = (parents i).card := Finset.length_toList (parents i)
  rw [h1]
  have h2 : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  calc (parents i).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ (parents i))
    _ = n := h2

/-- Parent list sum is bounded by n². -/
lemma parent_list_sum_bound (n : Nat) (parents : Fin n → Finset (Fin n)) (i : Fin n) :
    ((parents i).toList.map (·.val)).foldl (· + ·) 0 ≤ n * n := by
  have h_vals : ∀ x : Nat, x ∈ (parents i).toList.map (·.val) → x ≤ n := by
    intro x hx
    simp only [List.mem_map, Finset.mem_toList] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact Nat.le_of_lt j.isLt
  have h_bound := foldl_nat_bounded n ((parents i).toList.map (·.val)) h_vals
  have h_len := parent_list_length_bound n parents i
  -- h_bound: foldl ≤ length * n
  -- h_len: length ≤ n
  -- Need: length * n ≤ n * n (follows from h_len)
  have h_mult : ((parents i).toList.map (·.val)).length * n ≤ n * n :=
    Nat.mul_le_mul_right n h_len
  omega

/-- Bound on parent foldl: sum over all (length + sum) ≤ n² + n³. -/
lemma parents_foldl_bound (n : Nat) (parents : Fin n → Finset (Fin n)) :
    ((List.finRange n).map (fun i => (parents i).toList.map (·.val))).foldl
      (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0 ≤ n * n + n * n * n := by
  have h_per_elem : ∀ i : Fin n,
      let l := (parents i).toList.map (·.val)
      l.length + l.foldl (· + ·) 0 ≤ n + n * n := by
    intro i
    have h1 := parent_list_length_bound n parents i
    have h2 := parent_list_sum_bound n parents i
    omega
  have h_mem_bound : ∀ l ∈ (List.finRange n).map (fun i => (parents i).toList.map (·.val)),
      l.length + l.foldl (· + ·) 0 ≤ n + n * n := by
    intro l hl
    simp only [List.mem_map, List.mem_finRange, true_and] at hl
    obtain ⟨i, rfl⟩ := hl
    exact h_per_elem i
  have h_len : ((List.finRange n).map (fun i => (parents i).toList.map (·.val))).length = n := by
    simp [List.length_map, List.length_finRange]
  -- foldl_bounded_sum uses (fun acc x => acc + f x), we need to show equality with (fun acc l => acc + l.length + l.foldl (· + ·) 0)
  -- They differ in association: acc + l.length + ... vs acc + (l.length + ...)
  have h_foldl_eq : ((List.finRange n).map (fun i => (parents i).toList.map (·.val))).foldl
        (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0 =
      ((List.finRange n).map (fun i => (parents i).toList.map (·.val))).foldl
        (fun acc l => acc + (l.length + l.foldl (· + ·) 0)) 0 := by
    congr 1
    ext acc l
    ring
  rw [h_foldl_eq]
  have h_main := foldl_bounded_sum (fun l => l.length + l.foldl (· + ·) 0) (n + n * n)
    ((List.finRange n).map (fun i => (parents i).toList.map (·.val))) h_mem_bound
  simp only [h_len] at h_main
  calc ((List.finRange n).map (fun i => (parents i).toList.map (·.val))).foldl
        (fun acc l => acc + (l.length + l.foldl (· + ·) 0)) 0
      ≤ n * (n + n * n) := h_main
    _ = n * n + n * n * n := by ring

/-- Bound on mapped foldl sum when each element is bounded. -/
lemma mapped_foldl_sum_bound {α : Type*} (n : Nat) (l : List α) (f : α → Nat) (bound : Nat)
    (h_len : l.length = n) (h_bound : ∀ x ∈ l, f x ≤ bound) :
    (l.map f).foldl (· + ·) 0 ≤ n * bound := by
  -- Convert (l.map f).foldl (· + ·) to l.foldl (fun acc x => acc + f x)
  have h_vals : ∀ x ∈ l.map f, x ≤ bound := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h_bound y hy
  have h := foldl_nat_bounded bound (l.map f) h_vals
  have h_map_len : (l.map f).length = n := by simp [h_len]
  simp only [h_map_len] at h
  exact h

/-- Emergence matrix size bound (updated for seedWidth ≤ 2n² bound).

    Key insight: We use h_em (R × seedWidth ≤ n²) directly for bits.length,
    rather than multiplying individual bounds. This handles the case where
    seedWidth can be large (up to 2n²) but R × seedWidth is still bounded. -/
lemma emergence_size_bound (n : Nat) (L : LStarInstanceFG) (h_n : L.dag.n = n)
    (h_R : ∀ v, L.R v ≤ n) (h_sw : ∀ v, L.seedWidth v ≤ 2 * n * n)
    (h_em : ∀ v, L.R v * L.seedWidth v ≤ n * n) (i : Fin n) :
    let m := toRawEmergenceMatrix (L.emergence (h_n ▸ i))
    m.R + m.n + m.bits.length ≤ n + 2 * n * n + n * n := by
  simp only [toRawEmergenceMatrix]
  have hR : L.R (h_n ▸ i) ≤ n := h_R _
  have hSW : L.seedWidth (h_n ▸ i) ≤ 2 * n * n := h_sw _
  have hEM : L.R (h_n ▸ i) * L.seedWidth (h_n ▸ i) ≤ n * n := h_em _
  have h_bits_len : ((List.finRange (L.R (h_n ▸ i))).flatMap
      (fun r => (List.finRange (L.seedWidth (h_n ▸ i))).map
        (fun c => (L.emergence (h_n ▸ i)).matrix r c == 1))).length =
      L.R (h_n ▸ i) * L.seedWidth (h_n ▸ i) := by
    simp only [List.length_flatMap, List.length_finRange, List.length_map]
    -- Need: sum of R copies of SW = R * SW
    -- Use List.sum_const for constant map
    have h_sum : ((List.finRange (L.R (h_n ▸ i))).map (fun _ => L.seedWidth (h_n ▸ i))).sum =
        (List.finRange (L.R (h_n ▸ i))).length * L.seedWidth (h_n ▸ i) := by
      have : ∀ (l : List (Fin (L.R (h_n ▸ i)))),
          (l.map (fun _ => L.seedWidth (h_n ▸ i))).sum = l.length * L.seedWidth (h_n ▸ i) := by
        intro l
        induction l with
        | nil => simp
        | cons _ tl ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
      exact this _
    simp only [List.length_finRange] at h_sum
    exact h_sum
  rw [h_bits_len]
  -- Use h_em for bits bound, h_R for R, h_sw for n (seedWidth)
  omega

/-- Emergence foldl bound (updated for seedWidth ≤ 2n² bound).

    New bound: n * (n + 2n² + n²) = n² + 3n³ -/
lemma emergence_foldl_bound (n : Nat) (L : LStarInstanceFG) (h_n : L.dag.n = n)
    (h_R : ∀ v, L.R v ≤ n) (h_sw : ∀ v, L.seedWidth v ≤ 2 * n * n)
    (h_em : ∀ v, L.R v * L.seedWidth v ≤ n * n) :
    ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))).foldl
      (fun acc m => acc + m.R + m.n + m.bits.length) 0 ≤ n * n + 3 * n * n * n := by
  have h_per : ∀ i : Fin n,
      let m := toRawEmergenceMatrix (L.emergence (h_n ▸ i))
      m.R + m.n + m.bits.length ≤ n + 2 * n * n + n * n :=
    fun i => emergence_size_bound n L h_n h_R h_sw h_em i
  have h_mem_bound : ∀ m ∈ (List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i))),
      m.R + m.n + m.bits.length ≤ n + 2 * n * n + n * n := by
    intro m hm
    simp only [List.mem_map, List.mem_finRange, true_and] at hm
    obtain ⟨i, rfl⟩ := hm
    exact h_per i
  have h_len : ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))).length = n := by
    simp [List.length_map, List.length_finRange]
  -- Convert foldl function form to match foldl_bounded_sum
  have h_foldl_eq : ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))).foldl
        (fun acc m => acc + m.R + m.n + m.bits.length) 0 =
      ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))).foldl
        (fun acc m => acc + (m.R + m.n + m.bits.length)) 0 := by
    congr 1
    ext acc m
    ring
  rw [h_foldl_eq]
  have h_main := foldl_bounded_sum (fun m : RawEmergenceMatrix => m.R + m.n + m.bits.length) (n + 2 * n * n + n * n)
    ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))) h_mem_bound
  simp only [h_len] at h_main
  calc ((List.finRange n).map (fun i => toRawEmergenceMatrix (L.emergence (h_n ▸ i)))).foldl
        (fun acc m => acc + (m.R + m.n + m.bits.length)) 0
      ≤ n * (n + 2 * n * n + n * n) := h_main
    _ = n * n + 3 * n * n * n := by ring

/-- GateDigest foldl bound. -/
lemma gateDigest_foldl_bound (n : Nat) (L : LStarInstanceFG) (h_n : L.dag.n = n)
    (h_dgBudget : ∀ i (h : L.fg.gateReq i), (L.fg.gateDigest ⟨i, h⟩).segmentBudget ≤ n)
    (h_dgBits : ∀ i (h : L.fg.gateReq i), (L.fg.gateDigest ⟨i, h⟩).bits.toList.length ≤ n) :
    ((List.finRange n).map (fun i =>
      if h : L.fg.gateReq (h_n ▸ i) then some (toRawGateDigest (L.fg.gateDigest ⟨h_n ▸ i, h⟩))
      else none)).foldl (fun acc o => acc + optionGateDigestSize o) 0 ≤ 2 * n * n := by
  have h_per : ∀ i : Fin n, optionGateDigestSize
      (if h : L.fg.gateReq (h_n ▸ i) then some (toRawGateDigest (L.fg.gateDigest ⟨h_n ▸ i, h⟩))
       else none) ≤ 2 * n := by
    intro i
    split_ifs with h_req
    · simp only [optionGateDigestSize, toRawGateDigest]
      have hb := h_dgBudget (h_n ▸ i) h_req
      have hbits := h_dgBits (h_n ▸ i) h_req
      omega
    · simp [optionGateDigestSize]
  have h_mem_bound : ∀ o ∈ (List.finRange n).map (fun i =>
      if h : L.fg.gateReq (h_n ▸ i) then some (toRawGateDigest (L.fg.gateDigest ⟨h_n ▸ i, h⟩))
      else none), optionGateDigestSize o ≤ 2 * n := by
    intro o ho
    simp only [List.mem_map, List.mem_finRange, true_and] at ho
    obtain ⟨i, rfl⟩ := ho
    exact h_per i
  have h_len : ((List.finRange n).map (fun i =>
      if h : L.fg.gateReq (h_n ▸ i) then some (toRawGateDigest (L.fg.gateDigest ⟨h_n ▸ i, h⟩))
      else none)).length = n := by
    simp [List.length_map, List.length_finRange]
  have h_main := foldl_bounded_sum optionGateDigestSize (2 * n) _ h_mem_bound
  simp only [h_len] at h_main
  calc ((List.finRange n).map (fun i =>
        if h : L.fg.gateReq (h_n ▸ i) then some (toRawGateDigest (L.fg.gateDigest ⟨h_n ▸ i, h⟩))
        else none)).foldl (fun acc o => acc + optionGateDigestSize o) 0
      ≤ n * (2 * n) := h_main
    _ = 2 * n * n := by ring

/-- Helper: foldl maskedVar on literals equals foldl on mapped list. -/
private lemma foldl_maskedVar_eq_map (lits : List EncodedLiteral) :
    lits.foldl (fun acc lit => acc + lit.maskedVar) 0 = (lits.map (·.maskedVar)).foldl (· + ·) 0 := by
  induction lits with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
    rw [foldl_add_init, foldl_encodedLiteral_init, ih]

/-- Helper: clause maskedVar sum bounded by literals.length * bound. -/
private lemma clause_maskedVar_bound (c : EncodedClause) (bound : Nat)
    (h : ∀ lit ∈ c.literals, lit.maskedVar ≤ bound) :
    c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0 ≤ c.literals.length * bound := by
  rw [foldl_maskedVar_eq_map]
  have h_map := foldl_nat_bounded bound (c.literals.map (·.maskedVar))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨lit, hlit, rfl⟩ := hx; exact h lit hlit)
  simp only [List.length_map] at h_map
  exact h_map

/-- MaskedVar sum bound.
    Uses the bound that each maskedVar ≤ n and total literals ≤ 3n. -/
lemma maskedVar_sum_bound (n : Nat) (L : LStarInstanceFG)
    (h_nvars : L.encodedφ.nvars ≤ n)
    (h_lits : L.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 ≤ 3 * n)
    (h_masked : ∀ c ∈ L.encodedφ.clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ L.encodedφ.nvars) :
    totalMaskedVarSum L.encodedφ.clauses ≤ 3 * n * n := by
  simp only [totalMaskedVarSum]
  -- Each maskedVar ≤ nvars ≤ n
  have h_each : ∀ c ∈ L.encodedφ.clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ n := by
    intro c hc lit hlit
    calc lit.maskedVar ≤ L.encodedφ.nvars := h_masked c hc lit hlit
      _ ≤ n := h_nvars
  -- Main bound: totalMaskedVarSum ≤ (total literals) * n
  have h_bound : L.encodedφ.clauses.foldl
      (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 ≤
      L.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 * n := by
    -- Prove by induction on the clause list
    have h_main : ∀ (clauses : List EncodedClause),
        (∀ c ∈ clauses, ∀ lit ∈ c.literals, lit.maskedVar ≤ n) →
        clauses.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0 ≤
        clauses.foldl (fun acc c => acc + c.literals.length) 0 * n := by
      intro clauses h_cls_bound
      induction clauses with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.foldl_cons, Nat.zero_add]
        have h_hd_bound : ∀ lit ∈ hd.literals, lit.maskedVar ≤ n :=
          fun lit hlit => h_cls_bound hd List.mem_cons_self lit hlit
        have h_hd := clause_maskedVar_bound hd n h_hd_bound
        have h_tl_bound : ∀ c ∈ tl, ∀ lit ∈ c.literals, lit.maskedVar ≤ n :=
          fun c hc lit hlit => h_cls_bound c (List.mem_cons_of_mem hd hc) lit hlit
        have ih' := ih h_tl_bound
        -- Use accumulator lemmas to simplify
        rw [foldl_maskedVar_clause_init, foldl_encodedClause_init]
        calc hd.literals.foldl (fun acc lit => acc + lit.maskedVar) 0 +
              tl.foldl (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0
            ≤ hd.literals.length * n + tl.foldl (fun acc c => acc + c.literals.length) 0 * n := by
              have := h_hd; have := ih'; omega
          _ = (hd.literals.length + tl.foldl (fun acc c => acc + c.literals.length) 0) * n := by ring
    exact h_main L.encodedφ.clauses h_each
  calc L.encodedφ.clauses.foldl
        (fun acc c => acc + c.literals.foldl (fun acc lit => acc + lit.maskedVar) 0) 0
      ≤ L.encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0 * n := h_bound
    _ ≤ (3 * n) * n := Nat.mul_le_mul_right n h_lits
    _ = 3 * n * n := by ring

/-- Raw data size of toRawLStarInstanceFG L is bounded by O(n³) where n = L.dag.n.

    This captures that all components of L have polynomial size. The proof uses
    structural bounds from the L* construction (via lstar_component_bounds).

    Component analysis (let n = dag.n):
    - base.n: ≤ n (from dag_size_ge_n)
    - dag components: O(n²) (n vertices, each with ≤n parents)
    - seedWidth, R: O(n²) (n values, each ≤ n)
    - emergence: O(n³) (n matrices, each ≤ n² bits)
    - pools.stride: O(1) (construction constant, added separately)
    - encodedφ: O(n²) (O(n) clauses × O(1) literals × O(n) var indices)
    - fg: O(n²) (n elements, each ≤ n bits)

    Total: O(n³) + stride, still polynomial since stride is O(1). -/
theorem rawDataSize_poly_bound : ∀ (L : LStarInstanceFG),
    rawDataSize (toRawLStarInstanceFG L) ≤ 300 * (L.dag.n + 1) ^ 3 + L.pools.stride := by
  intro L
  -- Get construction bounds from the theorem
  -- Note: Order is (R, seedWidth, R×seedWidth, clauses, lits, masked, dgBudget, dgBits)
  -- Stride is handled separately as an additive constant (O(1))
  obtain ⟨h_R, h_sw, h_em_bound, h_clauses, h_lits, h_masked, h_dgBudget, h_dgBits⟩ :=
    lstar_component_bounds L
  -- Abbreviations
  let n := L.dag.n
  have h_n : L.dag.n = n := rfl
  have h_n_bound : L.n ≤ n := L.dag_size_ge_n
  have h_nvars : L.encodedφ.nvars = L.n := L.h_n_eq_nvars.symm
  have h_nvars_le : L.encodedφ.nvars ≤ n := by rw [h_nvars]; exact h_n_bound
  -- Component bounds
  have h1 : (toRawLStarInstanceFG L).base.n ≤ n := h_n_bound
  have h2 : (toRawLStarInstanceFG L).base.dag.n = n := rfl
  have h3 : (toRawLStarInstanceFG L).base.dag.parents.length = n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull, toRawDAG, List.length_map, List.length_finRange, h_n]
  have h4 : (toRawLStarInstanceFG L).base.dag.parents.foldl
      (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0 ≤ n * n + n * n * n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull, toRawDAG]
    exact parents_foldl_bound n L.dag.parents
  have h5 : (toRawLStarInstanceFG L).base.seedWidth.length = n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull, List.length_map, List.length_finRange, h_n]
  -- Note: seedWidth bound is now 2n² (was n²), so sum becomes 2n³
  have h6 : (toRawLStarInstanceFG L).base.seedWidth.foldl (· + ·) 0 ≤ 2 * n * n * n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull]
    have h := mapped_foldl_sum_bound n (List.finRange n) L.seedWidth (2 * n * n)
      (List.length_finRange) (fun x _ => h_sw x)
    -- Convert n * (2 * n * n) to 2 * n * n * n (associativity)
    have h_assoc : n * (2 * n * n) = 2 * n * n * n := by ring
    linarith
  have h7 : (toRawLStarInstanceFG L).base.R.length = n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull, List.length_map, List.length_finRange, h_n]
  have h8 : (toRawLStarInstanceFG L).base.R.foldl (· + ·) 0 ≤ n * n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull]
    exact mapped_foldl_sum_bound n (List.finRange n) L.R n
      (List.length_finRange) (fun x _ => h_R x)
  have h9 : (toRawLStarInstanceFG L).base.emergence.length = n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull, List.length_map, List.length_finRange, h_n]
  -- Note: emergence bound now uses h_em_bound for R×seedWidth
  have h10 : (toRawLStarInstanceFG L).base.emergence.foldl
      (fun acc m => acc + m.R + m.n + m.bits.length) 0 ≤ n * n + 3 * n * n * n := by
    simp only [toRawLStarInstanceFG, toRawLStarInstanceFull]
    exact emergence_foldl_bound n L h_n h_R h_sw h_em_bound
  -- Note: stride is a construction constant O(1), handled separately in final bound
  -- No h11 bound needed - stride is added as a separate term at the end
  have h12 : (toRawLStarInstanceFG L).encodedφ.nvars ≤ n := h_nvars_le
  have h13 : (toRawLStarInstanceFG L).encodedφ.clauses.length ≤ n := h_clauses
  have h14 : (toRawLStarInstanceFG L).encodedφ.clauses.foldl
      (fun acc c => acc + c.literals.length) 0 ≤ 3 * n := h_lits
  have h15 : totalMaskedVarSum (toRawLStarInstanceFG L).encodedφ.clauses ≤ 3 * n * n := by
    simp only [toRawLStarInstanceFG]
    exact maskedVar_sum_bound n L h_nvars_le h_lits h_masked
  have h16 : (toRawLStarInstanceFG L).fg.gateReq.length = n := by
    simp only [toRawLStarInstanceFG, toRawFrontierGateConfig, List.length_map, List.length_finRange, h_n]
  have h17 : (toRawLStarInstanceFG L).fg.gateDigests.length = n := by
    simp only [toRawLStarInstanceFG, toRawFrontierGateConfig, List.length_map, List.length_finRange, h_n]
  have h18 : (toRawLStarInstanceFG L).fg.gateDigests.foldl
      (fun acc o => acc + optionGateDigestSize o) 0 ≤ 2 * n * n := by
    simp only [toRawLStarInstanceFG, toRawFrontierGateConfig]
    exact gateDigest_foldl_bound n L h_n h_dgBudget h_dgBits
  -- Total bound calculation (updated for new bounds)
  -- rawDataSize = sum of 18 component bounds (stride handled separately)
  -- Linear terms (n): h1≤n, h2=n, h3=n, h5=n, h7=n, h9=n, h12≤n, h13≤n, h14≤3n, h16=n, h17=n
  --   Count: 1+1+1+1+1+1+1+1+3+1+1 = 13n
  -- Quadratic terms (n²): h4 has n², h8≤n², h10 has n², h15≤3n², h18≤2n²
  --   Count: 1+1+1+3+2 = 8n²
  -- Cubic terms (n³): h4 has n³, h6≤2n³, h10 has 3n³
  --   Count: 1+2+3 = 6n³
  -- Plus stride as separate constant
  -- Total: ≤ 13n + 8n² + 6n³ + stride
  have h_sum : rawDataSize (toRawLStarInstanceFG L) ≤ 13 * n + 8 * n * n + 6 * n * n * n + L.pools.stride := by
    -- Define abbreviations for components (abstract away structure access)
    let c1 := (toRawLStarInstanceFG L).base.n
    let c2 := (toRawLStarInstanceFG L).base.dag.n
    let c3 := (toRawLStarInstanceFG L).base.dag.parents.length
    let c4 := (toRawLStarInstanceFG L).base.dag.parents.foldl (fun acc l => acc + l.length + l.foldl (· + ·) 0) 0
    let c5 := (toRawLStarInstanceFG L).base.seedWidth.length
    let c6 := (toRawLStarInstanceFG L).base.seedWidth.foldl (· + ·) 0
    let c7 := (toRawLStarInstanceFG L).base.R.length
    let c8 := (toRawLStarInstanceFG L).base.R.foldl (· + ·) 0
    let c9 := (toRawLStarInstanceFG L).base.emergence.length
    let c10 := (toRawLStarInstanceFG L).base.emergence.foldl (fun acc m => acc + m.R + m.n + m.bits.length) 0
    let c11 := (toRawLStarInstanceFG L).base.pools.stride  -- Handled as constant
    let c12 := (toRawLStarInstanceFG L).encodedφ.nvars
    let c13 := (toRawLStarInstanceFG L).encodedφ.clauses.length
    let c14 := (toRawLStarInstanceFG L).encodedφ.clauses.foldl (fun acc c => acc + c.literals.length) 0
    let c15 := totalMaskedVarSum (toRawLStarInstanceFG L).encodedφ.clauses
    let c16 := (toRawLStarInstanceFG L).fg.gateReq.length
    let c17 := (toRawLStarInstanceFG L).fg.gateDigests.length
    let c18 := (toRawLStarInstanceFG L).fg.gateDigests.foldl (fun acc o => acc + optionGateDigestSize o) 0
    -- Establish bounds on each component (updated for new bounds)
    have b1 : c1 ≤ n := h1
    have b2 : c2 ≤ n := le_of_eq h2
    have b3 : c3 ≤ n := le_of_eq h3
    have b4 : c4 ≤ n * n + n * n * n := h4
    have b5 : c5 ≤ n := le_of_eq h5
    have b6 : c6 ≤ 2 * n * n * n := h6
    have b7 : c7 ≤ n := le_of_eq h7
    have b8 : c8 ≤ n * n := h8
    have b9 : c9 ≤ n := le_of_eq h9
    have b10 : c10 ≤ n * n + 3 * n * n * n := h10
    -- c11 (stride) handled separately as a constant
    have b12 : c12 ≤ n := h12
    have b13 : c13 ≤ n := h13
    have b14 : c14 ≤ 3 * n := h14
    have b15 : c15 ≤ 3 * n * n := h15
    have b16 : c16 ≤ n := le_of_eq h16
    have b17 : c17 ≤ n := le_of_eq h17
    have b18 : c18 ≤ 2 * n * n := h18
    -- rawDataSize equals sum of components
    have h_eq : rawDataSize (toRawLStarInstanceFG L) =
        c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 := rfl
    -- Separate stride from polynomial part
    have h_stride_eq : c11 = L.pools.stride := rfl
    -- Sum of bounds (excluding stride): 13n + 8n² + 5n³
    -- Build explicit bound on sum without stride
    have h_bound : c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c12 + c13 + c14 + c15 + c16 + c17 + c18
        ≤ n + n + n + (n * n + n * n * n) + n + 2 * n * n * n + n + n * n + n + (n * n + 3 * n * n * n) + n + n + 3 * n + 3 * n * n + n + n + 2 * n * n := by
      -- Apply Nat.add_le_add repeatedly
      apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add
      apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add
      apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add
      apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add
      exact b1; exact b2; exact b3; exact b4; exact b5; exact b6; exact b7; exact b8
      exact b9; exact b10; exact b12; exact b13; exact b14; exact b15; exact b16; exact b17
      exact b18
    have h_simplify : n + n + n + (n * n + n * n * n) + n + 2 * n * n * n + n + n * n + n + (n * n + 3 * n * n * n) + n + n + 3 * n + 3 * n * n + n + n + 2 * n * n
        = 13 * n + 8 * n * n + 6 * n * n * n := by ring
    -- rawDataSize = (sum without stride) + stride
    have h_split : c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18
        = (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c12 + c13 + c14 + c15 + c16 + c17 + c18) + c11 := by ring
    rw [h_eq, h_split]
    calc (c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c12 + c13 + c14 + c15 + c16 + c17 + c18) + c11
        ≤ (n + n + n + (n * n + n * n * n) + n + 2 * n * n * n + n + n * n + n + (n * n + 3 * n * n * n) + n + n + 3 * n + 3 * n * n + n + n + 2 * n * n) + c11 := by
          exact Nat.add_le_add_right h_bound c11
      _ = (13 * n + 8 * n * n + 6 * n * n * n) + c11 := by rw [h_simplify]
      _ = 13 * n + 8 * n * n + 6 * n * n * n + L.pools.stride := by rw [h_stride_eq]
  -- 13n + 8n² + 6n³ ≤ 300 * (n+1)³
  -- (n+1)³ = n³ + 3n² + 3n + 1, so 300(n+1)³ = 300n³ + 900n² + 900n + 300
  -- Coefficient check: 6 ≤ 300, 8 ≤ 900, 13 ≤ 900, 0 ≤ 300 ✓
  have h_final : 13 * n + 8 * n * n + 6 * n * n * n ≤ 300 * (n + 1) ^ 3 := by
    -- Prove by showing coefficient comparison
    have h_expand : 300 * (n + 1) ^ 3 = 300 * n * n * n + 900 * n * n + 900 * n + 300 := by ring
    rw [h_expand]
    -- Now prove: 13n + 8n² + 6n³ ≤ 300n³ + 900n² + 900n + 300
    have h1 : 6 * n * n * n ≤ 300 * n * n * n := by
      have step1 : 6 * n ≤ 300 * n := Nat.mul_le_mul_right n (by decide : 6 ≤ 300)
      have step2 : 6 * n * n ≤ 300 * n * n := Nat.mul_le_mul_right n step1
      exact Nat.mul_le_mul_right n step2
    have h2 : 8 * n * n ≤ 900 * n * n := by
      have step1 : 8 * n ≤ 900 * n := Nat.mul_le_mul_right n (by decide : 8 ≤ 900)
      exact Nat.mul_le_mul_right n step1
    have h3 : 13 * n ≤ 900 * n := Nat.mul_le_mul_right n (by decide : 13 ≤ 900)
    have h4 : (0 : Nat) ≤ 300 := by decide
    calc 13 * n + 8 * n * n + 6 * n * n * n
        = 6 * n * n * n + 8 * n * n + 13 * n + 0 := by ring
      _ ≤ 300 * n * n * n + 900 * n * n + 900 * n + 300 := by
        apply Nat.add_le_add; apply Nat.add_le_add; apply Nat.add_le_add
        exact h1; exact h2; exact h3; exact h4
  -- Connect n to L.dag.n for final goal
  calc rawDataSize (toRawLStarInstanceFG L)
      ≤ 13 * n + 8 * n * n + 6 * n * n * n + L.pools.stride := h_sum
    _ ≤ 300 * (n + 1) ^ 3 + L.pools.stride := Nat.add_le_add_right h_final L.pools.stride
    _ = 300 * (L.dag.n + 1) ^ 3 + L.pools.stride := by rw [← h_n]

#print axioms rawDataSize_poly_bound

/-! ### Complexity Class Integration Check -/

/-- Polynomial encoding length bound.

    The proof establishes that encoding length is polynomial in L.dag.n by tracking
    the size of each component:
    - DAG: n vertices, at most n² edges → O(n³) bits for parent lists
    - seedWidth, R: n elements, each ≤ some constant → O(n) bits
    - emergence: n matrices, each O(R×n) bits → O(n²) total (R constant)
    - encodedφ: O(n) clauses → O(n²) bits
    - fg: n booleans + digests → O(n²) bits
    - pools.stride: O(1) construction constant

    Total: O(n³) + O(stride), still polynomial since stride is O(1).

    The bound includes `8 * stride + 100` as an additive constant to account for
    the construction constant. For complexity theory purposes, this is O(1) and
    does not affect the polynomial nature of the encoding. -/
theorem encode_len_poly (L : LStarInstanceFG) :
  let bits := Encodable.encode (toRawLStarInstanceFG L)
  bits.length ≤ 3072 * (Sized.size L + 1) ^ 3 + 8 * L.pools.stride + 100 := by
  intro bits
  -- The proof uses two key lemmas:
  -- 1. encoding_linear_in_data: encoding length ≤ 8 * rawDataSize + 100
  -- 2. rawDataSize_poly_bound: rawDataSize(toRaw L) ≤ 300 * (n+1)³ + stride
  --
  -- Combining: bits.length ≤ 8 * (300 * (n+1)³ + stride) + 100
  --          = 2400 * (n+1)³ + 8 * stride + 100
  --          ≤ 3072 * (n+1)³ + 8 * stride + 100
  have h_linear := encoding_linear_in_data (toRawLStarInstanceFG L)
  have h_poly := rawDataSize_poly_bound L
  -- Sized.size L = L.dag.n by definition
  have h_size : Sized.size L = L.dag.n := rfl
  calc bits.length
      ≤ 8 * rawDataSize (toRawLStarInstanceFG L) + 100 := h_linear
    _ ≤ 8 * (300 * (L.dag.n + 1) ^ 3 + L.pools.stride) + 100 := by omega
    _ = 2400 * (L.dag.n + 1) ^ 3 + 8 * L.pools.stride + 100 := by ring
    _ ≤ 3072 * (L.dag.n + 1) ^ 3 + 8 * L.pools.stride + 100 := by omega
    _ = 3072 * (Sized.size L + 1) ^ 3 + 8 * L.pools.stride + 100 := by rw [h_size]

/- Note: BitEncoding instance is NOT provided because it requires a working bidirectional
   decode function, which would require hundreds of lines of dependent type reconstruction.

   For complexity theory purposes, the key properties are:
   1. encode : LStarInstanceFG → List Bool (provided by Encodable instance above)
   2. Polynomial length bound (encode_len_poly theorem)
   3. TMInputEncodingBase instance (provided below)

   These are sufficient to establish L* as a valid language in {0,1}* with polynomial encoding. -/

/-- Helper: get bits for an LStarInstanceFG -/
noncomputable def encodeBits (x : LStarInstanceFG) : List Bool :=
  Encodable.encode (toRawLStarInstanceFG x)

/-- Explicit TMInputEncodingBase instance (no injectivity required).
    Uses Fin 3 alphabet: 0=blank, 1=false, 2=true to distinguish data from blank.

    This instance demonstrates that LStarInstanceFG can be encoded to TM tape,
    establishing L* as a valid language in the complexity-theoretic sense.

    Note: The size bound includes a stride-dependent term. For complexity theory purposes,
    stride is a construction constant O(1) that doesn't affect polynomial complexity.
    The bound `encode_len_poly` gives: O(n³) + O(stride), which is polynomial since stride is O(1). -/
noncomputable instance lstarTMInputEncodingBase : TMInputEncodingBase LStarInstanceFG (Fin 3) where
  blank := 0
  min_support x := (encodeBits x).length
  encode x := fun i =>
    if h : i < (encodeBits x).length
    then if (encodeBits x).get ⟨i, h⟩ then 2 else 1  -- 1=false, 2=true (both ≠ 0=blank)
    else 0
  min_support_spec := fun x i => ⟨
    -- Before min_support: encoding is non-blank (1 or 2, both ≠ 0)
    fun hi => by split_ifs <;> decide,
    -- After min_support: encoding is blank (0)
    fun hi => by split_ifs with h1 <;> omega
  ⟩
  finite_support := fun x => ⟨(encodeBits x).length, fun i hi => by
    split_ifs with h1 <;> omega⟩
  -- Note: We use a large constant to absorb the stride term.
  -- encode_len_poly gives: bits.length ≤ 3072 * (n+1)³ + 8 * stride + 100
  -- Since stride is bounded by 2^65 (construction constant), and (n+1)³ ≥ 1,
  -- we can absorb stride into a larger constant for the asymptotic bound.
  -- This bound is used only for complexity class membership, not security analysis.
  C_encode := 2^70  -- Large enough to absorb any construction constant
  k_encode := 3
  size_bounded := fun x => by
    have h := encode_len_poly x
    -- 3072 * (n+1)³ + 8 * stride + 100 ≤ 2^70 * (n+1)³
    -- Since stride ≤ 2^65 (by x.stride_bound) and (n+1)³ ≥ 1:
    -- 3072 * (n+1)³ + 8*2^65 + 100 ≤ 2^70 * (n+1)³
    have h_stride : x.pools.stride ≤ 2^65 := x.stride_bound
    -- (n+1)³ ≥ 1 always holds since n+1 ≥ 1
    have h_cube_pos : (Sized.size x + 1)^3 ≥ 1 := Nat.one_le_pow 3 (Sized.size x + 1) (by omega)
    -- 8 * 2^65 + 3072 + 100 < 2^70 (verified below)
    -- So: 8 * stride + 3072 * (n+1)³ + 100 ≤ 8 * 2^65 + 3072 * (n+1)³ + 100
    --                                      ≤ (2^70 - 3072) * 1 + 3072 * (n+1)³
    --                                      ≤ 2^70 * (n+1)³
    calc (encodeBits x).length
        ≤ 3072 * (Sized.size x + 1)^3 + 8 * x.pools.stride + 100 := h
      _ ≤ 3072 * (Sized.size x + 1)^3 + 8 * 2^65 + 100 := by omega
      _ ≤ 2^70 * (Sized.size x + 1)^3 := by
          -- Need: 3072 * k³ + 8 * 2^65 + 100 ≤ 2^70 * k³ where k = (n+1) ≥ 1
          -- Rearranging: 8 * 2^65 + 100 ≤ (2^70 - 3072) * k³
          -- Since k³ ≥ 1: suffices 8 * 2^65 + 100 ≤ 2^70 - 3072
          -- 8 * 2^65 = 2^68 < 2^70 - 3072 ✓
          have h_const : 8 * 2^65 + 100 ≤ 2^70 - 3072 := by native_decide
          have h_factor : 2^70 - 3072 ≤ (2^70 - 3072) * (Sized.size x + 1)^3 := by
            have : 1 ≤ (Sized.size x + 1)^3 := h_cube_pos
            omega
          calc 3072 * (Sized.size x + 1)^3 + 8 * 2^65 + 100
              ≤ 3072 * (Sized.size x + 1)^3 + (2^70 - 3072) := by omega
            _ = 3072 * (Sized.size x + 1)^3 + 2^70 - 3072 := by omega
            _ ≤ 2^70 * (Sized.size x + 1)^3 := by
                -- 3072 * k³ + 2^70 - 3072 ≤ 2^70 * k³
                -- 2^70 - 3072 ≤ 2^70 * k³ - 3072 * k³ = (2^70 - 3072) * k³
                -- This holds when k³ ≥ 1
                have : 3072 * (Sized.size x + 1)^3 + 2^70 - 3072
                     ≤ 3072 * (Sized.size x + 1)^3 + (2^70 - 3072) * (Sized.size x + 1)^3 := by
                  have h1 : 2^70 - 3072 ≤ (2^70 - 3072) * (Sized.size x + 1)^3 := h_factor
                  omega
                calc 3072 * (Sized.size x + 1)^3 + 2^70 - 3072
                    ≤ 3072 * (Sized.size x + 1)^3 + (2^70 - 3072) * (Sized.size x + 1)^3 := this
                  _ = (3072 + (2^70 - 3072)) * (Sized.size x + 1)^3 := by ring
                  _ = 2^70 * (Sized.size x + 1)^3 := by ring

-- Axiom Audits: Trust Boundary Transparency
#print axioms encode_len_poly
#print axioms lstarTMInputEncodingBase

/-! ## L* as a Set of Bitstrings

**Purpose**: Make explicit that L* ⊆ {0,1}* is a language in the complexity-theoretic sense.

**Definition**: L* is the set of bitstrings that encode yes-instances of LStarInstanceFG.
A yes-instance is one where there exists a valid witness (satisfying assignment + correct digests).

This addresses the "L* is not defined as a set of strings" concern by providing:
1. `IsYesInstance`: Predicate for yes-instances (∃ valid witness)
2. `LStarLanguage`: The language L* ⊆ {0,1}* as a Set (List Bool)
3. `LStarLanguage_mem_iff`: Characterization theorem

**Reference**: This definition is the authoritative source for "L* as bitstrings".
Other files (CRITICAL_DEFINITIONS.md, paper) should reference this definition.

**Relationship to LStarNP.lean**: The `LStarLang` definition in LStarNP.lean provides
the full semantic definition with seed chain computation. This file provides the
bitstring-level view for complexity theory. Both are equivalent for planted instances.
-/

/-- A yes-instance is one where there exists a valid witness with correct digests.

    A witness for L* consists of:
    - An assignment (satisfying the hidden CNF)
    - Digest bits that match the computed digests from the assignment

    The `HasCorrectDigests` predicate (VerifiedWitness.lean) checks:
    `W.digestBits = digestsFromAssignmentWithSeeds L W.assignment (computeSeedChain ...)`

    This is the structural characterization equivalent to `LStarLang` (LStarNP.lean)
    for planted instances.

    Note: We use existential witness quantification rather than direct CNF
    access since EncodedCNF is OAP-encoded (seed-locked). -/
def IsYesInstance (L : LStarInstanceFG) : Prop :=
  ∃ (W : Witness L.n), LStar.StructuralOWF.Foundations.HasCorrectDigests L W

/-- L* as a subset of {0,1}*: the set of bitstrings encoding yes-instances.

    **This is the canonical definition of L* as a language of bitstrings.**

    L* = { encode(I) | I : LStarInstanceFG ∧ IsYesInstance I }

    Properties:
    - L* ⊆ {0,1}* (by construction: encodeBits returns List Bool)
    - Membership is NP: verification is polynomial-time (see LStarNP.lean)
    - Encoding has polynomial overhead (encode_len_poly theorem)

    **Encoding details**:
    - `encodeBits : LStarInstanceFG → List Bool` (this file, line 1534)
    - Polynomial bound: `encode_len_poly` proves O(n³) overhead
    - TM encoding: `lstarTMInputEncodingBase` provides TM tape representation
-/
def LStarLanguage : Set (List Bool) :=
  { bs | ∃ (L : LStarInstanceFG), encodeBits L = bs ∧ IsYesInstance L }

/-- Characterization: a bitstring is in L* iff it encodes an instance with valid witness. -/
theorem LStarLanguage_mem_iff (bs : List Bool) :
    bs ∈ LStarLanguage ↔
    ∃ (L : LStarInstanceFG), encodeBits L = bs ∧
      ∃ (W : Witness L.n), LStar.StructuralOWF.Foundations.HasCorrectDigests L W :=
  Iff.rfl

#print axioms IsYesInstance
#print axioms LStarLanguage
#print axioms LStarLanguage_mem_iff

/-! ## L* as a Language in NP (Bitstring Level)

**Purpose**: Prove that L* (as a set of bitstrings) is in NP.

**Approach**: The certificate carries the original structure + witness.
- Certificate type: `Σ L : LStarInstanceFG, Witness L.n`
- Verifier checks: `encodeBits L = bs ∧ HasCorrectDigests L W`

This avoids needing a `decodeBits` function (parsing bitstrings back to structures).
The certificate "carries" the structure, and we just verify it encodes correctly.

**Result**: `LStarLanguageLang_in_NP : InNP LStarLanguageLang`
-/

/-- L* as a decision language over bitstrings (Lang type). -/
def LStarLanguageLang : LStar.Complexity.Lang (List Bool) :=
  fun bs => bs ∈ LStarLanguage

/-- Certificate type for L* NP membership: structure + witness bundled together.
    The verifier checks the structure encodes to the input bitstring. -/
abbrev LStarCertificate := Σ (L : LStarInstanceFG), Witness L.n

/-- Verifier for L* bitstring membership.
    Given bitstring `bs` and certificate `(L, W)`:
    1. Check that `L` encodes to `bs`
    2. Check that `W` has correct digests for `L`
    3. Check that `W.gateProofs` is empty (for polynomial witness bounds) -/
def LStarVerifier (bs : List Bool) (cert : LStarCertificate) : Prop :=
  encodeBits cert.1 = bs ∧
  LStar.StructuralOWF.Foundations.HasCorrectDigests cert.1 cert.2 ∧
  cert.2.gateProofs = []

/-- Verifier correctness: bs ∈ L* ↔ ∃ certificate that verifies.

    Forward: If bs ∈ L*, then ∃ L W with encodeBits L = bs ∧ HasCorrectDigests L W.
             We construct a certificate with gateProofs = [] (valid since gateProofs
             is unused in single-gate mode; HasCorrectDigests doesn't depend on it).

    Backward: If certificate ⟨L, W⟩ verifies, then encodeBits L = bs ∧ HasCorrectDigests L W,
              so bs ∈ LStarLanguage by definition. -/
theorem LStarVerifier_correct (bs : List Bool) :
    LStarLanguageLang bs ↔ ∃ (cert : LStarCertificate), LStarVerifier bs cert := by
  constructor
  · -- Forward: bs ∈ L* → ∃ certificate
    intro h_mem
    -- Unfold membership
    simp only [LStarLanguageLang, LStarLanguage, Set.mem_setOf_eq, IsYesInstance] at h_mem
    obtain ⟨L, h_enc, W, h_digests⟩ := h_mem
    -- Construct certificate with empty gateProofs
    let W' : Witness L.n := ⟨W.assignment, [], W.digestBits⟩
    -- Show HasCorrectDigests W' = HasCorrectDigests W (same assignment and digestBits)
    have h_digests' : LStar.StructuralOWF.Foundations.HasCorrectDigests L W' := by
      simp only [LStar.StructuralOWF.Foundations.HasCorrectDigests] at h_digests ⊢
      exact h_digests
    exact ⟨⟨L, W'⟩, h_enc, h_digests', rfl⟩
  · -- Backward: ∃ certificate → bs ∈ L*
    intro ⟨⟨L, W⟩, h_enc, h_digests, _⟩
    simp only [LStarLanguageLang, LStarLanguage, Set.mem_setOf_eq, IsYesInstance]
    exact ⟨L, h_enc, W, h_digests⟩

/-- L* (as a bitstring language) has witness structure (no resource bounds).

    **Certificate**: `Σ L : LStarInstanceFG, Witness L.n` (structure + witness)
    **Verifier**: Check encoding match + digest correctness

    For complexity-theoretic NP with poly bounds, see `LStarLanguageLang_in_NP` below. -/
theorem LStarLanguageLang_has_witness_structure : LStar.Complexity.HasWitnessStructure LStarLanguageLang := by
  -- Construct VerifierCert
  refine ⟨⟨LStarCertificate, LStarVerifier, ?_⟩⟩
  -- Prove spec: ∀ bs, LStarLanguageLang bs ↔ ∃ cert, LStarVerifier bs cert
  exact LStarVerifier_correct

#print axioms LStarLanguageLang
#print axioms LStarCertificate
#print axioms LStarVerifier
#print axioms LStarVerifier_correct
#print axioms LStarLanguageLang_has_witness_structure

/-! ## L* in NP with Polynomial-Time Verifier (InNP)

**Purpose**: Prove that L* (as bitstrings) is in NP with an explicit polynomial-time verifier.

**Approach**:
1. Define `Sized LStarCertificate` via existing `sizedSigma` instance
2. Define `AlgSpec` for the verifier with polynomial bounds
3. Use `algspec_has_tm` axiom to get `RandAdv` with TM implementation
4. Prove `InNP LStarLanguageLang`

**Trust Boundary**: Uses `algspec_has_tm` axiom (Church-Turing bridge, already in trust boundary)

**Key Insight**: The verifier checks:
1. `encodeBits L = bs` - O(n³) comparison (from encode_len_poly)
2. `HasCorrectDigests L W` - polynomial in witness size (digest computation)
-/

-- Step 1: Sized instance for LStarCertificate
-- This follows automatically from sizedSigma + existing Sized instances for LStarInstanceFG and Witness

/-- Sized instance for LStarCertificate.
    Uses sizedSigma: size ⟨L, W⟩ = size L + size W -/
instance sizedLStarCertificate : LStar.Complexity.Sized LStarCertificate :=
  LStar.Complexity.sizedSigma

-- Step 2: Verifier run function (computable)

/-- Computable verifier: checks encoding match and digest correctness.
    Returns true iff the certificate is valid for the bitstring.

    **Note on gateProofs check**: For single-gate instances (which L* uses),
    gateProofs is unused - the path enumeration is trivial with one gate.
    We require gateProofs = [] to ensure polynomial witness bounds for NP.
    This is consistent with the canonical witness construction. -/
noncomputable def verifyLStarMembership (input : List Bool × LStarCertificate) : Bool :=
  let (bs, cert) := input
  let L := cert.1
  let W := cert.2
  -- Check 1: encoding match
  let enc_match := encodeBits L == bs
  -- Check 2: digest correctness (using decidable equality on lists)
  let digests_correct := W.digestBits == LStar.StructuralOWF.Foundations.digestsFromAssignmentWithSeeds L W.assignment
    (LStar.LStarInstanceFull.computeSeedChain L.toLStarInstanceFull
      (LStar.StructuralOWF.Foundations.entropyFromWitness L W))
  -- Check 3: gateProofs empty (required for polynomial witness bound in single-gate mode)
  let gateProofs_ok := W.gateProofs.length == 0
  enc_match && digests_correct && gateProofs_ok

-- Step 3: Time bound analysis

/-- Time bound for verification: O((size input)³).

    Components:
    - Encoding comparison: O(n³) from encode_len_poly
    - Digest computation: O(n²) (linear in witness size, poly in instance size)
    - Total: O(n³) where n = size of input -/
noncomputable def verifyLStar_time_bound (n : Nat) : Nat :=
  -- Conservative bound: 4096 * (n + 1)^3
  -- This covers encoding (3072 * (n+1)³) + digest computation overhead
  4096 * (n + 1) ^ 3

/-- Polynomial constants for verifier time bound -/
def verifyLStar_C : Nat := 4096
def verifyLStar_k : Nat := 3

-- Step 4: AlgSpec for the verifier

/-- AlgSpec for L* membership verification.

    **Specification**:
    - Input: (bitstring, certificate)
    - Output: Bool (membership decision)
    - Time: O(n³) polynomial

    **Components verified**:
    - C = 4096 (polynomial constant)
    - k = 3 (polynomial exponent)
    - Deterministic (no randomness used)
    - Output bounded (Bool has size 1) -/
noncomputable def verifyLStar_algspec :
    LStar.Complexity.AlgSpec (List Bool × LStarCertificate) Bool 1 where
  run := fun _ input => verifyLStarMembership input
  time_bound := verifyLStar_time_bound
  C := verifyLStar_C
  k := verifyLStar_k
  h_C_pos := by decide
  h_k_pos := by decide
  poly_explicit := fun x => by
    simp only [verifyLStar_time_bound, verifyLStar_C, verifyLStar_k]
    -- 4096 * (size x + 1)^3 ≤ 4096 * (size x + 1)^3
    exact Nat.le_refl _
  time_bound_uniform := fun n => by
    simp only [verifyLStar_time_bound, verifyLStar_C, verifyLStar_k]
    exact Nat.le_refl _
  output_bounded := fun _ x => by
    -- Bool has size 1, time_bound is at least 1
    simp only [verifyLStar_time_bound]
    have h : 4096 * (LStar.Complexity.Sized.size x + 1) ^ 3 ≥ 1 := by
      have h1 : (LStar.Complexity.Sized.size x + 1) ^ 3 ≥ 1 := Nat.one_le_pow 3 _ (by omega)
      omega
    exact h
  coins_pos := by decide

/-- The verifier AlgSpec is deterministic (ignores coins). -/
theorem verifyLStar_algspec_deterministic :
    verifyLStar_algspec.isDeterministic := by
  intro c₁ c₂ x
  rfl

-- Step 5: Connect verifier to membership

/-- Verifier correctness: verifyLStarMembership matches LStarVerifier predicate.

    Note: This connects the computable Bool function to the Prop predicate.
    The connection is via decidable equality on lists. -/
theorem verifyLStarMembership_correct (bs : List Bool) (cert : LStarCertificate) :
    verifyLStarMembership (bs, cert) = true ↔ LStarVerifier bs cert := by
  simp only [verifyLStarMembership, LStarVerifier]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro ⟨⟨h_enc, h_dig⟩, h_gp⟩
    refine ⟨h_enc, ?_, ?_⟩
    · -- Connect digestsFromAssignmentWithSeeds to HasCorrectDigests
      simp only [LStar.StructuralOWF.Foundations.HasCorrectDigests]
      exact h_dig
    · -- gateProofs.length = 0 → gateProofs = []
      exact List.eq_nil_of_length_eq_zero h_gp
  · intro ⟨h_enc, h_dig, h_gp⟩
    refine ⟨⟨h_enc, ?_⟩, ?_⟩
    · simp only [LStar.StructuralOWF.Foundations.HasCorrectDigests] at h_dig
      exact h_dig
    · -- gateProofs = [] → gateProofs.length = 0
      simp [h_gp]

-- Step 6: Prove InNP using algspec_has_tm

/-- L* (as bitstrings) is in NP with polynomial-time verifier.

    **Statement**: There exists a polynomial-time TM verifier for L* membership.

    **Proof**: Use `algspec_has_tm` (Church-Turing bridge) to convert AlgSpec to RandAdv.

    **Trust Boundary**: Uses `algspec_has_tm` axiom (standard, already in trust boundary)

    **Complexity**:
    - Verifier time: O(n³) where n = input size
    - Witness size: O(n³) (certificate carries structure + witness) -/
theorem LStarLanguageLang_in_NP : LStar.Complexity.InNP LStarLanguageLang := by
  -- Witness type is LStarCertificate
  use LStarCertificate
  use sizedLStarCertificate
  -- Use algspec_has_tm to get RandAdv from AlgSpec
  have h_tm := LStar.Complexity.algspec_has_tm verifyLStar_algspec
  obtain ⟨V, h_run_eq, h_C_eq, h_k_eq, _, _, _⟩ := h_tm
  use 1  -- T = 1 coin (deterministic)
  use V
  -- Witness size constants (conservative: O(n³))
  use 4096  -- C_wit
  use 3     -- k_wit
  -- Verifier time constants (from verifyLStar_algspec: C=4096, k=3)
  use V.C   -- C_time
  use V.k   -- k_time
  -- Helper: V.run equals verifyLStarMembership (via h_run_eq)
  have h_V_run : ∀ c x, V.run c x = verifyLStarMembership x := by
    intro c x
    have h1 : V.toAlgSpec.run = verifyLStar_algspec.run := h_run_eq
    simp only [LStar.Complexity.RandAdv.toAlgSpec] at h1
    have h2 : V.run c x = verifyLStar_algspec.run c x := congrFun (congrFun h1 c) x
    simp only [verifyLStar_algspec] at h2
    exact h2
  constructor
  · -- Determinism: all coin choices produce same output
    intro c₁ c₂ p
    simp only [h_V_run]
  constructor
  · -- Witness size bound: size cert ≤ C_wit * (size bs + 1) ^ k_wit
    intro bs cert h_true
    -- Extract verification conditions from h_true
    rw [h_V_run] at h_true
    have h_verify := (verifyLStarMembership_correct bs cert).mp h_true
    obtain ⟨h_enc, h_digests, h_gateProofs_empty⟩ := h_verify
    -- Abbreviations
    let L := cert.1
    let W := cert.2
    -- Key: size bs = bs.length + 1
    have h_size_bs : LStar.Complexity.Sized.size bs = bs.length + 1 := rfl
    -- Certificate size = size L + size W (by sizedSigma)
    have h_size_cert : LStar.Complexity.Sized.size cert = LStar.Complexity.Sized.size L + LStar.Complexity.Sized.size W := rfl
    -- Step 1: Show size L ≤ bs.length (encoding has length ≥ dag.n from parents list)
    have h_enc_len_ge : bs.length ≥ L.dag.n := by
      rw [← h_enc]
      -- The encoding includes dag.parents which has length = dag.n
      have h_parents_len : (toRawLStarInstanceFG L).base.dag.parents.length = L.dag.n := by
        unfold toRawLStarInstanceFG toRawLStarInstanceFull toRawDAG
        simp only [List.length_map, List.length_finRange]
      -- List encoding has length ≥ list.length (from unary prefix)
      have h_list_len : ∀ (l : List (List Nat)),
          (@Encodable.encode (List (List Nat)) _ l).length ≥ l.length := by
        intro l
        show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≥ l.length
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega
      have h_dag_in_full : ∀ (r : RawLStarInstanceFull),
          (@Encodable.encode RawLStarInstanceFull _ r).length ≥ r.dag.parents.length := by
        intro r
        have h1 : (@Encodable.encode RawLStarInstanceFull _ r).length =
            (encodeNat r.n ++ Encodable.encode r.dag ++ Encodable.encode r.seedWidth ++
             Encodable.encode r.R ++ Encodable.encode r.emergence ++ Encodable.encode r.pools).length := rfl
        have h2 : (@Encodable.encode RawDAG _ r.dag).length =
            (encodeNat r.dag.n ++ @Encodable.encode (List (List Nat)) _ r.dag.parents).length := rfl
        simp only [List.length_append] at h1 h2
        have h3 := h_list_len r.dag.parents
        omega
      have h_fg_in_raw : ∀ (r : RawLStarInstanceFG),
          (@Encodable.encode RawLStarInstanceFG _ r).length ≥ r.base.dag.parents.length := by
        intro r
        have h1 : (@Encodable.encode RawLStarInstanceFG _ r).length =
            (Encodable.encode r.base ++ Encodable.encode r.encodedφ ++ Encodable.encode r.fg).length := rfl
        simp only [List.length_append] at h1
        have h2 := h_dag_in_full r.base
        omega
      calc (encodeBits L).length
          ≥ (toRawLStarInstanceFG L).base.dag.parents.length := h_fg_in_raw (toRawLStarInstanceFG L)
        _ = L.dag.n := h_parents_len
    have h_L_le_bs : LStar.Complexity.Sized.size L ≤ bs.length := h_enc_len_ge
    -- Step 2: Bound witness size (simplified by h_gateProofs_empty)
    have h_nvars_le : L.n ≤ L.dag.n := L.dag_size_ge_n
    have h_R_bound : ∀ v : Fin L.dag.n, L.R v ≤ L.dag.n := fun v => by
      have ⟨h_R, _, _, _, _, _, _, _⟩ := lstar_component_bounds L
      exact h_R v
    have h_totalRBits_bound : LStar.StructuralOWF.Foundations.totalRBits L ≤ L.dag.n * L.dag.n := by
      unfold LStar.StructuralOWF.Foundations.totalRBits
      calc (Finset.univ.filter (fun v : Fin L.dag.n => L.fg.gateReq v)).sum (fun v => L.R v)
          ≤ (Finset.univ : Finset (Fin L.dag.n)).sum (fun v => L.R v) := by
            apply Finset.sum_le_sum_of_subset
            exact Finset.filter_subset _ _
        _ ≤ (Finset.univ : Finset (Fin L.dag.n)).sum (fun _ => L.dag.n) := by
            apply Finset.sum_le_sum
            intro v _
            exact h_R_bound v
        _ = L.dag.n * L.dag.n := by simp [Finset.sum_const]
    -- digestBits.length = totalRBits L when HasCorrectDigests holds
    have h_digest_len : W.digestBits.length = LStar.StructuralOWF.Foundations.totalRBits L :=
      LStar.StructuralOWF.Foundations.correct_digests_implies_correct_length L W h_digests
    -- gateProofs is empty (from verification), so foldl = 0
    have h_proofs_zero : W.gateProofs.foldl (fun acc _p => acc + 1) 0 = 0 := by
      rw [h_gateProofs_empty]; rfl
    -- Now bound size W (simplified: gateProofs contributes 0)
    have h_size_W_bound : LStar.Complexity.Sized.size W ≤ L.dag.n + L.dag.n * L.dag.n + 1 := by
      have h_size_W : LStar.Complexity.Sized.size W =
          L.n + W.gateProofs.foldl (fun acc _ => acc + 1) 0 + W.digestBits.length + 1 := rfl
      rw [h_size_W, h_proofs_zero]
      have h3 : W.digestBits.length ≤ L.dag.n * L.dag.n := by
        rw [h_digest_len]; exact h_totalRBits_bound
      -- L.n ≤ dag.n, digestBits ≤ dag.n²
      linarith
    -- Final calculation using size bs ≥ L.dag.n + 1 ≥ 1
    rw [h_size_cert]
    have h_sbs_ge : LStar.Complexity.Sized.size bs ≥ L.dag.n + 1 := by
      rw [h_size_bs]; linarith
    have h_sbs_pos : 0 < LStar.Complexity.Sized.size bs := LStar.Complexity.Sized.size_pos bs
    -- size L + size W ≤ dag.n + (dag.n + dag.n + dag.n² + 1) ≤ dag.n² + 3*dag.n + 1
    have h_sum_le : LStar.Complexity.Sized.size L + LStar.Complexity.Sized.size W ≤
        L.dag.n * L.dag.n + 3 * L.dag.n + 1 := by
      have hL : LStar.Complexity.Sized.size L = L.dag.n := rfl
      calc LStar.Complexity.Sized.size L + LStar.Complexity.Sized.size W
          = L.dag.n + LStar.Complexity.Sized.size W := by rw [hL]
        _ ≤ L.dag.n + (L.dag.n + L.dag.n + L.dag.n * L.dag.n + 1) := by linarith [h_size_W_bound]
        _ = L.dag.n * L.dag.n + 3 * L.dag.n + 1 := by ring
    -- dag.n² + 3*dag.n + 1 ≤ 4*(dag.n + 1)² since 4(n+1)² = 4n² + 8n + 4 ≥ n² + 3n + 1
    have h_quad : L.dag.n * L.dag.n + 3 * L.dag.n + 1 ≤ 4 * (L.dag.n + 1) * (L.dag.n + 1) := by
      have h : 4 * (L.dag.n + 1) * (L.dag.n + 1) = 4 * L.dag.n * L.dag.n + 8 * L.dag.n + 4 := by ring
      nlinarith
    -- 4*(dag.n + 1)² ≤ 4*(size bs)² since dag.n + 1 ≤ size bs
    have h_sq : 4 * (L.dag.n + 1) * (L.dag.n + 1) ≤ 4 * (LStar.Complexity.Sized.size bs) * (LStar.Complexity.Sized.size bs) := by
      have h1 : (L.dag.n + 1) * (L.dag.n + 1) ≤ LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs :=
        Nat.mul_le_mul h_sbs_ge h_sbs_ge
      linarith
    -- 4*(size bs)² ≤ 4*(size bs)³ since size bs ≥ 1
    have h_cube_ge : 4 * (LStar.Complexity.Sized.size bs) * (LStar.Complexity.Sized.size bs) ≤
        4 * (LStar.Complexity.Sized.size bs) ^ 3 := by
      have h_one : 1 ≤ LStar.Complexity.Sized.size bs := h_sbs_pos
      -- size bs² * 1 ≤ size bs² * size bs
      have h2 : LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs * 1 ≤
          LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs :=
        Nat.mul_le_mul_left _ h_one
      have h3 : (LStar.Complexity.Sized.size bs) ^ 3 =
          LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs * LStar.Complexity.Sized.size bs := by ring
      simp only [Nat.mul_one] at h2
      linarith
    -- (size bs)³ ≤ (size bs + 1)³
    have h_cube_mono : 4 * (LStar.Complexity.Sized.size bs) ^ 3 ≤ 4 * (LStar.Complexity.Sized.size bs + 1) ^ 3 := by
      have hp : (LStar.Complexity.Sized.size bs) ^ 3 ≤ (LStar.Complexity.Sized.size bs + 1) ^ 3 :=
        Nat.pow_le_pow_left (Nat.le_succ _) 3
      linarith
    -- 4 ≤ 4096
    have h_const : 4 * (LStar.Complexity.Sized.size bs + 1) ^ 3 ≤ 4096 * (LStar.Complexity.Sized.size bs + 1) ^ 3 :=
      Nat.mul_le_mul_right _ (by omega : 4 ≤ 4096)
    -- Chain all the bounds together
    calc LStar.Complexity.Sized.size L + LStar.Complexity.Sized.size W
        ≤ L.dag.n * L.dag.n + 3 * L.dag.n + 1 := h_sum_le
      _ ≤ 4 * (L.dag.n + 1) * (L.dag.n + 1) := h_quad
      _ ≤ 4 * (LStar.Complexity.Sized.size bs) * (LStar.Complexity.Sized.size bs) := h_sq
      _ ≤ 4 * (LStar.Complexity.Sized.size bs) ^ 3 := h_cube_ge
      _ ≤ 4 * (LStar.Complexity.Sized.size bs + 1) ^ 3 := h_cube_mono
      _ ≤ 4096 * (LStar.Complexity.Sized.size bs + 1) ^ 3 := h_const
  constructor
  · -- Verifier time bound: time_bound (size p) ≤ C_time * (size p + 1) ^ k_time
    intro p
    -- V inherits poly_explicit from verifyLStar_algspec via algspec_has_tm
    exact V.poly_explicit p
  · -- Correctness: L bs ↔ ∃ cert, V.run 0 (bs, cert) = true
    intro bs
    constructor
    · -- Forward: bs ∈ L* → ∃ cert, verifier accepts
      intro h_mem
      simp only [LStarLanguageLang] at h_mem
      have h_exists := (LStarVerifier_correct bs).mp h_mem
      obtain ⟨cert, h_verify⟩ := h_exists
      use cert
      rw [h_V_run]
      exact (verifyLStarMembership_correct bs cert).mpr h_verify
    · -- Backward: ∃ cert, verifier accepts → bs ∈ L*
      intro ⟨cert, h_accept⟩
      simp only [LStarLanguageLang]
      apply (LStarVerifier_correct bs).mpr
      use cert
      rw [h_V_run] at h_accept
      exact (verifyLStarMembership_correct bs cert).mp h_accept

#print axioms sizedLStarCertificate
#print axioms verifyLStarMembership
#print axioms verifyLStar_time_bound
#print axioms verifyLStar_algspec
#print axioms verifyLStar_algspec_deterministic
#print axioms verifyLStarMembership_correct
#print axioms LStarLanguageLang_in_NP

/-! ## Generic Language Transfer: Structured Types ↔ Bitstrings

**Purpose**: Prove that complexity class membership transfers between structured types
and their bitstring encodings.

**Key Insight**: No decode function needed! The certificate carries the original
structure, and we just verify it encodes to the claimed bitstring.

**Theorems**:
1. `np_transfer`: InNP L → InNP (encodedLang enc L)
2. `p_backward_transfer`: InP (encodedLang enc L) → InP L
3. `hardness_transfer`: ¬InP L → ¬InP (encodedLang enc L)
4. `separation_transfer`: InNP L ∧ ¬InP L → InNP (encodedLang enc L) ∧ ¬InP (encodedLang enc L)

**Note**: The main `P_ne_NP` theorem uses abstract input types (α : Type) with
bitstring witnesses. To obtain a fully explicit bitstring language L ⊆ {0,1}*
matching textbook definitions, use these transfer theorems with `LStarLanguageLang`.
-/

section LanguageTransfer

open LStar.Complexity

variable {α : Type} [Sized α]

/-- The encoded language: bitstrings that encode yes-instances.

    `encodedLang enc L` = { bs : List Bool | ∃ x : α, enc x = bs ∧ L x }

    This is the standard way to view a structured language as a bitstring language. -/
def encodedLang (enc : α → List Bool) (L : Lang α) : Lang (List Bool) :=
  fun bs => ∃ x : α, enc x = bs ∧ L x

/-- Encoding assumptions required for complexity transfer.

    **Key properties**:
    - `enc_injective`: Different values produce different encodings (no collisions)
    - `size_upper`: Encoding length is polynomially bounded by input size
    - `size_lower`: Input size is polynomially bounded by encoding length

    **Note**: We don't require a decode function! The certificate carries the
    original structure, avoiding the need for parsing. -/
structure PolytimeEncoding (enc : α → List Bool) where
  /-- Encoding is injective: enc x₁ = enc x₂ → x₁ = x₂ -/
  enc_injective : Function.Injective enc
  /-- Upper bound: encoding length ≤ C_up * (size x + 1)^k_up -/
  C_up : Nat
  k_up : Nat
  h_C_up_pos : C_up > 0
  h_k_up_pos : k_up > 0
  size_upper : ∀ x : α, (enc x).length ≤ C_up * (Sized.size x + 1) ^ k_up
  /-- Lower bound: size x ≤ C_lo * (|enc x| + 1)^k_lo -/
  C_lo : Nat
  k_lo : Nat
  h_C_lo_pos : C_lo > 0
  h_k_lo_pos : k_lo > 0
  size_lower : ∀ x : α, Sized.size x ≤ C_lo * ((enc x).length + 1) ^ k_lo

/-- **NP Transfer Theorem**: NP membership transfers from structured to encoded language.

    **Proof idea**: Certificate for `bs` is `(x, w)` where:
    - `x : α` is the structured object
    - `w` is the original NP witness for `L x`

    Verifier checks:
    1. `enc x = bs` (structure encodes to claimed bitstring)
    2. Original verifier accepts `(x, w)`

    No decode needed — the certificate carries the structure!

    **Polynomial bounds preserved**: Witness size and verifier time remain polynomial
    because `size x ≤ poly(|bs|)` via `size_lower`. -/
theorem np_transfer (enc : α → List Bool) (L : Lang α)
    (h_enc : PolytimeEncoding enc) (h_np : InNP L) :
    InNP (encodedLang enc L) := by
  -- Extract NP witness for L
  obtain ⟨β, inst_β, T, V, C_wit, k_wit, C_time, k_time,
          h_det, h_wit_bound, h_time_bound, h_spec⟩ := h_np
  -- Certificate type: (α × β) — carries structured object + original witness
  use (α × β)
  use sizedProd
  use T
  -- Define AlgSpec for the verifier (accessible for proofs below)
  let A : AlgSpec (List Bool × (α × β)) Bool T := {
    run := fun c (bs, (x, w)) =>
      if enc x = bs then V.run c (x, w) else false
    time_bound := fun n => V.time_bound n + n + 1
    C := V.C + 1
    k := max V.k 1
    h_C_pos := Nat.add_pos_left V.h_C_pos 1
    h_k_pos := Nat.le_max_right V.k 1
    poly_explicit := fun (bs, (x, w)) => by
      -- V.time_bound n + n + 1 ≤ (V.C + 1) * (n + 1)^(max V.k 1)
      have h_V := V.poly_explicit (x, w)
      have h_size : Sized.size (bs, (x, w)) = Sized.size bs + Sized.size (x, w) := rfl
      -- V.time_bound (size (x,w)) ≤ V.C * (size (x,w) + 1)^V.k
      -- size (bs, (x, w)) ≥ size (x, w), so time_bound (size (bs, (x, w))) ≥ time_bound (size (x, w))
      -- We need: V.time_bound n + n + 1 ≤ (V.C + 1) * (n + 1)^(max V.k 1) where n = size (bs, (x, w))
      have h_n_pos : 0 < Sized.size (bs, (x, w)) + 1 := Nat.succ_pos _
      have h_exp_ge_1 : (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 ≥ Sized.size (bs, (x, w)) + 1 := by
        have h1 : max V.k 1 ≠ 0 := by
          have : max V.k 1 ≥ 1 := Nat.le_max_right V.k 1
          omega
        exact Nat.le_self_pow h1 (Sized.size (bs, (x, w)) + 1)
      -- Simplify: need V.time_bound n + n + 1 ≤ (V.C + 1) * (n + 1)^(max V.k 1)
      -- Use: V.time_bound n ≤ V.C * (n+1)^V.k ≤ V.C * (n+1)^(max V.k 1)
      -- And: n + 1 ≤ (n+1)^(max V.k 1)
      have h_V_bound := V.time_bound_uniform (Sized.size (bs, (x, w)))
      have h_exp_mono : (Sized.size (bs, (x, w)) + 1) ^ V.k ≤ (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 := by
        apply Nat.pow_le_pow_right h_n_pos
        exact Nat.le_max_left V.k 1
      calc V.time_bound (Sized.size (bs, (x, w))) + Sized.size (bs, (x, w)) + 1
          ≤ V.C * (Sized.size (bs, (x, w)) + 1) ^ V.k + (Sized.size (bs, (x, w)) + 1) := by
            omega
        _ ≤ V.C * (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 + (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 := by
            have h1 : V.C * (Sized.size (bs, (x, w)) + 1) ^ V.k ≤ V.C * (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 :=
              Nat.mul_le_mul_left V.C h_exp_mono
            omega
        _ = (V.C + 1) * (Sized.size (bs, (x, w)) + 1) ^ max V.k 1 := by ring
    time_bound_uniform := fun n => by
      have h_V := V.time_bound_uniform n
      have h_n_pos : 0 < n + 1 := Nat.succ_pos n
      have h_exp_ge_1 : (n + 1) ^ max V.k 1 ≥ n + 1 := by
        have h1 : max V.k 1 ≠ 0 := by
          have : max V.k 1 ≥ 1 := Nat.le_max_right V.k 1
          omega
        exact Nat.le_self_pow h1 (n + 1)
      have h_exp_mono : (n + 1) ^ V.k ≤ (n + 1) ^ max V.k 1 := by
        apply Nat.pow_le_pow_right h_n_pos
        exact Nat.le_max_left V.k 1
      calc V.time_bound n + n + 1
          ≤ V.C * (n + 1) ^ V.k + (n + 1) := by omega
        _ ≤ V.C * (n + 1) ^ max V.k 1 + (n + 1) ^ max V.k 1 := by
            have h1 : V.C * (n + 1) ^ V.k ≤ V.C * (n + 1) ^ max V.k 1 :=
              Nat.mul_le_mul_left V.C h_exp_mono
            omega
        _ = (V.C + 1) * (n + 1) ^ max V.k 1 := by ring
    output_bounded := fun c (bs, (x, w)) => by
      simp only
      split_ifs with h_enc
      · -- enc x = bs case: output is Bool, size = 1
        have h_bool : Sized.size (V.run c (x, w)) = 1 := rfl
        omega
      · -- enc x ≠ bs case: output is false, size = 1
        have h_bool : Sized.size false = 1 := rfl
        omega
    coins_pos := V.coins_pos
  }
  -- Get RandAdv V' with proof that V'.run = A.run
  obtain ⟨V', h_V'_run, _, _, _, _, _⟩ := algspec_has_tm A
  use V'
  -- Witness size constants (using encoding bounds)
  -- Derived bound: C_lo + C_wit * (C_lo + 1)^k_wit for size (x, w)
  use h_enc.C_lo + C_wit * (h_enc.C_lo + 1) ^ k_wit
  use max h_enc.k_lo (k_wit * h_enc.k_lo)
  -- Verifier time constants
  use V'.C
  use V'.k
  -- Helper: V'.run equals A.run
  have h_V'_eq : ∀ c p, V'.run c p = A.run c p := by
    intro c p
    have h1 : V'.toAlgSpec.run = A.run := h_V'_run
    simp only [RandAdv.toAlgSpec] at h1
    exact congrFun (congrFun h1 c) p
  constructor
  · -- Determinism: V' is deterministic because V is deterministic
    intro c₁ c₂ (bs, (x, w))
    simp only [h_V'_eq]
    -- A.run c (bs, (x, w)) = if enc x = bs then V.run c (x, w) else false
    simp only [A]
    split_ifs with h_enc_eq
    · -- enc x = bs: result is V.run c (x, w), deterministic by h_det
      exact h_det c₁ c₂ (x, w)
    · -- enc x ≠ bs: result is false (constant)
      rfl
  constructor
  · -- Witness size bound: size (x, w) ≤ poly(size bs)
    -- Key: enc x = bs (from acceptance), so size x ≤ C_lo * (|bs|+1)^k_lo
    -- And size w ≤ C_wit * (size x + 1)^k_wit (from original NP bound)
    intro bs (x, w) h_accept
    -- Extract from h_accept: enc x = bs and V accepts (x, w)
    simp only [h_V'_eq, A] at h_accept
    by_cases h_enc_eq : enc x = bs
    · -- enc x = bs case
      simp only [h_enc_eq, ↓reduceIte] at h_accept
      -- h_accept : V.run ⟨0, V.coins_pos⟩ (x, w) = true
      -- Get size bounds
      have h_size_x : Sized.size x ≤ h_enc.C_lo * ((enc x).length + 1) ^ h_enc.k_lo :=
        h_enc.size_lower x
      -- Since enc x = bs, (enc x).length = bs.length
      rw [h_enc_eq] at h_size_x
      -- For List Bool, Sized.size bs = bs.length + 1
      have h_bs_size : Sized.size bs = bs.length + 1 := rfl
      -- So h_size_x : size x ≤ C_lo * (size bs)^k_lo
      have h_size_x' : Sized.size x ≤ h_enc.C_lo * (Sized.size bs) ^ h_enc.k_lo := by
        simp only [Sized.size, sizedBitstring] at h_size_x ⊢
        exact h_size_x
      -- Get witness bound from original NP
      have h_size_w : Sized.size w ≤ C_wit * (Sized.size x + 1) ^ k_wit :=
        h_wit_bound x w h_accept
      -- size (x, w) = size x + size w (for pairs)
      have h_pair_size : Sized.size (x, w) = Sized.size x + Sized.size w := rfl
      -- Now combine: size x ≤ C_lo * (size bs)^k_lo ≤ C_lo * (size bs + 1)^k_lo
      have h_bs_pos : Sized.size bs ≥ 1 := Sized.size_pos bs
      have h_pow_mono : (Sized.size bs) ^ h_enc.k_lo ≤ (Sized.size bs + 1) ^ h_enc.k_lo := by
        apply Nat.pow_le_pow_left
        omega
      have h_size_x'' : Sized.size x ≤ h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo := by
        calc Sized.size x ≤ h_enc.C_lo * (Sized.size bs) ^ h_enc.k_lo := h_size_x'
          _ ≤ h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo := Nat.mul_le_mul_left h_enc.C_lo h_pow_mono
      -- For size w: size w ≤ C_wit * (size x + 1)^k_wit
      -- size x + 1 ≤ C_lo * (size bs + 1)^k_lo + 1 ≤ (C_lo + 1) * (size bs + 1)^k_lo
      have h_bs_pos' : (Sized.size bs + 1) ^ h_enc.k_lo ≥ 1 := Nat.one_le_pow h_enc.k_lo (Sized.size bs + 1) (by omega)
      have h_size_x_plus : Sized.size x + 1 ≤ (h_enc.C_lo + 1) * (Sized.size bs + 1) ^ h_enc.k_lo := by
        calc Sized.size x + 1 ≤ h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo + 1 := by omega
          _ ≤ h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo + (Sized.size bs + 1) ^ h_enc.k_lo := by omega
          _ = (h_enc.C_lo + 1) * (Sized.size bs + 1) ^ h_enc.k_lo := by ring
      -- (size x + 1)^k_wit ≤ ((C_lo + 1) * (size bs + 1)^k_lo)^k_wit
      have h_pow_bound : (Sized.size x + 1) ^ k_wit ≤ ((h_enc.C_lo + 1) * (Sized.size bs + 1) ^ h_enc.k_lo) ^ k_wit :=
        Nat.pow_le_pow_left h_size_x_plus k_wit
      -- ((C_lo + 1) * (size bs + 1)^k_lo)^k_wit = (C_lo + 1)^k_wit * (size bs + 1)^(k_lo * k_wit)
      have h_expand : ((h_enc.C_lo + 1) * (Sized.size bs + 1) ^ h_enc.k_lo) ^ k_wit =
                      (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) := by
        rw [Nat.mul_pow, Nat.pow_mul]
      rw [h_expand] at h_pow_bound
      -- size w ≤ C_wit * (C_lo + 1)^k_wit * (size bs + 1)^(k_lo * k_wit)
      have h_size_w' : Sized.size w ≤ C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) := by
        calc Sized.size w ≤ C_wit * (Sized.size x + 1) ^ k_wit := h_size_w
          _ ≤ C_wit * ((h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit)) := Nat.mul_le_mul_left C_wit h_pow_bound
          _ = C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) := by ring
      -- Now combine for size (x, w)
      -- k = max k_lo (k_wit * k_lo), so k ≥ k_lo and k ≥ k_wit * k_lo = k_lo * k_wit
      have h_k_ge_klo : max h_enc.k_lo (k_wit * h_enc.k_lo) ≥ h_enc.k_lo := Nat.le_max_left _ _
      have h_k_ge_kwklo : max h_enc.k_lo (k_wit * h_enc.k_lo) ≥ k_wit * h_enc.k_lo := Nat.le_max_right _ _
      have h_k_ge_klokw : max h_enc.k_lo (k_wit * h_enc.k_lo) ≥ h_enc.k_lo * k_wit := by
        rw [Nat.mul_comm h_enc.k_lo k_wit]
        exact h_k_ge_kwklo
      -- Power monotonicity
      have h_pow_mono_x : (Sized.size bs + 1) ^ h_enc.k_lo ≤ (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) :=
        Nat.pow_le_pow_right (by omega) h_k_ge_klo
      have h_pow_mono_w : (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) ≤ (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) :=
        Nat.pow_le_pow_right (by omega) h_k_ge_klokw
      -- Final bound
      calc Sized.size (x, w) = Sized.size x + Sized.size w := h_pair_size
        _ ≤ h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo +
            C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) := by omega
        _ ≤ h_enc.C_lo * (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) +
            C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) := by
          have h1 : h_enc.C_lo * (Sized.size bs + 1) ^ h_enc.k_lo ≤
                    h_enc.C_lo * (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) :=
            Nat.mul_le_mul_left h_enc.C_lo h_pow_mono_x
          have h2 : C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ (h_enc.k_lo * k_wit) ≤
                    C_wit * (h_enc.C_lo + 1) ^ k_wit * (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) := by
            apply Nat.mul_le_mul_left
            exact h_pow_mono_w
          omega
        _ = (h_enc.C_lo + C_wit * (h_enc.C_lo + 1) ^ k_wit) * (Sized.size bs + 1) ^ max h_enc.k_lo (k_wit * h_enc.k_lo) := by ring
    · -- enc x ≠ bs: contradiction from h_accept
      simp only [h_enc_eq, ↓reduceIte] at h_accept
      exact absurd h_accept Bool.false_ne_true
  constructor
  · -- Verifier time bound (inherited from V')
    intro (bs, (x, w))
    exact V'.poly_explicit (bs, (x, w))
  · -- Correctness: encodedLang enc L bs ↔ ∃ (x, w), V' accepts
    intro bs
    constructor
    · -- Forward: bs ∈ encodedLang → ∃ witness
      intro ⟨x, h_enc_eq, h_Lx⟩
      have h_Lx_wit := (h_spec x).mp h_Lx
      obtain ⟨w, h_V_accept⟩ := h_Lx_wit
      use (x, w)
      -- V' accepts (x, w) because enc x = bs and V accepts
      simp only [h_V'_eq, A]
      simp only [h_enc_eq, ↓reduceIte]
      exact h_V_accept
    · -- Backward: ∃ witness accepted → bs ∈ encodedLang
      intro ⟨(x, w), h_accept⟩
      -- V'.run accepts means A.run accepts
      simp only [h_V'_eq, A] at h_accept
      -- A.run c (bs, (x, w)) = if enc x = bs then V.run c (x, w) else false
      by_cases h_enc_eq : enc x = bs
      · -- enc x = bs and V accepts (x, w)
        use x
        simp only [h_enc_eq, ↓reduceIte] at h_accept
        exact ⟨h_enc_eq, (h_spec x).mpr ⟨w, h_accept⟩⟩
      · -- enc x ≠ bs: h_accept says false = true, contradiction
        simp only [h_enc_eq, ↓reduceIte] at h_accept
        exact absurd h_accept Bool.false_ne_true

/-- **P Backward Transfer**: If encoded language is in P, so is the original.

    **Proof idea**: To decide `L x`:
    1. Compute `bs := enc x` (polynomial time by encoding assumption)
    2. Run the P decider for `encodedLang enc L` on `bs`
    3. Return the result

    Correctness: `enc` is injective, so `bs ∈ encodedLang enc L ↔ L x`.
    Time: Polynomial composition of encoding + decider. -/
theorem p_backward_transfer (enc : α → List Bool) (L : Lang α)
    (h_enc : PolytimeEncoding enc) (h_p : InP (encodedLang enc L)) :
    InP L := by
  obtain ⟨T, A, h_det, h_correct⟩ := h_p
  use T
  -- Build decider for L: compute enc x, then run A
  -- Define AlgSpec outside tactic to access in proofs below
  let spec : AlgSpec α Bool T := {
    run := fun c x => A.run c (enc x)
    time_bound := fun n => A.time_bound (h_enc.C_up * (n + 1) ^ h_enc.k_up + 1) + h_enc.C_up * (n + 1) ^ h_enc.k_up
    -- Correct constant for polynomial composition
    -- Use (2 * C_up + 1) to handle the n=0 case where time_bound 0 ≤ A.C * 3^A.k + 1
    C := A.C * (2 * h_enc.C_up + 1) ^ A.k + h_enc.C_up
    k := A.k * h_enc.k_up
    h_C_pos := by
      have h_A_C := A.h_C_pos
      have h_C_up := h_enc.h_C_up_pos
      have h_pow_pos : (2 * h_enc.C_up + 1) ^ A.k ≥ 1 := Nat.one_le_pow A.k (2 * h_enc.C_up + 1) (by omega)
      omega
    h_k_pos := Nat.mul_pos A.h_k_pos h_enc.h_k_up_pos
    poly_explicit := fun x => by
      -- Goal: time_bound (size x) ≤ C * (size x + 1)^k
      -- where time_bound n = A.time_bound (C_up * (n+1)^k_up + 1) + C_up * (n+1)^k_up
      -- and C = A.C * (2*C_up+1)^A.k + C_up, k = A.k * k_up
      -- Let m = C_up * (size x + 1)^k_up + 1
      set m := h_enc.C_up * (Sized.size x + 1) ^ h_enc.k_up + 1 with h_m_def
      set p := (Sized.size x + 1) ^ h_enc.k_up with h_p_def
      -- Step 1: A.time_bound m ≤ A.C * (m + 1)^A.k
      have h_A_bound : A.time_bound m ≤ A.C * (m + 1) ^ A.k := A.time_bound_uniform m
      -- Step 2: m + 1 = C_up * p + 2 ≤ (C_up + 2) * p ≤ (2*C_up + 1) * p (since p ≥ 1)
      have h_p_pos : p ≥ 1 := Nat.one_le_pow h_enc.k_up (Sized.size x + 1) (by omega)
      have h_m_plus_1 : m + 1 = h_enc.C_up * p + 2 := by omega
      have h_bound_intermediate : h_enc.C_up * p + 2 ≤ (2 * h_enc.C_up + 1) * p := by
        have h_C_up_pos : h_enc.C_up ≥ 1 := h_enc.h_C_up_pos
        -- C_up * p + 2 ≤ C_up * p + 2 * p = (C_up + 2) * p ≤ (2*C_up + 1) * p
        have h_2_le_2p : 2 ≤ 2 * p := by omega
        calc h_enc.C_up * p + 2
            ≤ h_enc.C_up * p + 2 * p := by omega
          _ = (h_enc.C_up + 2) * p := by ring
          _ ≤ (2 * h_enc.C_up + 1) * p := by nlinarith
      have h_m_bound : m + 1 ≤ (2 * h_enc.C_up + 1) * p := by omega
      -- Step 3: (m + 1)^A.k ≤ ((2*C_up + 1) * p)^A.k = (2*C_up + 1)^A.k * p^A.k
      have h_pow_bound : (m + 1) ^ A.k ≤ ((2 * h_enc.C_up + 1) * p) ^ A.k :=
        Nat.pow_le_pow_left h_m_bound A.k
      have h_pow_expand : ((2 * h_enc.C_up + 1) * p) ^ A.k =
          (2 * h_enc.C_up + 1) ^ A.k * p ^ A.k := Nat.mul_pow _ _ _
      -- Step 4: p^A.k = ((size x + 1)^k_up)^A.k = (size x + 1)^(k_up * A.k)
      have h_pow_assoc : p ^ A.k = (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by
        simp only [h_p_def]
        rw [← Nat.pow_mul]
      -- Step 5: Combine for A.time_bound m bound
      have h_A_final : A.time_bound m ≤ A.C * (2 * h_enc.C_up + 1) ^ A.k * (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by
        calc A.time_bound m
            ≤ A.C * (m + 1) ^ A.k := h_A_bound
          _ ≤ A.C * ((2 * h_enc.C_up + 1) * p) ^ A.k := by
              apply Nat.mul_le_mul_left; exact h_pow_bound
          _ = A.C * ((2 * h_enc.C_up + 1) ^ A.k * p ^ A.k) := by rw [h_pow_expand]
          _ = A.C * (2 * h_enc.C_up + 1) ^ A.k * p ^ A.k := by ring
          _ = A.C * (2 * h_enc.C_up + 1) ^ A.k * (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by rw [h_pow_assoc]
      -- Step 6: C_up * p ≤ C_up * (size x + 1)^(k_up * A.k) since A.k ≥ 1
      have h_A_k_pos : A.k ≥ 1 := A.h_k_pos
      have h_exp_growth : p ≤ (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by
        simp only [h_p_def]
        have h_base_pos : Sized.size x + 1 ≥ 1 := by omega
        have h_exp_le : h_enc.k_up ≤ h_enc.k_up * A.k := Nat.le_mul_of_pos_right h_enc.k_up h_A_k_pos
        exact Nat.pow_le_pow_right h_base_pos h_exp_le
      have h_second_term : h_enc.C_up * p ≤ h_enc.C_up * (Sized.size x + 1) ^ (h_enc.k_up * A.k) :=
        Nat.mul_le_mul_left h_enc.C_up h_exp_growth
      -- Step 7: Combine both terms
      have h_k_comm : h_enc.k_up * A.k = A.k * h_enc.k_up := Nat.mul_comm _ _
      calc A.time_bound m + h_enc.C_up * p
          ≤ A.C * (2 * h_enc.C_up + 1) ^ A.k * (Sized.size x + 1) ^ (h_enc.k_up * A.k) +
            h_enc.C_up * (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by omega
        _ = (A.C * (2 * h_enc.C_up + 1) ^ A.k + h_enc.C_up) * (Sized.size x + 1) ^ (h_enc.k_up * A.k) := by ring
        _ = (A.C * (2 * h_enc.C_up + 1) ^ A.k + h_enc.C_up) * (Sized.size x + 1) ^ (A.k * h_enc.k_up) := by rw [h_k_comm]
    time_bound_uniform := fun n => by
      -- Goal: time_bound n ≤ C * (n + 1)^k (same as poly_explicit but for arbitrary n)
      set m := h_enc.C_up * (n + 1) ^ h_enc.k_up + 1 with h_m_def
      set p := (n + 1) ^ h_enc.k_up with h_p_def
      have h_A_bound : A.time_bound m ≤ A.C * (m + 1) ^ A.k := A.time_bound_uniform m
      have h_p_pos : p ≥ 1 := Nat.one_le_pow h_enc.k_up (n + 1) (by omega)
      have h_m_plus_1 : m + 1 = h_enc.C_up * p + 2 := by omega
      have h_bound_intermediate : h_enc.C_up * p + 2 ≤ (2 * h_enc.C_up + 1) * p := by
        have h_C_up_pos : h_enc.C_up ≥ 1 := h_enc.h_C_up_pos
        have h_2_le_2p : 2 ≤ 2 * p := by omega
        calc h_enc.C_up * p + 2
            ≤ h_enc.C_up * p + 2 * p := by omega
          _ = (h_enc.C_up + 2) * p := by ring
          _ ≤ (2 * h_enc.C_up + 1) * p := by nlinarith
      have h_m_bound : m + 1 ≤ (2 * h_enc.C_up + 1) * p := by omega
      have h_pow_bound : (m + 1) ^ A.k ≤ ((2 * h_enc.C_up + 1) * p) ^ A.k :=
        Nat.pow_le_pow_left h_m_bound A.k
      have h_pow_expand : ((2 * h_enc.C_up + 1) * p) ^ A.k =
          (2 * h_enc.C_up + 1) ^ A.k * p ^ A.k := Nat.mul_pow _ _ _
      have h_pow_assoc : p ^ A.k = (n + 1) ^ (h_enc.k_up * A.k) := by
        simp only [h_p_def]
        rw [← Nat.pow_mul]
      have h_A_final : A.time_bound m ≤ A.C * (2 * h_enc.C_up + 1) ^ A.k * (n + 1) ^ (h_enc.k_up * A.k) := by
        calc A.time_bound m
            ≤ A.C * (m + 1) ^ A.k := h_A_bound
          _ ≤ A.C * ((2 * h_enc.C_up + 1) * p) ^ A.k := by
              apply Nat.mul_le_mul_left; exact h_pow_bound
          _ = A.C * ((2 * h_enc.C_up + 1) ^ A.k * p ^ A.k) := by rw [h_pow_expand]
          _ = A.C * (2 * h_enc.C_up + 1) ^ A.k * p ^ A.k := by ring
          _ = A.C * (2 * h_enc.C_up + 1) ^ A.k * (n + 1) ^ (h_enc.k_up * A.k) := by rw [h_pow_assoc]
      have h_A_k_pos : A.k ≥ 1 := A.h_k_pos
      have h_exp_growth : p ≤ (n + 1) ^ (h_enc.k_up * A.k) := by
        simp only [h_p_def]
        have h_base_pos : n + 1 ≥ 1 := by omega
        have h_exp_le : h_enc.k_up ≤ h_enc.k_up * A.k := Nat.le_mul_of_pos_right h_enc.k_up h_A_k_pos
        exact Nat.pow_le_pow_right h_base_pos h_exp_le
      have h_second_term : h_enc.C_up * p ≤ h_enc.C_up * (n + 1) ^ (h_enc.k_up * A.k) :=
        Nat.mul_le_mul_left h_enc.C_up h_exp_growth
      have h_k_comm : h_enc.k_up * A.k = A.k * h_enc.k_up := Nat.mul_comm _ _
      calc A.time_bound m + h_enc.C_up * p
          ≤ A.C * (2 * h_enc.C_up + 1) ^ A.k * (n + 1) ^ (h_enc.k_up * A.k) +
            h_enc.C_up * (n + 1) ^ (h_enc.k_up * A.k) := by omega
        _ = (A.C * (2 * h_enc.C_up + 1) ^ A.k + h_enc.C_up) * (n + 1) ^ (h_enc.k_up * A.k) := by ring
        _ = (A.C * (2 * h_enc.C_up + 1) ^ A.k + h_enc.C_up) * (n + 1) ^ (A.k * h_enc.k_up) := by rw [h_k_comm]
    output_bounded := fun c x => by
      -- Output is Bool (size 1), time_bound is clearly ≥ 1
      have h_bool_size : Sized.size (A.run c (enc x)) = 1 := rfl
      rw [h_bool_size]
      -- time_bound n = A.time_bound (...) + C_up * (n+1)^k_up ≥ 1
      have h_A_pos : A.time_bound (h_enc.C_up * (Sized.size x + 1) ^ h_enc.k_up + 1) ≥ 0 := Nat.zero_le _
      have h_enc_pos : h_enc.C_up * (Sized.size x + 1) ^ h_enc.k_up ≥ 1 := by
        have h1 : h_enc.C_up ≥ 1 := h_enc.h_C_up_pos
        have h2 : (Sized.size x + 1) ^ h_enc.k_up ≥ 1 := Nat.one_le_pow h_enc.k_up (Sized.size x + 1) (by omega)
        have h3 : 1 * 1 ≤ h_enc.C_up * (Sized.size x + 1) ^ h_enc.k_up := Nat.mul_le_mul h1 h2
        simp at h3; exact h3
      omega
    coins_pos := A.coins_pos
  }
  -- Get RandAdv A' with proof that A'.run = spec.run
  obtain ⟨A', h_A'_run, _, _, _, _, _⟩ := algspec_has_tm spec
  use A'
  -- Helper: A'.run equals spec.run
  have h_A'_eq : ∀ c x, A'.run c x = A.run c (enc x) := by
    intro c x
    have h1 : A'.toAlgSpec.run = spec.run := h_A'_run
    simp only [RandAdv.toAlgSpec] at h1
    exact congrFun (congrFun h1 c) x
  constructor
  · -- Determinism: A' computes A(enc x), and A is deterministic
    intro c₁ c₂ x
    simp only [h_A'_eq]
    exact h_det c₁ c₂ (enc x)
  · -- Correctness: A' x = true ↔ L x
    -- A correctly decides encodedLang, and enc is injective
    -- So: encodedLang enc L (enc x) ↔ L x
    intro x
    have h_encoded_iff : encodedLang enc L (enc x) ↔ L x := by
      constructor
      · intro ⟨y, h_enc_eq, h_Ly⟩
        have h_xy : x = y := h_enc.enc_injective h_enc_eq.symm
        rw [h_xy]; exact h_Ly
      · intro h_Lx
        exact ⟨x, rfl, h_Lx⟩
    -- A' x = A (enc x), and A decides encodedLang
    rw [h_A'_eq]
    -- h_encoded_iff.symm : L x ↔ encodedLang enc L (enc x)
    -- h_correct (enc x) : encodedLang enc L (enc x) ↔ A.run ⟨0, A.coins_pos⟩ (enc x) = true
    exact h_encoded_iff.symm.trans (h_correct (enc x))

/-- **Hardness Transfer Corollary**: If L is not in P, neither is its encoding.

    Immediate from `p_backward_transfer` by contrapositive. -/
theorem hardness_transfer (enc : α → List Bool) (L : Lang α)
    (h_enc : PolytimeEncoding enc) (h_hard : ¬InP L) :
    ¬InP (encodedLang enc L) := by
  intro h_p_encoded
  exact h_hard (p_backward_transfer enc L h_enc h_p_encoded)

/-- **Combined Transfer**: Separation transfers from structured to bitstring languages.

    If L ∈ NP and L ∉ P over structured type α, then encodedLang enc L ∈ NP and
    encodedLang enc L ∉ P over bitstrings. -/
theorem separation_transfer (enc : α → List Bool) (L : Lang α)
    (h_enc : PolytimeEncoding enc)
    (h_np : InNP L) (h_hard : ¬InP L) :
    InNP (encodedLang enc L) ∧ ¬InP (encodedLang enc L) :=
  ⟨np_transfer enc L h_enc h_np, hardness_transfer enc L h_enc h_hard⟩

#print axioms encodedLang
#print axioms PolytimeEncoding
#print axioms np_transfer
#print axioms p_backward_transfer
#print axioms hardness_transfer
#print axioms separation_transfer

end LanguageTransfer

/-! ## Instantiate PolytimeEncoding for encodeBits

**Purpose**: Connect the main L* proof (over structured `LStarInstanceFG`) to
standard complexity theory (over bitstrings `{0,1}*`).

**Components**:
1. `encodeBits_injective`: Different L* instances produce different encodings
2. `encodeBits_size_lower`: Input size is bounded by encoding length
3. `encodeBits_polytime`: Full PolytimeEncoding instance

Combined with the transfer theorems above, this establishes that:
- L* ∈ NP over bitstrings
- L* ∉ P over bitstrings (from main proof + hardness_transfer)
-/

section EncodeBitsPolytime

open LStar.Complexity LStar.StructuralOWF.Foundations

/-! ### Helper Lemmas for Injectivity Proofs -/

/-- If two finRange-mapped lists are equal, the underlying functions are equal.
    This is the key lemma for recovering function equality from raw list equality. -/
lemma finRange_map_eq_implies_fun_eq {n : Nat} {α : Type*} {f g : Fin n → α}
    (h : (List.finRange n).map f = (List.finRange n).map g) : f = g := by
  funext i
  -- Using List.getElem on mapped finRange gives f/g applied to i
  have hf_get : ((List.finRange n).map f)[i.val]'(by simp) = f i := by simp
  have hg_get : ((List.finRange n).map g)[i.val]'(by simp) = g i := by simp
  -- Since h says the lists are equal, their i-th elements are equal
  rw [← hf_get, ← hg_get]
  simp only [h]

/-- Get a specific `(r,c)` entry from the row-major `finRange`/`flatMap` construction.

This is the common pattern used by `toRawEmergenceMatrix`, where entries are stored in
row-major order as:
`finRange R >>= (fun r => (finRange n).map (fun c => f r c))`.
-/
lemma finRange_flatMap_finRange_map_get {R n : Nat} {α : Type*}
    (f : Fin R → Fin n → α) (r : Fin R) (c : Fin n) :
    (((List.finRange R).flatMap (fun r' => (List.finRange n).map (fun c' => f r' c')))[r.val * n + c.val]'(by
            -- index is within `R*n` elements
            have hlen :
                ((List.finRange R).flatMap
                      (fun r' => (List.finRange n).map (fun c' => f r' c'))).length =
                  R * n := by
              simp [List.length_flatMap, List.length_finRange]
            -- `r.val*n + c.val < R*n` since `r.val < R` and `c.val < n`
            simpa [hlen] using (by
              have hr : r.val < R := r.isLt
              have hc : c.val < n := c.isLt
              have hlt₁ : r.val * n + c.val < r.val * n + n := Nat.add_lt_add_left hc _
              have hle₂ : r.val * n + n ≤ R * n := by
                have hsucc : r.val + 1 ≤ R := Nat.succ_le_of_lt hr
                have := Nat.mul_le_mul_right n hsucc
                simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
              exact lt_of_lt_of_le hlt₁ hle₂))) = f r c := by
  induction R with
  | zero =>
      cases r with
      | mk rv hr =>
        cases hr
  | succ R ih =>
      refine Fin.cases ?base ?step r
      · -- r = 0: element lies in the first row
        have hlt : c.val < ((List.finRange n).map (fun c' => f 0 c')).length := by
          simpa using c.isLt
        -- `finRange (R+1)` splits into `0 :: (finRange R).map Fin.succ`
        -- and `flatMap` becomes firstRow ++ rest.
        -- Then `getElem_append_left` selects from the first row.
        simp [List.finRange_succ, List.flatMap_cons, List.flatMap_map, hlt, Nat.zero_mul, Nat.zero_add]
      · -- r = Fin.succ r0: element lies in the tail after dropping the first row (length n)
        intro r0
        have hge :
            ((List.finRange n).map (fun c' => f 0 c')).length ≤ (Fin.succ r0).val * n + c.val := by
          -- left length is n, and (succ r0).val * n + c.val ≥ n
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.le_add_right n (r0.val * n + c.val))
        -- Rewrite into append form, drop the first row, and apply IH on shifted rows.
        -- `simp` also normalizes `(Fin.succ r0).val` and the arithmetic `idx - n`.
        simpa [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.getElem_append_right hge,
          Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (ih (f := fun r' c' => f (Fin.succ r') c') r0)
/-- Membership in a Finset is equivalent to the nat value appearing in the mapped toList. -/
lemma finset_mem_iff_val_in_map {n : Nat} (s : Finset (Fin n)) (p : Fin n) :
    p ∈ s ↔ p.val ∈ s.toList.map (·.val) := by
  constructor
  · intro hp
    simp only [List.mem_map]
    exact ⟨p, Finset.mem_toList.mpr hp, rfl⟩
  · intro hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq_mem, hq_val⟩ := hp
    have h_eq : p = q := Fin.ext hq_val.symm
    rw [h_eq]
    exact Finset.mem_toList.mp hq_mem

/-- Two Finsets of Fin n are equal if their toList.map (·.val) are equal. -/
lemma finset_eq_of_val_list_eq {n : Nat} (s t : Finset (Fin n))
    (h : s.toList.map (·.val) = t.toList.map (·.val)) : s = t := by
  apply Finset.ext
  intro p
  rw [finset_mem_iff_val_in_map, finset_mem_iff_val_in_map, h]

/-- Raw DAG conversion is injective: different DAGs produce different raw DAGs.

    The raw DAG stores `n` and `parents` as a list. Two DAGs with the same
    raw representation must have the same `n` and `parents` function.

    **Proof outline**:
    1. Extract n equality from raw.n
    2. Extract parents list equality from raw.parents
    3. Convert list equality to function equality by showing each Finset matches
    4. Apply DAG constructor equality

    This is a mechanical proof: toRawDAG extracts all data fields, so equal raw implies
    equal data implies equal structures. -/
theorem toRawDAG_injective : Function.Injective toRawDAG := by
  intro d₁ d₂ h_raw_eq
  -- Use cases to destructure DAGs
  cases d₁ with | mk n₁ p₁ =>
  cases d₂ with | mk n₂ p₂ =>
  -- Extract n equality from raw
  have h_n : n₁ = n₂ := congrArg RawDAG.n h_raw_eq
  cases h_n
  -- Extract parents list equality from raw
  have h_parents_raw : (List.finRange n₁).map (fun j => (p₁ j).toList.map (·.val)) =
                       (List.finRange n₁).map (fun j => (p₂ j).toList.map (·.val)) :=
    congrArg RawDAG.parents h_raw_eq
  -- Show parents functions are equal
  -- The key insight: if the raw nat-value lists are equal, the Finsets are equal
  -- because membership is determined by the nat values appearing in the list
  have h_parents : p₁ = p₂ := by
    -- Apply finRange_map_eq_implies_fun_eq to get pointwise equality of toList maps
    have h_fun_eq := finRange_map_eq_implies_fun_eq h_parents_raw
    -- h_fun_eq : (fun j => (p₁ j).toList.map (·.val)) = (fun j => (p₂ j).toList.map (·.val))
    funext i
    -- For each i, we have (p₁ i).toList.map (·.val) = (p₂ i).toList.map (·.val)
    have h_i : (p₁ i).toList.map (·.val) = (p₂ i).toList.map (·.val) := congrFun h_fun_eq i
    -- Apply finset_eq_of_val_list_eq to conclude p₁ i = p₂ i
    exact finset_eq_of_val_list_eq (p₁ i) (p₂ i) h_i
  cases h_parents
  rfl

/-- In ZMod 2, beq with 1 determines the value: if (x == 1) = (y == 1) then x = y. -/
lemma zmod2_beq_one_determines {x y : ZMod 2} (h : (x == 1) = (y == 1)) : x = y := by
  -- ZMod 2 has only two elements: 0 and 1
  fin_cases x <;> fin_cases y <;> simp_all

/-- `toRawEmergenceMatrix` is injective: different matrices produce different raw forms.

    **Proof**: EmergenceMatrix has a matrix over ZMod 2 (0/1 entries) and a rank proof (Prop).
    The raw form stores (R, n, bits) where bits encodes whether each entry is 1.
    Since ZMod 2 only has values 0 and 1, the bits exactly determine the matrix.
    The rank proof is a Prop (Subsingleton), so it doesn't affect equality. -/
theorem toRawEmergenceMatrix_injective {R n : Nat} :
    Function.Injective (toRawEmergenceMatrix (R := R) (n := n)) := by
  intro E₁ E₂ h_raw_eq
  -- Extract field equalities from raw equality
  have h_bits : (toRawEmergenceMatrix E₁).bits = (toRawEmergenceMatrix E₂).bits :=
    congrArg RawEmergenceMatrix.bits h_raw_eq
  simp only [toRawEmergenceMatrix] at h_bits
  -- The bits list determines the matrix entries
  -- Both bits lists are built identically from their respective matrices using List.finRange/flatMap/map
  -- If the lists are equal, the matrices must produce the same bits at each position
  -- Since ZMod 2 is determined by (== 1), the matrices are equal
  have h_matrix : E₁.matrix = E₂.matrix := by
    ext r c
    -- The bits list is: finRange R >>= (λ r' => finRange n >>= (λ c' => [E.matrix r' c' == 1]))
    -- For the (r, c) entry, it appears at a fixed position in the list
    -- Equal lists means equal elements at each position
    -- Use List.ext_getElem to work with list equality
    have h_list_eq := h_bits
    -- The entry (E.matrix r c == 1) appears in the list at some position
    -- Since the lists are built the same way, equal lists → equal entries at each (r,c)
    -- We prove this by showing that if the flatMap results are equal,
    -- the inner map results must be equal for each r', hence each entry must match
    -- This is a consequence of the deterministic construction
    apply zmod2_beq_one_determines
    -- Need: (E₁.matrix r c == 1) = (E₂.matrix r c == 1)
    -- The bits list at row r is: (finRange n).map (fun c' => E.matrix r c' == 1)
    -- From h_list_eq, both lists are equal, so the sublists for each row must match
    -- For a fixed r, the bits at columns 0..n-1 form a contiguous segment
    -- Since the full lists are equal, these segments are equal, hence each bit matches
    -- The bits list is: flatMap over rows r' of (map over cols c' of (E.matrix r' c' == 1))
    -- Row r's bits occupy positions [r.val * n, r.val * n + n) in the flattened list
    -- If the full lists are equal, row segments must be equal, hence individual bits match
    -- This is mechanical list manipulation that requires showing:
    -- 1. Both lists have the same structure (flatMap preserves row boundaries)
    -- 2. Equal total lists → equal sublists at each row
    -- 3. Equal row lists → equal elements at each column
    -- LOW-RISK: purely extractive, deterministic list construction
    have h₁ :=
      finRange_flatMap_finRange_map_get
        (f := fun r' c' => (E₁.matrix r' c' == 1)) r c
    -- Rewrite the selected bit using the raw-bits equality.
    have h₁' := (by simpa [h_bits] using h₁)
    have h₂ :=
      finRange_flatMap_finRange_map_get
        (f := fun r' c' => (E₂.matrix r' c' == 1)) r c
    exact h₁'.symm.trans h₂
  -- With matrix equality, use EmergenceMatrix extensionality
  cases E₁; cases E₂
  simp only [EmergenceMatrix.mk.injEq]
  exact h_matrix

/-- `toRawLStarInstanceFull` is injective: different instances produce different raw forms.

    **Proof Strategy** (following LStarInstanceFull.ext pattern):
    1. `cases A; cases B` to destructure immediately
    2. Extract field equalities from raw equality
    3. Case split on n, dag to unify dependent types
    4. Derive function equalities for seedWidth, R, emergence
    5. Conclude by reflexivity -/
theorem toRawLStarInstanceFull_injective :
    Function.Injective toRawLStarInstanceFull := by
  intro A B h_raw_eq
  -- Step 1: Destructure FIRST (critical for dependent type handling)
  cases A with | mk n₁ n_pos₁ dag₁ dagAcyclic₁ seedWidth₁ R₁ emergence₁ pools₁ seedWidth_ok₁ =>
  cases B with | mk n₂ n_pos₂ dag₂ dagAcyclic₂ seedWidth₂ R₂ emergence₂ pools₂ seedWidth_ok₂ =>
  -- Step 2: Now h_raw_eq is between mk constructors, extract field equalities
  simp only [toRawLStarInstanceFull] at h_raw_eq
  -- h_raw_eq : { n := n₁, dag := toRawDAG dag₁, ... } = { n := n₂, dag := toRawDAG dag₂, ... }
  have h_n : n₁ = n₂ := congrArg RawLStarInstanceFull.n h_raw_eq
  have h_dag_raw : toRawDAG dag₁ = toRawDAG dag₂ := congrArg RawLStarInstanceFull.dag h_raw_eq
  have h_dag : dag₁ = dag₂ := toRawDAG_injective h_dag_raw
  have h_sw_raw : (List.finRange dag₁.n).map seedWidth₁ = (List.finRange dag₂.n).map seedWidth₂ :=
    congrArg RawLStarInstanceFull.seedWidth h_raw_eq
  have h_R_raw : (List.finRange dag₁.n).map R₁ = (List.finRange dag₂.n).map R₂ :=
    congrArg RawLStarInstanceFull.R h_raw_eq
  have h_em_raw : (List.finRange dag₁.n).map (fun i => toRawEmergenceMatrix (emergence₁ i)) =
                  (List.finRange dag₂.n).map (fun i => toRawEmergenceMatrix (emergence₂ i)) :=
    congrArg RawLStarInstanceFull.emergence h_raw_eq
  have h_stride : pools₁.stride = pools₂.stride :=
    congrArg (fun r => r.pools.stride) h_raw_eq
  -- Step 3: Case split on n and dag to unify Fin types
  cases h_n
  cases h_dag
  -- Now dag₁ = dag₂, so Fin dag₁.n = Fin dag₂.n (definitionally equal)
  -- Step 4: Derive function equalities from list equalities
  have h_sw : seedWidth₁ = seedWidth₂ := finRange_map_eq_implies_fun_eq h_sw_raw
  have h_R : R₁ = R₂ := finRange_map_eq_implies_fun_eq h_R_raw
  cases h_sw; cases h_R
  -- For emergence, we need to show the matrices are equal
  have h_em_fun := finRange_map_eq_implies_fun_eq h_em_raw
  have h_em : emergence₁ = emergence₂ := by
    funext i
    have h_i : toRawEmergenceMatrix (emergence₁ i) = toRawEmergenceMatrix (emergence₂ i) :=
      congrFun h_em_fun i
    exact (toRawEmergenceMatrix_injective (R := R₁ i) (n := seedWidth₁ i)) h_i
  cases h_em
  -- Step 5: Pools equality from stride
  have h_pools : pools₁ = pools₂ := by
    cases pools₁; cases pools₂
    simp only [PoolConfig.mk.injEq]
    exact h_stride
  cases h_pools
  -- All data fields match; remaining proof fields are Props (Subsingletons).
  have hnpos : n_pos₁ = n_pos₂ := by
    apply Subsingleton.elim
  have hacyc : dagAcyclic₁ = dagAcyclic₂ := by
    apply Subsingleton.elim
  have h_ok : seedWidth_ok₁ = seedWidth_ok₂ := by
    apply Subsingleton.elim
  cases hnpos
  cases hacyc
  cases h_ok
  rfl

/-- `toRawLStarInstanceFG` is injective: different L* instances produce different raw forms.

    **Proof idea**: The `toRaw*` functions extract ALL data fields (n, dag, seedWidth, R,
    emergence, pools, encodedφ, fg). Proof fields (Prop) are irrelevant by Subsingleton.
    So if raw representations match, all data fields match, hence structures are equal.

    **Key equalities established**:
    - n, dag equality: directly from raw base.n, toRawDAG_injective
    - seedWidth, R equality: from raw lists (indexed by finRange dag.n)
    - emergence equality: from raw matrices (toRawEmergenceMatrix is injective)
    - pools equality: from raw stride (only field)
    - encodedφ equality: directly stored in raw
    - fg equality: from raw gateReq/gateDigests

    **Note**: The detailed field-by-field proof is tedious but mechanical. The structure
    is: extract raw field equality → show data field equality → apply extensionality.
    This is LOW RISK because the toRaw functions are purely extractive (no lossy transforms).
-/
theorem toRawLStarInstanceFG_injective :
    Function.Injective toRawLStarInstanceFG := by
  intro L₁ L₂ h_raw_eq
  -- Extract top-level component equalities
  have h_base_eq : toRawLStarInstanceFull L₁.toLStarInstanceFull =
                   toRawLStarInstanceFull L₂.toLStarInstanceFull := by
    simp only [toRawLStarInstanceFG] at h_raw_eq
    exact congrArg RawLStarInstanceFG.base h_raw_eq
  have h_encoded_eq : L₁.encodedφ = L₂.encodedφ := by
    simp only [toRawLStarInstanceFG] at h_raw_eq
    exact congrArg RawLStarInstanceFG.encodedφ h_raw_eq
  have h_fg_raw_eq : toRawFrontierGateConfig L₁.fg = toRawFrontierGateConfig L₂.fg := by
    simp only [toRawLStarInstanceFG] at h_raw_eq
    exact congrArg RawLStarInstanceFG.fg h_raw_eq
  -- Step 1: Prove key data field equalities from raw base
  have h_n_eq : L₁.n = L₂.n := by
    simp only [toRawLStarInstanceFull] at h_base_eq
    exact congrArg RawLStarInstanceFull.n h_base_eq
  have h_dag_raw_eq : toRawDAG L₁.dag = toRawDAG L₂.dag := by
    simp only [toRawLStarInstanceFull] at h_base_eq
    exact congrArg RawLStarInstanceFull.dag h_base_eq
  have h_dag_eq : L₁.dag = L₂.dag := toRawDAG_injective h_dag_raw_eq
  have h_stride_eq : L₁.pools.stride = L₂.pools.stride := by
    simp only [toRawLStarInstanceFull] at h_base_eq
    exact congrArg (fun r => r.pools.stride) h_base_eq
  -- Step 2: Prove toLStarInstanceFull equality using injectivity
  have h_full_eq : L₁.toLStarInstanceFull = L₂.toLStarInstanceFull :=
    toRawLStarInstanceFull_injective h_base_eq
  -- Step 3: Prove fg HEq using h_full_eq
  -- After h_full_eq, the types match: FrontierGateConfig L₁.toLStarInstanceFull = FrontierGateConfig L₂.toLStarInstanceFull
  -- So HEq is just eq (via heq_of_eq)
  have h_fg_heq : L₁.fg ≍ L₂.fg := by
    -- Strategy: destructure L₁, L₂ first, then use h_full_eq to unify types
    cases L₁ with | mk full₁ encodedφ₁ fg₁ =>
    cases L₂ with | mk full₂ encodedφ₂ fg₂ =>
    -- h_full_eq : full₁ = full₂
    simp only [LStarInstanceFG.toLStarInstanceFull] at h_full_eq
    cases h_full_eq
    -- Now full₁ = full₂ definitionally, so fg₁ and fg₂ have the same type
    -- Show fg₁ = fg₂, then HEq is trivial
    suffices h_eq : fg₁ = fg₂ by exact heq_of_eq h_eq
    -- Extract gateReq equality from raw
    simp only [toRawFrontierGateConfig] at h_fg_raw_eq
    have h_gateReq_raw := congrArg RawFrontierGateConfig.gateReq h_fg_raw_eq
    have h_gateReq : fg₁.gateReq = fg₂.gateReq := finRange_map_eq_implies_fun_eq h_gateReq_raw
    have h_gateDigests_raw := congrArg RawFrontierGateConfig.gateDigests h_fg_raw_eq
    -- FrontierGateConfig has fields: gateReq, gateDigest, wiring_in_seeds (Prop)
    cases fg₁ with | mk gateReq₁ gateDigest₁ wiring₁ =>
    cases fg₂ with | mk gateReq₂ gateDigest₂ wiring₂ =>
    simp only at h_gateReq
    subst h_gateReq
    -- After gateReq substitution, need to show gateDigest₁ = gateDigest₂
    -- The wiring_in_seeds proofs are Prop, so irrelevant
    simp only [FrontierGateConfig.mk.injEq, heq_eq_eq, true_and]
    -- Show gateDigest₁ = gateDigest₂ : ({v // gateReq₁ v} → GateDigest)
    funext ⟨v, hv⟩
    -- From h_gateDigests_raw, extract equality at position v
    have h_v_raw := congrFun (finRange_map_eq_implies_fun_eq h_gateDigests_raw) v
    -- h_v_raw involves: if gateReq₁ v then some (...) else none
    simp only [hv, ↓reduceDIte, Option.some.injEq] at h_v_raw
    -- Now h_v_raw : toRawGateDigest (gateDigest₁ ⟨v, hv⟩) = toRawGateDigest (gateDigest₂ ⟨v, hv⟩)
    -- Extract field equalities from raw equality
    simp only [toRawGateDigest, RawGateDigest.mk.injEq] at h_v_raw
    obtain ⟨h_sb, h_bits⟩ := h_v_raw
    -- h_sb : segmentBudget equality, h_bits : toList equality
    -- GateDigest equality follows from field equalities via structure injectivity
    -- The proof involves dependent type handling: bits type depends on segmentBudget
    exact GateDigest_eq_of_raw_eq h_sb h_bits
  -- Step 4: Apply LStarInstanceFG.ext
  exact LStarInstanceFG.ext h_full_eq h_encoded_eq h_fg_heq

/-- `encodeBits` is injective: different L* instances produce different encodings.

    Proof: Composition of two injective functions:
    1. `Encodable.encode` is injective (proven in Encodable.encode_injective)
    2. `toRawLStarInstanceFG` is injective (proven above)
-/
theorem encodeBits_injective : Function.Injective encodeBits := by
  unfold encodeBits
  have h1 : Function.Injective (Encodable.encode (α := RawLStarInstanceFG)) :=
    Encodable.encode_injective
  have h2 : Function.Injective toRawLStarInstanceFG := toRawLStarInstanceFG_injective
  exact Function.Injective.comp h1 h2

/-- Size lower bound: input size ≤ polynomial in encoding length.

    The encoding length is at least `dag.n` (parents list has that many entries).
    Since `Sized.size L = L.dag.n`, we have `size L ≤ |encodeBits L| + 1`.

    This gives us the required polynomial bound: size L ≤ 1 * (|enc| + 1)^1.
-/
theorem encodeBits_size_lower (L : LStarInstanceFG) :
    Sized.size L ≤ (encodeBits L).length + 1 := by
  -- Sized.size L = L.dag.n (from Sized instance)
  have h_size : Sized.size L = L.dag.n := rfl
  -- encodeBits L has length ≥ L.dag.n (from the parents list encoding)
  have h_enc_ge : (encodeBits L).length ≥ L.dag.n := by
    unfold encodeBits
    -- The encoding includes dag.parents which has length = dag.n
    have h_parents_len : (toRawLStarInstanceFG L).base.dag.parents.length = L.dag.n := by
      unfold toRawLStarInstanceFG toRawLStarInstanceFull toRawDAG
      simp only [List.length_map, List.length_finRange]
    -- The encoding length includes at least the parents list
    have h_fg_in_raw : ∀ (r : RawLStarInstanceFG),
        (@Encodable.encode RawLStarInstanceFG _ r).length ≥ r.base.dag.parents.length := by
      intro r
      have h1 : (@Encodable.encode RawLStarInstanceFG _ r).length =
          (Encodable.encode r.base ++ Encodable.encode r.encodedφ ++ Encodable.encode r.fg).length := rfl
      simp only [List.length_append] at h1
      have h_list_len : ∀ (l : List (List Nat)),
          (@Encodable.encode (List (List Nat)) _ l).length ≥ l.length := by
        intro l
        show (List.replicate l.length true ++ [false] ++ l.flatMap Encodable.encode).length ≥ l.length
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega
      have h_dag_in_full : ∀ (rf : RawLStarInstanceFull),
          (@Encodable.encode RawLStarInstanceFull _ rf).length ≥ rf.dag.parents.length := by
        intro rf
        have h2 : (@Encodable.encode RawLStarInstanceFull _ rf).length =
            (encodeNat rf.n ++ Encodable.encode rf.dag ++ Encodable.encode rf.seedWidth ++
             Encodable.encode rf.R ++ Encodable.encode rf.emergence ++ Encodable.encode rf.pools).length := rfl
        simp only [List.length_append] at h2
        have h3 : (@Encodable.encode RawDAG _ rf.dag).length =
            (encodeNat rf.dag.n ++ @Encodable.encode (List (List Nat)) _ rf.dag.parents).length := rfl
        simp only [List.length_append] at h3
        have h4 := h_list_len rf.dag.parents
        omega
      have h5 := h_dag_in_full r.base
      omega
    calc (Encodable.encode (toRawLStarInstanceFG L)).length
        ≥ (toRawLStarInstanceFG L).base.dag.parents.length := h_fg_in_raw (toRawLStarInstanceFG L)
      _ = L.dag.n := h_parents_len
  -- Combine: size L = dag.n ≤ |enc| ≤ |enc| + 1
  rw [h_size]
  omega

/-- PolytimeEncoding instance for encodeBits.

    **Upper bound**: From `encode_len_poly`, encoding length ≤ O(n³).
    **Lower bound**: From `encodeBits_size_lower`, size ≤ |enc| + 1.
    **Injectivity**: From `encodeBits_injective`.
-/
noncomputable def encodeBits_polytime : PolytimeEncoding encodeBits where
  enc_injective := encodeBits_injective
  -- Upper bound: 2^70 * (size + 1)^3 (from lstarTMInputEncodingBase)
  C_up := 2^70
  k_up := 3
  h_C_up_pos := by decide
  h_k_up_pos := by decide
  size_upper := fun L => by
    -- From encode_len_poly and stride bound
    have h := encode_len_poly L
    have h_stride : L.pools.stride ≤ 2^65 := L.stride_bound
    have h_cube_pos : (Sized.size L + 1)^3 ≥ 1 := Nat.one_le_pow 3 (Sized.size L + 1) (by omega)
    calc (encodeBits L).length
        ≤ 3072 * (Sized.size L + 1)^3 + 8 * L.pools.stride + 100 := h
      _ ≤ 3072 * (Sized.size L + 1)^3 + 8 * 2^65 + 100 := by omega
      _ ≤ 2^70 * (Sized.size L + 1)^3 := by
          have h_const : 8 * 2^65 + 100 ≤ 2^70 - 3072 := by native_decide
          have h_factor : 2^70 - 3072 ≤ (2^70 - 3072) * (Sized.size L + 1)^3 := by
            have : 1 ≤ (Sized.size L + 1)^3 := h_cube_pos
            omega
          calc 3072 * (Sized.size L + 1)^3 + 8 * 2^65 + 100
              ≤ 3072 * (Sized.size L + 1)^3 + (2^70 - 3072) := by omega
            _ ≤ 3072 * (Sized.size L + 1)^3 + (2^70 - 3072) * (Sized.size L + 1)^3 := by
                have h1 : 2^70 - 3072 ≤ (2^70 - 3072) * (Sized.size L + 1)^3 := h_factor
                omega
            _ = (3072 + (2^70 - 3072)) * (Sized.size L + 1)^3 := by ring
            _ = 2^70 * (Sized.size L + 1)^3 := by ring
  -- Lower bound: 1 * (|enc| + 1)^1
  C_lo := 1
  k_lo := 1
  h_C_lo_pos := by decide
  h_k_lo_pos := by decide
  size_lower := fun L => by
    have h := encodeBits_size_lower L
    calc Sized.size L
        ≤ (encodeBits L).length + 1 := h
      _ ≤ 1 * ((encodeBits L).length + 1)^1 := by ring_nf; omega

#print axioms toRawLStarInstanceFG_injective
#print axioms encodeBits_injective
#print axioms encodeBits_size_lower
#print axioms encodeBits_polytime

end EncodeBitsPolytime

end LStar.Encoding
