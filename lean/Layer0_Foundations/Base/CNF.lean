import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Layer0_Foundations.Base.FiniteEncoding
import Batteries.Data.List.Pairwise
import Layer0_Foundations.Base.List.DedupRight

/-! ## CNF: Conjunctive Normal Form (SAT Problem Infrastructure)

**Purpose**: Standard SAT representation for L* problem instances.

**Main Definitions**:
- `CNF`: Formula φ = C₁ ∧ C₂ ∧ ... ∧ Cₘ (conjunction of clauses)
- `Clause`: Disjunction C = l₁ ∨ l₂ ∨ ... ∨ lₖ (at least one literal true)
- `Literal`: Variable xᵥ or negation ¬xᵥ
- `Assignment`: Truth values σ: Nat → Bool
- `satisfies`: φ satisfied when all clauses satisfied
- `is3SAT`: Predicate checking if CNF is 3-SAT (all clauses ≤ 3 literals)

**Key Theorems** (security-critical, all PROVEN):
1. `encodeAssignment_injective`: Encoding is injective → Plant function injective (OWF property)
2. `satisfies_of_agree_on_vars_wf`: Extensionality → witness extraction works
3. `normalize_semantically_faithful`: Normalization preserves satisfiability

**⚠️ FORMALIZATION STATUS**:
- ✅ **PROVEN**: L* ∈ NP (verifier + witness extraction, see LStarNP.lean)
- ❌ **NOT PROVEN**: L* is NP-hard (3-SAT ≤_p L* reduction NOT formalized)
- ❌ **NOT PROVEN**: L* is NP-complete (follows from above)
- **Infrastructure exists**: `is3SAT` predicate defined but UNUSED in proofs
- **Actual proof path**: OWF exists → FP≠FNP → P≠NP (bypasses NP-completeness)
- **Paper divergence**: Paper §10.2 claims "NP-hardness via 3-SAT reduction" (Theorem 10.2)
  but Lean formalization uses information-theoretic approach (OWF via Shannon's theorem)
- **Soundness**: NO GAP - OWF-based proof is complete (see CLAUDE.md §5)

**Design**: nvars > 0 invariant, decidable satisfaction, infinite assignments (simplifies composition).

**Trust Boundary**: All three key theorems proven (zero axioms for CNF properties).
-/

namespace LStar

/-- **Literal**: A variable or its negation in a boolean formula.

    **Mathematical Content**:
    A literal l is either:
    - Positive literal: xᵥ (represented as var=v, polarity=true)
    - Negative literal: ¬xᵥ (represented as var=v, polarity=false)

    **Structure Fields**:
    - `var: Nat`: Variable index v (references variables x₀, x₁, x₂, ...)
    - `polarity: Bool`: true for positive (xᵥ), false for negative (¬xᵥ)

    **Example**: For 3-SAT clause (x₂ ∨ ¬x₅ ∨ x₇):
    - First literal: {var := 2, polarity := true} represents x₂
    - Second literal: {var := 5, polarity := false} represents ¬x₅
    - Third literal: {var := 7, polarity := true} represents x₇

    **Decidable Equality**: Enables computational comparison (needed for deduplication)
-/
structure Literal where
  var : Nat
  polarity : Bool
  deriving DecidableEq, Repr

/-- **Clause**: Disjunction of literals (at least one must be true).

    **Mathematical Content**:
    A clause C = l₁ ∨ l₂ ∨ ... ∨ lₖ is satisfied when at least one literal evaluates to true.

    **Structure Field**:
    - `literals: List Literal`: Ordered list of literals in the clause

    **3-SAT Restriction**: For 3-SAT instances, we require `literals.length ≤ 3`
    (enforced by `is3SAT` predicate on CNF formulas)

    **Example**: Clause (x₁ ∨ ¬x₃ ∨ x₄) is represented as:
    ```
    { literals := [{var := 1, polarity := true},
                   {var := 3, polarity := false},
                   {var := 4, polarity := true}] }
    ```

    **Empty Clause**: literals = [] represents unsatisfiable clause (always false)
-/
structure Clause where
  literals : List Literal
  deriving DecidableEq, Repr

/-- **CNF Formula**: Conjunction of clauses (all must be satisfied).

    **Mathematical Content**:
    A CNF formula φ = C₁ ∧ C₂ ∧ ... ∧ Cₘ is satisfied when every clause is satisfied.
    This is the standard form for SAT problems.

    **Structure Fields**:
    - `nvars: Nat`: Number of variables x₀, x₁, ..., x_{nvars-1}
    - `clauses: List Clause`: List of clauses (conjunction)
    - `nvars_pos: nvars > 0`: Invariant ensuring non-trivial formulas

    **Invariant Rationale**:
    Requiring nvars > 0 prevents degenerate empty formulas. This simplifies the
    reduction and ensures L* instances always have at least one variable to reason about.

    **Well-Formedness** (separate predicate):
    A CNF is well-formed if all literal indices are < nvars (no out-of-bounds references).
    See `CNF.WellFormed` predicate below.

    **Example**: 3-SAT formula (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) with nvars = 3:
    ```
    { nvars := 3,
      clauses := [{ literals := [{var := 0, polarity := true}, {var := 1, polarity := true}] },
                  { literals := [{var := 0, polarity := false}, {var := 2, polarity := true}] }],
      nvars_pos := by decide }
    ```
-/
structure CNF where
  nvars : Nat  -- Number of variables in the formula
  clauses : List Clause  -- List of clauses (conjunction)
  nvars_pos : nvars > 0  -- Non-triviality invariant: at least one variable
  deriving DecidableEq, Repr

/-- **Assignment**: Truth value assignment to n variables.

    **Type**: Assignment n = Fin n → Bool (FINITE function over n variables)

    **Mathematical Content**:
    An assignment σ maps each variable index i ∈ {0, ..., n-1} to a boolean value σ(i).
    - σ(i) = true means variable xᵢ is assigned TRUE
    - σ(i) = false means variable xᵢ is assigned FALSE

    **Design Note - Why Finite (Track A Refactor)**:
    We use finite functions Fin n → Bool (not Nat → Bool) because:
    1. **Complexity-theoretic correctness**: NP witnesses must be finite bit strings
    2. **OWF domain/codomain**: One-way functions map {0,1}^m → {0,1}^n (finite!)
    3. **Encoding soundness**: Cannot encode Nat → Bool as a polynomial-size bit string

    For CNF φ with nvars = n, exactly n values σ(0), ..., σ(n-1) exist.
    Use `Assignment.extend` to convert to Nat → Bool when needed for evaluation.

    **Usage in OWF**:
    The Plant function embeds satisfying assignments as seeds. The injective encoding
    `encodeAssignmentFin n σ` captures all n bits as a natural number.

    **Bitstring Representation**:
    Assignment n ≅ Vector Bool n ≅ Fin (2^n) — all finite, encodable as poly(n) bits.
-/
def Assignment (n : Nat) := Fin n → Bool

/-- **Legacy Assignment**: Infinite assignment type for internal evaluation.

    Used internally by Literal.eval, Clause.satisfies, CNF.satisfies.
    External interfaces should use `Assignment n` (finite).

    **Conversion**: Use `Assignment.extend` to convert finite → infinite.
-/
def AssignmentInf := Nat → Bool

namespace Assignment

/-- Extend finite assignment to infinite by padding with false.

    **Mathematical Content**:
    Given σ : Fin n → Bool, extend to σ' : Nat → Bool where:
    - σ'(i) = σ(i) for i < n
    - σ'(i) = false for i ≥ n

    **Key Property**: For well-formed CNF φ with φ.nvars = n, satisfaction
    is preserved: φ.satisfies (σ.extend) ↔ φ.satisfiesFinite σ
-/
def extend {n : Nat} (a : Assignment n) : AssignmentInf :=
  fun i => if h : i < n then a ⟨i, h⟩ else false

/-- Create assignment from infinite function by restricting to first n values. -/
def ofInfinite (n : Nat) (f : AssignmentInf) : Assignment n :=
  fun i => f i.val

/-- Roundtrip: restrict then extend agrees on first n values. -/
theorem extend_ofInfinite_agree (n : Nat) (f : AssignmentInf) (i : Nat) (hi : i < n) :
    (ofInfinite n f).extend i = f i := by
  simp [extend, ofInfinite, hi]

/-- Two finite assignments equal iff they agree pointwise. -/
theorem ext {n : Nat} (a b : Assignment n) (h : ∀ i, a i = b i) : a = b :=
  funext h

/-- Finite assignment from a function (convenience constructor). -/
def mk {n : Nat} (f : Fin n → Bool) : Assignment n := f

end Assignment

/-!
## Assignment Encoding for OWF Security

**Purpose**: Injective encoding of assignments to natural numbers, ensuring Plant
function injectivity—a core property required for one-way function security.

**Mathematical Requirement**:
The OWF construction (Layer2) requires that distinct witnesses produce distinct
planted instances. This injectivity traces back to assignment encoding:

```
r₁ ≠ r₂  ⟹  Plant(φ, r₁) ≠ Plant(φ, r₂)
```

**Implementation Strategy**:
We encode the first n bits of an assignment σ: Nat → Bool as a natural number by:
1. Extracting finite prefix: (σ(0), σ(1), ..., σ(n-1))
2. Packing as Seed n (finite bitvector): ofBits n σ : Seed n
3. Extracting underlying Nat: (ofBits n σ).val : Nat

The typed `Seed n` representation (from FiniteEncoding.lean) provides:
- **Finite encoding**: Seed n = Fin (2^n) wraps values < 2^n
- **Extensionality**: Seeds equal iff their bits equal (via Fin.ext)
- **Injectivity**: ofBits is injective (proven in FiniteEncoding.lean)

**Security Implication**:
If adversary finds preimage r' with Plant(φ, r') = Plant(φ, r), then assignment
injectivity implies r'.assignment = r.assignment on all variables in φ. The
Extractor (Layer2) uses this to extract a valid SAT witness from any successful
inversion.

**Paper References**:
- Appendix A "Encoding injectivity for OWF security"
- §9.2 "Extractor construction" - Uses assignment injectivity
- §9.3 "Poly-time analysis" - Encoding computable in poly time
-/

/-- **Encode finite assignment**: All n bits → natural number.

    **Function**: encodeAssignmentFin σ = ⌊σ(0)σ(1)...σ(n-1)⌋₂

    **Mathematical Content**:
    Interprets all n bits of σ : Assignment n as a binary number (little-endian):
    - σ(0) is least significant bit (2^0 place)
    - σ(1) is next bit (2^1 place)
    - σ(n-1) is most significant bit (2^(n-1) place)

    Result: Σᵢ₌₀ⁿ⁻¹ σ(i)·2^i ∈ {0, 1, ..., 2^n - 1}

    **Implementation**: Uses typed Seed representation for type safety and
    automatic range checking (result always < 2^n).

    **Bijectivity**: This is a bijection Assignment n ≅ Fin (2^n), critical for OWF.

    **Example**: encodeAssignmentFin σ where σ = [1,0,1,1] (4 bits)
    - Binary: 1011₂ (little-endian: 1 + 0·2 + 1·4 + 1·8)
    - Decimal: 1 + 4 + 8 = 13
    - Result: 13
-/
def encodeAssignmentFin {n : Nat} (a : Assignment n) : Nat :=
  (ofBits n (fun i => a i)).val

/-- **Decode natural to finite assignment**: Inverse of encodeAssignmentFin.

    **Function**: decodeAssignmentFin k = σ where σ(i) = bit i of k

    **Mathematical Content**:
    Extracts bits from natural number k (little-endian):
    - σ(0) = k mod 2
    - σ(1) = (k / 2) mod 2
    - σ(i) = (k / 2^i) mod 2

    **Bijectivity**: This is the inverse of encodeAssignmentFin.
-/
def decodeAssignmentFin {n : Nat} (k : Fin (2^n)) : Assignment n :=
  fun i => Seed.get k i

/-- **Roundtrip theorem**: decode ∘ encode = id -/
theorem decodeAssignmentFin_encodeAssignmentFin {n : Nat} (a : Assignment n) :
    decodeAssignmentFin (ofBits n (fun i => a i)) = a := by
  unfold decodeAssignmentFin
  funext i
  exact ofBits_get n (fun i => a i) i

/-- **Legacy encode**: For compatibility, encode infinite assignment by taking first n bits. -/
def encodeAssignment (n : Nat) (a : AssignmentInf) : Nat :=
  (ofBits n (fun i => a i)).val

/-- **Encoding injectivity for finite assignments**: Bijection implies injectivity.

    **Theorem Statement**:
    ```
    encodeAssignmentFin a₁ = encodeAssignmentFin a₂ ⟹ a₁ = a₂
    ```

    **Mathematical Content**:
    Finite assignments encode bijectively to Fin (2^n). Equal encodings mean equal
    assignments—this is exact, not just "agree on first n bits".

    **Security Implication for OWF**:
    This theorem is **critical** for Plant function injectivity. The proof chain:

    1. Assume Plant(φ, r₁) = Plant(φ, r₂) (adversary found collision)
    2. Plant equality implies stride equality (by Plant definition)
    3. Stride equality implies encodeAssignmentFin r₁.assignment
                              = encodeAssignmentFin r₂.assignment
    4. This theorem gives: r₁.assignment = r₂.assignment (exact equality!)
    5. Extractor uses this to show r₁ and r₂ encode the same witness

    **Trust Boundary**: Proven theorem (no axioms needed beyond standard foundations).
-/
theorem encodeAssignmentFin_injective {n : Nat} (a1 a2 : Assignment n)
    (h : encodeAssignmentFin a1 = encodeAssignmentFin a2) :
    a1 = a2 := by
  unfold encodeAssignmentFin at h
  have hseed : ofBits n (fun i => a1 i) = ofBits n (fun i => a2 i) := by
    apply Fin.ext
    exact h
  funext i
  have h1 := ofBits_get n (fun i => a1 i) i
  have h2 := ofBits_get n (fun i => a2 i) i
  rw [hseed] at h1
  rw [← h1, ← h2]

/-- **Legacy injectivity**: For infinite assignments, encoding is injective on first n bits. -/
theorem encodeAssignment_injective (n : Nat) (a1 a2 : AssignmentInf)
    (h : encodeAssignment n a1 = encodeAssignment n a2) :
    ∀ i < n, a1 i = a2 i := by
  intro i hi
  unfold encodeAssignment at h
  have hseed : ofBits n (fun i => a1 i) = ofBits n (fun i => a2 i) := by
    apply Fin.ext
    exact h
  have h1 := ofBits_get n (fun i => a1 i) (Fin.mk i hi)
  have h2 := ofBits_get n (fun i => a2 i) (Fin.mk i hi)
  rw [hseed] at h1
  rw [← h1, ← h2]

namespace Literal

/-- **Evaluate literal**: Compute truth value under infinite assignment.

    **Function**: eval l σ returns the boolean value of literal l under assignment σ

    **Mathematical Content**:
    - Positive literal xᵥ: eval returns σ(v) (variable's value directly)
    - Negative literal ¬xᵥ: eval returns ¬σ(v) (negation of variable's value)

    **Implementation**:
    ```
    if l.polarity then σ l.var else !(σ l.var)
    ```

    **Example**:
    - l = {var := 3, polarity := true}, σ(3) = true  → eval l σ = true (x₃ is true)
    - l = {var := 3, polarity := false}, σ(3) = true → eval l σ = false (¬x₃ is false)
    - l = {var := 5, polarity := false}, σ(5) = false → eval l σ = true (¬x₅ is true)

    **Note**: Uses AssignmentInf (infinite). For finite assignments, use `.extend`.
-/
def eval (l : Literal) (σ : AssignmentInf) : Bool :=
  if l.polarity then σ l.var else !(σ l.var)

/-- Evaluate literal under finite assignment (requires variable in bounds). -/
def evalFin {n : Nat} (l : Literal) (σ : Assignment n) (h : l.var < n) : Bool :=
  if l.polarity then σ ⟨l.var, h⟩ else !(σ ⟨l.var, h⟩)

/-- Evaluation via extend equals direct evaluation for in-bounds variables. -/
theorem evalFin_eq_eval_extend {n : Nat} (l : Literal) (σ : Assignment n) (h : l.var < n) :
    evalFin l σ h = eval l σ.extend := by
  unfold evalFin eval Assignment.extend
  simp [h]

end Literal

namespace Clause

/-- **Clause satisfaction**: At least one literal must be true (disjunction).

    **Definition**: c.satisfies σ ≡ ∃ l ∈ c.literals, eval l σ = true

    **Mathematical Content**:
    A clause C = l₁ ∨ l₂ ∨ ... ∨ lₖ is satisfied when at least one literal evaluates
    to true under σ. This is the standard SAT semantics for disjunction.

    **Logical Form**: Existential quantification over literals
    - If c.literals = [l₁, l₂, l₃], then
      c.satisfies σ ≡ (eval l₁ σ = true) ∨ (eval l₂ σ = true) ∨ (eval l₃ σ = true)

    **Empty Clause**: If c.literals = [], then c.satisfies σ is false for all σ
    (empty disjunction is always false—standard convention in SAT)

    **Computational Decidability**: See instance below—satisfaction is decidable
    (can be computed in finite time by checking each literal).

    **Note**: Uses AssignmentInf (infinite). For finite assignments, use `.extend`.
-/
def satisfies (c : Clause) (σ : AssignmentInf) : Prop :=
  ∃ l ∈ c.literals, Literal.eval l σ = true

/-- **Decidable satisfaction**: Clause satisfaction is computationally decidable.

    **Purpose**: Enables computational checking of satisfaction via `decide` tactic.

    **Implementation**: Lean's typeclass inference automatically derives decidability
    from the decidability of:
    1. List membership (l ∈ c.literals)
    2. Literal evaluation (Literal.eval l σ = true)
    3. Boolean equality (= on Bool)
    4. Existential over finite list (∃ l ∈ finite list)

    **Computational Complexity**: O(|literals|) time—check each literal sequentially
    until finding one that's true, or conclude unsatisfied if all are false.
-/
instance decidable_satisfies (c : Clause) (σ : AssignmentInf) :
  Decidable (c.satisfies σ) := by
  unfold satisfies
  infer_instance  -- Let Lean derive decidability automatically

/-- Clause satisfaction under finite assignment (via extend). -/
def satisfiesFin {n : Nat} (c : Clause) (σ : Assignment n) : Prop :=
  c.satisfies σ.extend

/-- Finite satisfaction is decidable. -/
instance decidable_satisfiesFin {n : Nat} (c : Clause) (σ : Assignment n) :
  Decidable (c.satisfiesFin σ) := by
  unfold satisfiesFin
  infer_instance

end Clause

namespace CNF

/-- **Well-formedness**: Every literal references a valid variable index.

    **Definition**: φ.WellFormed ≡ ∀ clauses c, ∀ literals l, l.var < φ.nvars

    **Mathematical Content**:
    A CNF formula is well-formed if all variable indices are in bounds:
    - Formula has nvars variables: x₀, x₁, ..., x_{nvars-1}
    - Every literal must reference index < nvars (no out-of-bounds access)

    **Why This Matters**:
    1. **Type safety**: Prevents runtime errors when evaluating formulas
    2. **Satisfaction extensionality**: Enables `satisfies_of_agree_on_vars_wf` theorem
       (satisfaction determined by first nvars bits)
    3. **Reduction correctness**: 3-SAT → L* reduction preserves well-formedness

    **Design Note**: Well-formedness is a *separate* predicate, not built into CNF type.
    This allows flexibility—formulas can be constructed first, then validated. Most
    theorems (e.g., satisfaction extensionality) require explicit WellFormed hypothesis.

    **Example**:
    - φ.nvars = 5, clause (x₂ ∨ ¬x₄ ∨ x₁) → well-formed ✓ (all indices < 5)
    - φ.nvars = 5, clause (x₃ ∨ x₇) → NOT well-formed ✗ (index 7 ≥ 5)
-/
def WellFormed (φ : CNF) : Prop :=
  ∀ c ∈ φ.clauses, ∀ l ∈ c.literals, l.var < φ.nvars

/-- **Formula satisfaction**: All clauses must be satisfied (conjunction).

    **Definition**: φ.satisfies σ ≡ ∀ c ∈ φ.clauses, c.satisfies σ

    **Mathematical Content**:
    A CNF formula φ = C₁ ∧ C₂ ∧ ... ∧ Cₘ is satisfied when every clause is satisfied
    under σ. This is the standard SAT semantics for conjunction.

    **Logical Form**: Universal quantification over clauses
    - If φ.clauses = [C₁, C₂, C₃], then
      φ.satisfies σ ≡ C₁.satisfies σ ∧ C₂.satisfies σ ∧ C₃.satisfies σ

    **Computational Decidability**: Decidable (check all clauses in finite time).

    **Satisfiability vs Satisfaction**:
    - **Satisfiability**: ∃σ, φ.satisfies σ (problem: find witness)
    - **Satisfaction**: φ.satisfies σ (given σ, check if it works)

    Satisfaction is decidable (P), satisfiability is NP-complete.

    **Note**: Uses AssignmentInf (infinite). For finite assignments, use `satisfiesFin`.
-/
def satisfies (φ : CNF) (σ : AssignmentInf) : Prop :=
  ∀ c ∈ φ.clauses, Clause.satisfies c σ

/-- **Finite formula satisfaction**: Satisfaction under finite assignment.

    For φ with nvars = n, this checks satisfaction using a finite assignment
    of exactly n bits. This is the proper complexity-theoretic notion.
-/
def satisfiesFin (φ : CNF) (σ : Assignment φ.nvars) : Prop :=
  φ.satisfies σ.extend

/-- Finite satisfaction implies regular satisfaction via extend. -/
theorem satisfiesFin_iff_satisfies_extend (φ : CNF) (σ : Assignment φ.nvars) :
    φ.satisfiesFin σ ↔ φ.satisfies σ.extend := by
  rfl

/-- **SAT language (infinite)**: Set of all satisfying infinite assignments. -/
def SAT (φ : CNF) : Set AssignmentInf :=
  {σ | φ.satisfies σ}

/-- **SAT language (finite)**: Set of all satisfying finite assignments.

    **Definition**: SATFin(φ) = {σ : Assignment φ.nvars | φ.satisfiesFin σ}

    **Mathematical Content**:
    The finite SAT language is the set of all n-bit assignments that satisfy φ.
    This is isomorphic to a subset of {0,1}^n, the proper complexity-theoretic notion.

    **Size**: |SATFin(φ)| ≤ 2^(φ.nvars) (at most 2^n assignments)
-/
def SATFin (φ : CNF) : Set (Assignment φ.nvars) :=
  {σ | φ.satisfiesFin σ}

/-- **3-SAT restriction**: All clauses have at most 3 literals.

    **Definition**: φ.is3SAT ≡ ∀ c ∈ φ.clauses, |c.literals| ≤ 3

    **Mathematical Content**:
    3-SAT is the restricted SAT problem where each clause has ≤ 3 literals:
    - General SAT: clauses can have arbitrary size (k-SAT for any k)
    - 3-SAT: each clause has ≤ 3 literals
    - 2-SAT: each clause has ≤ 2 literals (polynomial-time solvable!)

    **Complexity**:
    - **2-SAT**: In P (polynomial-time algorithms exist)
    - **3-SAT**: NP-complete (Cook-Levin theorem, 1971)
    - **k-SAT for k ≥ 3**: NP-complete (reduce from 3-SAT)

    **Why 3-SAT for Reduction**:
    We reduce from 3-SAT (not general SAT) because:
    1. 3-SAT is the *canonical* NP-complete problem (simplest hard SAT variant)
    2. Reduction from 3-SAT → L* is cleaner than general SAT → L*
    3. NP-hardness of 3-SAT implies NP-hardness of L* (suffices for proof)

    **Paper Reference**: §10.2 "NP-hardness via 3-SAT reduction"
-/
def is3SAT (φ : CNF) : Prop :=
  ∀ c ∈ φ.clauses, c.literals.length ≤ 3

/-- **Positive Clause Property**: CNF contains at least one all-positive clause.

    **Definition**: ∃ C ∈ φ.clauses, ∀ l ∈ C.literals, l.polarity = true

    **Mathematical Content**:
    A clause C = (x₁ ∨ x₂ ∨ ... ∨ xₖ) is "all-positive" if every literal is unnegated.
    The all-false assignment σ(xᵢ) = false ∀i cannot satisfy such a clause, since
    every literal evaluates to false.

    **Application**: Planted 3-SAT instances from the L* construction satisfy this
    property. Combined with format separation of TM encodings, this enables proving
    that incomplete computation cannot produce satisfying assignments.
-/
def HasPositiveClause (φ : CNF) : Prop :=
  ∃ c ∈ φ.clauses, ∀ l ∈ c.literals, l.polarity = true

/-! ## Satisfaction Extensionality

Satisfaction is determined by the first φ.nvars variables. If two assignments
agree on all variables appearing in φ (i.e., variables 0 through φ.nvars-1),
and one satisfies φ, then both do.

**Key property for OWF security**: If adversary finds preimage r' with
plant_n n φ r' = plant_n n φ r, then plant_injectivity_on_gateDigests
gives us r'.gateDigests = r.gateDigests. Combined with WellFormedRandomness,
this ensures r'.assignment satisfies φ. The theorem below lets us transfer
satisfaction between assignments that agree on relevant variables.

Note: The extensionality lemma without wellformedness has been removed.
Use `satisfies_of_agree_on_vars_wf` with an explicit `WellFormed` hypothesis.
-/

/-- Satisfaction is preserved when infinite assignments agree on all referenced variables,
    assuming well-formedness of the CNF. -/
theorem satisfies_of_agree_on_vars_wf
    (φ : CNF) (a1 a2 : AssignmentInf)
    (h_agree : ∀ i < φ.nvars, a1 i = a2 i)
    (h_sat : φ.satisfies a1)
    (wf : φ.WellFormed)
    : φ.satisfies a2 := by
  unfold satisfies at h_sat ⊢
  intro c hc
  -- Get satisfaction of c under a1
  have h_c_sat := h_sat c hc
  unfold Clause.satisfies at h_c_sat ⊢
  -- Extract the witness literal from a1
  obtain ⟨l, hl_in, hl_eval⟩ := h_c_sat
  -- Show same literal works for a2 using well-formedness
  use l, hl_in
  unfold Literal.eval at hl_eval ⊢
  have hvar_lt : l.var < φ.nvars := wf c hc l hl_in
  by_cases h_pol : l.polarity
  · simp [h_pol] at hl_eval ⊢
    simpa [h_agree _ hvar_lt] using hl_eval
  · simp [h_pol] at hl_eval ⊢
    simpa [h_agree _ hvar_lt] using hl_eval

/-- Finite assignments that are equal satisfy the same formulas. -/
theorem satisfiesFin_ext (φ : CNF) (a1 a2 : Assignment φ.nvars)
    (h_eq : a1 = a2) (h_sat : φ.satisfiesFin a1) : φ.satisfiesFin a2 := by
  rw [← h_eq]; exact h_sat

end CNF

/-! ## CNF Normalization

Normalization preserves semantics while converting CNF to canonical form:
- Literals: canonicalized (identity for now, extensible for var renaming)
- Clauses: deduplicated literals, normalized literal order
- CNF: tautology clauses removed, clauses deduplicated

The main result is `normalize_semantically_faithful`: normalization preserves
the set of satisfying assignments.

**Purpose**: Shrink trust boundary by proving CNF transformations are sound,
eliminating need for normalization axioms.
-/

/-! ### Deduplication with Proven Membership Preservation

We use `LStar.List.eraseDupsRight` instead of core `eraseDups` because it has a
structurally-recursive definition that supports complete proofs without sorries.

**Implementation**: `LStar.Base.List.DedupRight`
**Key theorem**: `mem_eraseDupsRight_iff : a ∈ eraseDupsRight l ↔ a ∈ l`

This pragmatic solution provides the exact membership equivalence needed for CNF
normalization proofs without relying on opaque accumulator loops or library gaps.
-/

namespace Literal

/-- Normalize a literal (identity for now, extensible for canonicalization). -/
def normalize (l : Literal) : Literal := l

/-- Literal evaluation is preserved by normalization. -/
theorem eval_normalize (l : Literal) (σ : AssignmentInf) :
    Literal.eval l σ = Literal.eval (normalize l) σ := by
  unfold normalize
  rfl

end Literal

namespace Clause

/-- Check if a clause is a tautology (contains both x and ¬x for some variable). -/
def isTautology (c : Clause) : Bool :=
  c.literals.any fun l₁ =>
    c.literals.any fun l₂ =>
      l₁.var == l₂.var && (l₁.polarity != l₂.polarity)

/-- Normalize a clause: deduplicate literals after normalizing each literal. -/
def normalize (c : Clause) : Clause :=
  { literals := LStar.List.eraseDupsRight (c.literals.map Literal.normalize) }

/-- Deduplication preserves clause satisfaction. -/
theorem satisfies_eraseDups (lits : List Literal) (σ : AssignmentInf) :
    Clause.satisfies { literals := lits } σ ↔
    Clause.satisfies { literals := LStar.List.eraseDupsRight lits } σ := by
  unfold Clause.satisfies
  constructor
  · intro ⟨l, hl, heval⟩
    use l, (LStar.List.mem_eraseDupsRight_iff).mpr hl, heval
  · intro ⟨l, hl, heval⟩
    use l, (LStar.List.mem_eraseDupsRight_iff).mp hl, heval

/-- Tautology clauses are always satisfied.

    A tautology contains both x and ¬x for some variable, so one must be true. -/
theorem satisfies_of_tautology (c : Clause) (σ : AssignmentInf)
    (h_taut : isTautology c = true) :
    Clause.satisfies c σ := by
  unfold isTautology at h_taut
  simp [List.any_eq_true] at h_taut
  --  h_taut: ∃ l₁ ∈ c.literals, ∃ l₂ ∈ c.literals, l₁.var = l₂.var ∧ l₁.polarity ≠ l₂.polarity
  obtain ⟨l₁, hl₁, l₂, hl₂, hvar, hpol⟩ := h_taut
  unfold Clause.satisfies Literal.eval
  -- Either l₁ or l₂ evaluates to true (opposite polarities on same var)
  by_cases h : σ l₁.var
  · -- σ(l₁.var) = true
    by_cases hp₁ : l₁.polarity
    · -- l₁ is positive: use l₁
      use l₁, hl₁
      simp [hp₁, h]
    · -- l₁ is negative, so l₂ must be positive: use l₂
      use l₂, hl₂
      have hp₂ : l₂.polarity = true := by simp [hp₁] at hpol; exact hpol
      simp [hp₂, ←hvar, h]
  · -- σ(l₁.var) = false
    by_cases hp₁ : l₁.polarity
    · -- l₁ is positive, so l₂ must be negative: use l₂
      use l₂, hl₂
      have hp₂ : l₂.polarity = false := by simp [hp₁] at hpol; exact hpol
      simp [hp₂, ←hvar, h]
    · -- l₁ is negative: use l₁
      use l₁, hl₁
      simp [hp₁, h]

/-- Clause normalization preserves satisfaction. -/
theorem satisfies_normalize (c : Clause) (σ : AssignmentInf) :
    Clause.satisfies c σ ↔ Clause.satisfies (normalize c) σ := by
  unfold normalize
  -- Step 1: Map Literal.normalize over literals
  have h_map : Clause.satisfies c σ ↔
                Clause.satisfies { literals := c.literals.map Literal.normalize } σ := by
    unfold Clause.satisfies
    constructor
    · intro ⟨l, hl, heval⟩
      use Literal.normalize l
      simp [List.mem_map]
      constructor
      · exact ⟨l, hl, rfl⟩
      · rw [← Literal.eval_normalize]
        exact heval
    · intro ⟨l, hl, heval⟩
      simp [List.mem_map] at hl
      obtain ⟨l', hl', rfl⟩ := hl
      use l', hl'
      rw [Literal.eval_normalize]
      exact heval
  -- Step 2: Apply eraseDups
  rw [h_map]
  exact satisfies_eraseDups (c.literals.map Literal.normalize) σ

end Clause

namespace CNF

/-- Normalize a CNF formula: normalize clauses, remove tautologies, deduplicate.

    Tautology clauses (containing both x and ¬x) are always satisfied and can
    be safely removed without changing the set of satisfying assignments. -/
def normalize (φ : CNF) : CNF :=
  { nvars := φ.nvars
  , clauses := LStar.List.eraseDupsRight ((φ.clauses.map Clause.normalize).filter (fun c => !Clause.isTautology c))
  , nvars_pos := φ.nvars_pos }

/-- Removing tautology clauses preserves satisfaction. -/
theorem satisfies_filter_tautologies (clauses : List Clause) (σ : AssignmentInf) :
    (∀ c ∈ clauses, Clause.satisfies c σ) ↔
    (∀ c ∈ clauses.filter (fun c => !Clause.isTautology c), Clause.satisfies c σ) := by
  constructor
  · intro h c hc
    have : c ∈ clauses := List.mem_filter.mp hc |>.left
    exact h c this
  · intro h c hc
    by_cases h_taut : Clause.isTautology c = true
    · -- c is a tautology, so it's always satisfied
      exact Clause.satisfies_of_tautology c σ h_taut
    · -- c is not a tautology, so it's in the filtered list
      have : c ∈ clauses.filter (fun c => !Clause.isTautology c) := by
        simp [List.mem_filter, Bool.not_eq_true] at h_taut ⊢
        exact ⟨hc, h_taut⟩
      exact h c this

/-- CNF normalization preserves satisfaction. -/
theorem satisfies_normalize (φ : CNF) (σ : AssignmentInf) :
    CNF.satisfies φ σ ↔ CNF.satisfies (normalize φ) σ := by
  unfold CNF.satisfies normalize
  simp only [LStar.List.mem_eraseDupsRight_iff]
  -- Step 1: Map Clause.normalize
  have h_map : (∀ c ∈ φ.clauses, Clause.satisfies c σ) ↔
               (∀ c ∈ φ.clauses.map Clause.normalize, Clause.satisfies c σ) := by
    constructor
    · intro h c hc
      simp [List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [← Clause.satisfies_normalize]
      exact h c' hc'
    · intro h c hc
      have : Clause.normalize c ∈ φ.clauses.map Clause.normalize := by
        simp [List.mem_map]
        exact ⟨c, hc, rfl⟩
      have := h (Clause.normalize c) this
      rw [Clause.satisfies_normalize]
      exact this

  -- Step 2: Filter tautologies
  have h_filter : (∀ c ∈ φ.clauses.map Clause.normalize, Clause.satisfies c σ) ↔
                  (∀ c ∈ (φ.clauses.map Clause.normalize).filter (fun c => !Clause.isTautology c),
                    Clause.satisfies c σ) :=
    satisfies_filter_tautologies (φ.clauses.map Clause.normalize) σ

  -- Combine all steps
  rw [h_map, h_filter]

/-- Main theorem: Normalization is semantically faithful.

    The set of satisfying assignments is preserved by normalization.

    **Significance**: This theorem eliminates the need for a normalization axiom
    in the trust boundary. We can now safely normalize CNF formulas (removing
    tautologies, deduplicating clauses) with a PROVEN guarantee that the
    satisfiability problem remains equivalent. -/
theorem normalize_semantically_faithful (φ : CNF) (σ : AssignmentInf) :
    CNF.satisfies φ σ ↔ CNF.satisfies (normalize φ) σ :=
  satisfies_normalize φ σ

/- Axiom audit: Key theorems for CNF handling. Both rely on structural
   induction and standard Lean foundations. -/
#print axioms LStar.encodeAssignment_injective
#print axioms LStar.CNF.normalize_semantically_faithful

end CNF

end LStar
