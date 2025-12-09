import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log

/-! ## Nat.log Helper Lemmas

These lemmas compute Nat.log for small constants without using `native_decide`,
avoiding sorryAx in axiom traces. -/

/-- Nat.log 2 4 = 2 (proven without native_decide). -/
theorem Nat.log_two_four_eq_two : Nat.log 2 4 = 2 := by
  have : 4 = 2^2 := by decide
  rw [this]
  exact Nat.log_pow (by decide : 1 < 2) 2

/-- Nat.log 2 128 = 7 (proven without native_decide). -/
theorem Nat.log_two_128_eq_seven : Nat.log 2 128 = 7 := by
  have : 128 = 2^7 := by decide
  rw [this]
  exact Nat.log_pow (by decide : 1 < 2) 7

/-! ## BoundedSecurityParam: Type-Encoded Security Parameter Bounds

**Purpose**: Security parameters with type-level domain constraints (axiom elimination).

**Main Definition**:
```lean
def SecurityParam (k : Nat) := {n : Nat // k ≤ n}  -- n ≥ k encoded in type
```

**Axiom Elimination**: Type encoding replaces axiomatic domain bounds.
```
Naive: axiom domain_bound : ∀n, n ≥ k → property  (axiom!)
Better: theorem property (n : SecurityParam k) : ...  (proven, k ≤ n automatic!)
```

**Benefits**:
- Trust boundary: Eliminates 2+ domain axioms
- Type safety: Cannot use n < k (type system prevents)
- Ergonomics: `(n : SecurityParam 128)` cleaner than `(n : Nat) (h : n ≥ 128)`

**Key Theorem**: `lambdaBaseSize_ge_generic` - (log₂ n)² ≥ (log₂ k)² for n ≥ k (PROVEN).

**Applications**: OWF families indexed by SecurityParam (ensures minimum security level).

**Paper**: §5 "Security parameter families".
- k=256: λ_base ≥ (log₂ 256)² = 8² = 64 (post-quantum security parameter)

**Why Crucial for QP-Sharp Profile**:
The quasi-polynomial time bound n^{Ω(log n)} (Theorem 8.A) requires λ = Θ(log² n).
This theorem establishes the minimum λ_base that enables this scaling:
```
λ_base = (log₂ n)² → bound 2^{λ_base} = 2^{(log₂ n)²} = n^{log₂ n}  (quasi-polynomial)
```

**Proof Technique**:
Pure monotonicity via Mathlib lemmas—no custom axioms:
1. n ≥ k (from SecurityParam k constraint)
2. log₂ n ≥ log₂ k (log is monotone: Nat.log_mono_right)
3. (log₂ n)² ≥ (log₂ k)² (squaring is monotone: Nat.pow_le_pow_left)

**Paper References**:
- §3 "Parametric Complexity Spectrum" - Security parameter families k → L*(φ, k)
- §1.2.1 "QP-sharp profile" - λ = Θ(log² n) residual enables n^{Ω(log n)} bound
- §8.A "Per-instance Deterministic Bounds" - λ_base = (log₂ n)² formula
- Theorem 8.A "Quasi-polynomial time bound" - n^{Ω(log n)} from λ = Θ(log² n)

**Dependencies**:
- Mathlib.Data.Nat.Log: Natural logarithm and monotonicity lemmas

**Applications in Proof Chain**:
- **Layer 2 (PlantCore.lean)**: Uses SecurityParam 128 for QP-sharp OWF construction
- **Layer 2 (PlantExponential.lean)**: Does NOT use—exponential profile uses unrestricted Nat
- **Layer 3 (Information Bounds)**: λ_base = (log₂ n)² formula appears in residual calculations
- **Layer 4 (Operational)**: QP time bound n^{log n} traces back to this quadratic λ

**Design Note - Profile Specificity**:
This module is SPECIFIC to the quasi-polynomial profile. The exponential profile (R_v = n)
doesn't need bounded security parameters—it works for all n ∈ ℕ. This demonstrates the
formalization's support for DUAL PROFILES with different parameter requirements.
-/

namespace LStar.Base

/-- **SecurityParam**: Parametric security parameter with type-level lower bound.

    **Type Definition**: SecurityParam k = {n : Nat // k ≤ n}

    **Mathematical Content**:
    Elements of SecurityParam k are natural numbers n with proof that n ≥ k. The constraint
    is encoded in the type, making domain violations impossible (type system rejects them).

    **Type-Level Encoding Benefits**:
    - **Automatic bounds**: Every `n : SecurityParam k` automatically satisfies `n.val ≥ k`
    - **Type safety**: Cannot accidentally pass n < k (Lean type checker prevents it)
    - **Clean API**: `(n : SecurityParam 128)` instead of `(n : Nat) (h : n ≥ 128)`
    - **Proof automation**: Bound available via `n.property` (automatic subtype projection)

    **Standard Instantiations**:
    - `SecurityParam 64`: n ∈ [64, ∞) (minimal practical security)
    - `SecurityParam 128`: n ∈ [128, ∞) (standard 128-bit security parameter)
    - `SecurityParam 256`: n ∈ [256, ∞) (post-quantum security parameter)

    **Usage in L* Construction**:
    PlantCore.lean uses SecurityParam 128 to enforce minimum security level for quasi-polynomial
    OWF construction. This eliminates domain axioms—bound enforcement is definitional.
-/
def SecurityParam (k : Nat) : Type := { n : Nat // k ≤ n }

namespace SecurityParam

variable {k : Nat}

/-- **Lower bound property**: Every security parameter n satisfies n ≥ k.

    **Theorem**: n.val ≥ k (automatic from subtype definition)

    **Purpose**: Exposes the type-level constraint as an explicit theorem for use in proofs.
    This is definitional (just projects the .property field), not a proven property.
-/
theorem ge_k (n : SecurityParam k) : k ≤ n.val := n.property

/-- **Positivity**: Security parameters are positive when k > 0.

    **Theorem**: k > 0 → n.val > 0

    **Proof**: Transitivity of inequalities (0 < k ≤ n.val → 0 < n.val).

    **Use case**: Ensures division by n or log n is well-defined when k > 0.
-/
theorem pos (n : SecurityParam k) (h_k_pos : 0 < k) : 0 < n.val :=
  Nat.lt_of_lt_of_le h_k_pos (ge_k n)

/-- **Constructor**: Build SecurityParam k from n and proof of k ≤ n.

    **Function**: mk n h creates element of SecurityParam k

    **Use case**: Explicit construction when n and bound proof are available.
-/
def mk (n : Nat) (h_lo : k ≤ n) : SecurityParam k := ⟨n, h_lo⟩

/-- **Decidability**: Domain membership k ≤ n is decidable (computable in finite time).

    **Purpose**: Enables computational checking whether n ∈ SecurityParam k.

    **Implementation**: Uses Nat.decLe from Mathlib (decidable ≤ on naturals).
-/
instance (n : Nat) : Decidable (k ≤ n) := Nat.decLe k n

/-- **Quadratic lower bound on λ_base**: Minimum residual complexity for QP-sharp profile.

    **Theorem Statement**:
    ```lean
    k ≥ 2 → n ∈ SecurityParam k → (log₂ n)² ≥ (log₂ k)²
    ```

    **Mathematical Content**:
    For security parameter families indexed by k ≥ 2, the residual complexity λ_base = (log₂ n)²
    is bounded below by the constant (log₂ k)². This establishes the minimum "hardness floor"
    for the family—no instance can have residual smaller than (log₂ k)².

    **Concrete Bounds** (standard security levels):
    - k=64:  λ_base ≥ (log₂ 64)²  = 6² = 36  (minimal practical security)
    - k=128: λ_base ≥ (log₂ 128)² = 7² = 49  (standard 128-bit security)
    - k=256: λ_base ≥ (log₂ 256)² = 8² = 64  (post-quantum security parameter)

    **Why Crucial for Quasi-Polynomial Bound**:
    The QP-sharp profile achieves time bound n^{Ω(log n)} via residual λ = Θ(log² n):
    ```
    λ_base = (log₂ n)²
    → Bound = 2^{λ_base} = 2^{(log₂ n)²} = n^{log₂ n}  (quasi-polynomial in n)
    ```

    This theorem establishes that λ_base ≥ (log₂ k)², ensuring the bound holds uniformly
    for all n ≥ k in the security parameter family.

    **Proof Strategy**:
    Pure monotonicity argument using Mathlib lemmas (no custom axioms):
    1. **Domain**: n ≥ k (from SecurityParam k type constraint via ge_k)
    2. **Log monotone**: log₂ n ≥ log₂ k (Nat.log_mono_right from Mathlib)
    3. **Power monotone**: (log₂ n)² ≥ (log₂ k)² (Nat.pow_le_pow_left from Mathlib)

    **Trust Boundary**: Proven theorem relying only on Mathlib monotonicity lemmas.
    No custom axioms introduced—bounds follow from type-level constraints and monotonicity.

    **Paper References**:
    - §8.A "Per-instance Deterministic Bounds" - λ_base = (log₂ n)² formula
    - Theorem 8.A "Quasi-polynomial bound" - n^{Ω(log n)} from λ = Θ(log² n)
    - §3 "Parametric Complexity Spectrum" - Security parameter families k → L*(φ, k)

    **Application**: PlantCore.lean uses this bound to establish minimum residual for
    quasi-polynomial OWF security.
-/
theorem lambdaBaseSize_ge_generic (_h_k : k ≥ 2) (n : SecurityParam k) :
    (Nat.log 2 n.val) ^ 2 ≥ (Nat.log 2 k) ^ 2 := by
  -- Extract bound n ≥ k from type constraint
  have h_n_ge_k : n.val ≥ k := ge_k n
  -- Apply log monotonicity: n ≥ k → log₂ n ≥ log₂ k
  have h_log_ge : Nat.log 2 n.val ≥ Nat.log 2 k := Nat.log_mono_right h_n_ge_k
  -- Apply power monotonicity: log₂ n ≥ log₂ k → (log₂ n)² ≥ (log₂ k)²
  exact Nat.pow_le_pow_left h_log_ge 2

/- **Axiom Audit**: Trust boundary verification for security parameter encoding.

   **SecurityParam**: Pure type definition (subtype {n // k ≤ n}).
   - No axioms—just type-theoretic structure
   - Constraint k ≤ n encoded definitionally, not axiomatically

   **lambdaBaseSize_ge_generic**: Proven theorem using only Mathlib lemmas.
   - Dependencies: Nat.log_mono_right, Nat.pow_le_pow_left (standard monotonicity)
   - No custom axioms introduced

   **Significance**: This module ELIMINATES historical domain axioms by encoding constraints
   in types. Previous versions had axioms like `practical_domain_bound : n ≥ 64 → ...`.
   Now: domain restrictions are definitional, shrinking trust boundary.

   **Verification**: The #print axioms commands below confirm no custom axioms.
-/
#print axioms SecurityParam
#print axioms lambdaBaseSize_ge_generic

end SecurityParam

end LStar.Base
