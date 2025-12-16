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
- Trust boundary: Eliminates domain axioms
- Type safety: Cannot use n < k (type system prevents)
- Ergonomics: `(n : SecurityParam 128)` cleaner than `(n : Nat) (h : n ≥ 128)`

**Applications**: OWF families indexed by SecurityParam (ensures minimum security level).

**Paper**: §5 "Security parameter families".

**Note**: The exponential profile (R = n) is used throughout the P≠NP proof.
This module provides general security parameter infrastructure.
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
    - `SecurityParam 128`: n ∈ [128, ∞) (standard security parameter)
    - `SecurityParam 256`: n ∈ [256, ∞) (post-quantum security parameter)
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

/-- **Logarithmic lower bound**: (log₂ n)² ≥ (log₂ k)² for n ≥ k.

    **Theorem Statement**:
    ```lean
    k ≥ 2 → n ∈ SecurityParam k → (log₂ n)² ≥ (log₂ k)²
    ```

    **Mathematical Content**:
    For security parameter families indexed by k ≥ 2, the value (log₂ n)²
    is bounded below by (log₂ k)².

    **Concrete Bounds** (standard security levels):
    - k=128: (log₂ n)² ≥ (log₂ 128)² = 7² = 49
    - k=256: (log₂ n)² ≥ (log₂ 256)² = 8² = 64

    **Proof Strategy**:
    Pure monotonicity argument using Mathlib lemmas (no custom axioms):
    1. **Domain**: n ≥ k (from SecurityParam k type constraint via ge_k)
    2. **Log monotone**: log₂ n ≥ log₂ k (Nat.log_mono_right from Mathlib)
    3. **Power monotone**: (log₂ n)² ≥ (log₂ k)² (Nat.pow_le_pow_left from Mathlib)

    **Trust Boundary**: Proven theorem relying only on Mathlib monotonicity lemmas.
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
-/
#print axioms SecurityParam
#print axioms lambdaBaseSize_ge_generic

end SecurityParam

end LStar.Base
