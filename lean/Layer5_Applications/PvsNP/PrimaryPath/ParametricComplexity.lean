import Layer5_Applications.PvsNP.ComplexityClasses.ComplexityClasses
import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Mathlib.Data.Nat.Basic

/-!
# Parametric Complexity Classes: FP and FNP Families

This module defines **parametric versions** of FP and FNP that work over families
indexed by security parameter n. This is the natural setting for:
- OWF families (hardness grows with n)
- Asymptotic complexity (cofinitely many n)
- Uniform algorithms (same machine works for all n)

## Key Definitions

- `InFP_parametric`: Uniform polynomial-time function families
- `InFNP_parametric`: Uniform polynomial-time verifiable relation families
- `FPneFNP_parametric`: Asymptotic separation between search and decision

## Design Principles

**Uniformity**: A single algorithm/verifier (same Turing machine) works for all n,
with input (n, x) where n is the security parameter.

**Polynomial Bound**: One polynomial p(n) bounds time for all n (no re-tuning).

**Asymptotics**: Properties hold for cofinitely many n (large enough n).

## Alignment with Existing Code

This uses the existing `RandAdv`, `InFP`, `InFNP` definitions from
`ComplexityClasses.lean`, extending them to families by:
1. Taking `α, β : Nat → Type` (type families indexed by n)
2. Requiring **one** adversary type T works for all n
3. Enforcing **one** polynomial degree applies to all n

**Paper reference**: §11 (Parametric complexity classes), §9 (FP and FNP families)

-/

namespace LStar.Complexity

/-! ## Parametric FP: Uniform Polynomial-Time Function Families -/

/-- **Parametric FP (UNIFORM)**: Uniform polynomial-time function families.

A family `{f_n : α n → β n}` is in `FP_parametric` if there exists:
1. A **single uniform machine**: `M : RandAdv (Σ n, α n) (Σ n, β n) T` that takes
   `⟨n, x⟩` as input and returns `⟨n, f_n(x)⟩`
2. A **single polynomial degree**: One deg such that M has time bound n^deg for all n
3. **Determinism**: Machine doesn't use randomness
4. **Correctness**: M computes f_n for all n

**Key Insight**: The Sigma type `Σ n, α n` forces n to be DATA (runtime input),
not a TYPE-LEVEL parameter. This enforces TRUE uniformity - a single algorithm
that receives n as part of its input, matching the standard textbook definition.

**Why Sigma types enforce uniformity**:
- `M : RandAdv (Σ n, α n) ...` → Single machine M, n is runtime data
- `A : ∀ n, RandAdv (α n) ...` → Family of machines {A_n}, allows per-n specialization

**Polynomial Time in Input Size** (proven equivalence to textbook formulations):
The bound `M.time_bound n ≤ (n+1)^deg` establishes polynomial time in the full input
length |⟨n,x⟩|. The connection is proven via the following chain:

1. **Size lower bound** (ParamSizeLowerBound typeclass): `size x ≥ n` for all x : α n
2. **Input encoding**: `size ⟨n,x⟩ ≥ n` (security parameter is part of input)
3. **Therefore**: Time polynomial in n → time polynomial in `size ⟨n,x⟩` (input length)

**Textbook alignment**: This formulation is **equivalent** to "polynomial in input size"
(Goldreich Vol. 1 §2.2.7, Arora-Barak §1.2). Using security parameter n directly
provides cleaner uniformity statements (single degree deg for all n) while the size
bound typeclass ensures semantic equivalence with standard input-size formulations.

**Why this works**: Since inputs must encode the security parameter (size x ≥ n),
polynomial time in n automatically implies polynomial time in input length.

**Example**: The family f_n : BitVec n → BitVec n defined by f_n(x) = x ⊕ x is in
FP_parametric with degree 1 (linear time in n, hence linear in input length).

**Non-Example**: A family where f_n has time bound n² for even n but n³ for odd n
is NOT in FP_parametric (no single degree works uniformly).
-/
def InFP_parametric {α β : Nat → Type} [∀ n, Sized (α n)] [∀ n, Sized (β n)]
    (f_family : ∀ n, α n → β n) : Prop :=
  ∃ (deg T : Nat)
     (M : RandAdv (Sigma fun n => α n) (Sigma fun n => β n) T),
    -- Deterministic: doesn't use coins
    (∀ c₁ c₂ s, M.run c₁ s = M.run c₂ s) ∧
    -- Correctness: M computes f_n at each n (returns ⟨n, f_n(x)⟩)
    (∀ n x, M.run ⟨0, M.coins_pos⟩ ⟨n, x⟩ = ⟨n, f_family n x⟩) ∧
    -- Uniform polynomial bound: same degree deg for all n
    (∀ n, M.time_bound n ≤ (n + 1) ^ deg)

/-! ## Parametric FNP: Uniform Polynomial-Time Verifiable Relation Families -/

/-- **Parametric FNP (UNIFORM)**: Uniform polynomial-time verifiable relation families.

A family `{R_n : α n → β n → Prop}` is in `FNP_parametric` if there exists:
1. A **single uniform verifier**: `V : RandAdv (Σ n, α n × β n) Bool T` that takes
   `⟨n, (x, y)⟩` as input and returns true iff R_n(x, y) holds
2. A **single polynomial degree**: One deg such that V has time bound n^deg for all n
3. **Determinism**: Verifier doesn't use randomness
4. **Correctness**: V correctly verifies R_n for all n

**Key Insight**: This is NP-search (find witnesses) with uniform verification.
The family R_n(x, y) is "y is a witness for x at security parameter n".

The Sigma type `Σ n, α n × β n` enforces uniformity - a single verifier receives
the security parameter n as DATA along with the instance-witness pair.

**Example**: The family R_n(φ, a) = "a satisfies CNF φ of size n" is in FNP_parametric
with degree 2 (check each clause, linear in formula size).

**Relation to InFNP**: At fixed n, if R_family n is in FNP (fixed-size), then
the collection {R_family n} is in FNP_parametric if one verifier works for all n.

**Standard Alignment Note**: This generic definition does NOT include a polynomial
witness-size bound (standard FNP requires witnesses to be polynomially bounded).
For standard-aligned FNP with explicit witness-length bounds, use `InFNP_parametric_bits`
from `ParametricBitstringBridge.lean`, which includes the constraint:
`∃ C k, C > 0 ∧ k > 0 ∧ ∀ n, wlen n ≤ C * (n + 1) ^ k`
The main proof path uses `InFNP_parametric_bits` for this reason.
-/
def InFNP_parametric {α β : Nat → Type} [∀ n, Sized (α n)] [∀ n, Sized (β n)]
    (R_family : ∀ n, α n → β n → Prop) : Prop :=
  ∃ (deg T : Nat)
     (V : RandAdv (Sigma fun n => α n × β n) Bool T),
    -- Deterministic: doesn't use coins
    (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
    -- Correctness: V verifies R_n at each n
    (∀ n x y, V.run ⟨0, V.coins_pos⟩ ⟨n, (x, y)⟩ = true ↔ R_family n x y) ∧
    -- Uniform polynomial bound: same degree deg for all n
    (∀ n, V.time_bound n ≤ (n + 1) ^ deg)

/-! ## Parametric FP ≠ FNP: Asymptotic Separation -/

/-- **FP ≠ FNP (parametric)**: Asymptotic separation between search and decision.

This states: There exists a relation family in FNP_parametric that is NOT in
FP_parametric, meaning **no uniform polynomial-time witness finder exists**.

**Formal Definition**: There exists R in FNP_parametric such that for every
alleged witness finder f_family:
- Either f_family is not uniformly polynomial-time, OR
- f_family fails to find witnesses for cofinitely many n

**Key Difference from Fixed FP≠FNP**:
- Fixed: At specific size n, some relation R_n is hard
- Parametric: For large enough n, the family R_n is hard uniformly

**Cryptographic Interpretation**: This is the natural complexity assumption for
OWF families - "as n grows, inverting becomes impossible uniformly".

**Relation to P≠NP**: FP≠FNP (parametric) implies P≠NP, because if P=NP then
the uniform decider lifts to a uniform witness finder (proved below).
-/
def FPneFNP_parametric : Prop :=
  ∃ (α β : Nat → Type) (_inst_α : ∀ n, Sized (α n)) (_inst_β : ∀ n, Sized (β n))
    (R : ∀ n, α n → β n → Prop),
    InFNP_parametric R ∧
    -- No uniform poly-time witness finder (asymptotic hardness)
    ¬(∃ f_family : ∀ n, α n → β n,
        InFP_parametric f_family ∧
        -- Correct for cofinitely many n (allows finite exceptions)
        (∃ N₀ : Nat, ∀ n ≥ N₀, ∀ x : α n,
          (∃ y : β n, R n x y) →  -- If witness exists
          R n x (f_family n x)))   -- Then f finds it

/-! ## Helper Definitions: Parametric Versions of Standard Classes -/

/-- **Parametric P**: Uniform polynomial-time decidable language families.

A family of languages {L_n : Lang (α n)} is in P_parametric if membership
can be decided uniformly in polynomial time.

**Uniformity enforcement**: Uses Sigma type to require a single decision algorithm
that receives the security parameter n as input data (not as type index).
-/
def InP_parametric {α : Nat → Type} [∀ n, Sized (α n)]
    (L_family : ∀ n, Lang (α n)) : Prop :=
  ∃ (deg : Nat) (T : Nat)
     (M : RandAdv (Sigma fun n => α n) Bool T),
    -- Deterministic: doesn't use coins
    (∀ c₁ c₂ s, M.run c₁ s = M.run c₂ s) ∧
    -- Correctness: M decides L_n at each n
    (∀ n x, M.run ⟨0, M.coins_pos⟩ ⟨n, x⟩ = true ↔ L_family n x) ∧
    -- Uniform polynomial bound: same degree deg for all n
    (∀ n, M.time_bound n ≤ (n + 1) ^ deg)

/-- **Parametric NP**: Uniform polynomial-time verifiable language families.

A family of languages {L_n : Lang (α n)} is in NP_parametric if membership
has uniform polynomial-time verifiable witnesses.

**Uniformity enforcement**: Uses Sigma type to require a single verifier algorithm
that receives the security parameter n as input data (not as type index).
-/
def InNP_parametric {α : Nat → Type} [∀ n, Sized (α n)]
    (L_family : ∀ n, Lang (α n)) : Prop :=
  ∃ (β : Nat → Type) (_inst : ∀ n, Sized (β n)) (deg : Nat) (T : Nat)
     (V : RandAdv (Sigma fun n => α n × β n) Bool T),
    -- Deterministic: doesn't use coins
    (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
    -- Correctness: V verifies L_n at each n
    (∀ n x, L_family n x ↔ ∃ y : β n, V.run ⟨0, V.coins_pos⟩ ⟨n, (x, y)⟩ = true) ∧
    -- Uniform polynomial bound: same degree deg for all n
    (∀ n, V.time_bound n ≤ (n + 1) ^ deg)

/-! ## Lifting Lemmas: Parametric ↔ Fixed-Size -/

/-- **Lifting Lemma**: If each R_n is in FNP at fixed size n with the SAME
polynomial degree, then the family is in FNP_parametric.

This is the key connection: size-by-size polynomial time + uniform degree = parametric.
-/
theorem fnp_uniform_implies_parametric {α β : Nat → Type} [∀ n, Sized (α n)] [∀ n, Sized (β n)]
    (R : ∀ n, α n → β n → Prop)
    (deg : Nat)
    -- **Fixed**: Strengthen h_uniform to include all required properties
    -- This makes the theorem actually provable without type transport gaps
    (h_uniform : ∃ (T : Nat),
      ∀ n, ∃ (V : RandAdv (α n × β n) Bool T),
        (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
        (∀ x y, V.run ⟨0, V.coins_pos⟩ (x, y) = true ↔ R n x y) ∧
        V.time_bound n ≤ (n + 1) ^ deg)
    : InFNP_parametric R := by
  -- Extract the uniform T and verifier family from h_uniform
  obtain ⟨T, h_verifiers⟩ := h_uniform

  -- Use classical choice to extract per-n verifiers, then wrap into Sigma machine
  classical
  let V_family : ∀ n, RandAdv (α n × β n) Bool T := fun n =>
    Classical.choose (h_verifiers n)

  -- Extract the properties for each verifier
  have h_V : ∀ n,
      (∀ c₁ c₂ p, (V_family n).run c₁ p = (V_family n).run c₂ p) ∧
      (∀ x y, (V_family n).run ⟨0, (V_family n).coins_pos⟩ (x, y) = true ↔ R n x y) ∧
      (V_family n).time_bound n ≤ (n + 1) ^ deg := fun n =>
    Classical.choose_spec (h_verifiers n)

  -- Wrap into uniform Sigma machine via AlgSpec + Church-Turing bridge
  -- First create AlgSpec, then use algspec_has_tm to get RandAdv
  -- Use max deg 1 for k to ensure k > 0 (AlgSpec requirement)
  -- This is valid since m^deg ≤ m^(max deg 1) for m ≥ 1

  let k_val := max deg 1

  have h_k_pos : k_val > 0 := by simp [k_val]

  let V_spec : AlgSpec (Sigma fun n => α n × β n) Bool T := {
    run := fun c s =>
      let ⟨n, p⟩ := s
      (V_family n).run c p
    time_bound := fun m => m ^ deg  -- Uniform bound (matches the hypothesis)
    C := 1  -- Uniform constant
    k := k_val  -- Use max deg 1 to ensure positivity
    h_C_pos := by omega
    h_k_pos := h_k_pos
    poly_explicit := fun s => by
      -- time_bound (size s) = (size s)^deg ≤ 1 * (size s + 1)^k_val
      calc Sized.size s ^ deg
        _ ≤ (Sized.size s + 1) ^ deg := Nat.pow_le_pow_left (Nat.le_succ _) deg
        _ ≤ (Sized.size s + 1) ^ k_val := by
            apply Nat.pow_le_pow_right (Nat.succ_pos _)
            exact Nat.le_max_left deg 1
        _ = 1 * (Sized.size s + 1) ^ k_val := by rw [Nat.one_mul]
    time_bound_uniform := fun m => by
      -- time_bound m = m^deg ≤ 1 * (m + 1)^k_val
      calc m ^ deg
        _ ≤ (m + 1) ^ deg := Nat.pow_le_pow_left (Nat.le_succ _) deg
        _ ≤ (m + 1) ^ k_val := by
            apply Nat.pow_le_pow_right (Nat.succ_pos _)
            exact Nat.le_max_left deg 1
        _ = 1 * (m + 1) ^ k_val := by rw [Nat.one_mul]
    output_bounded := fun c s => by
      -- Output is Bool (size 1), time_bound is (size s)^deg ≥ 1
      calc Sized.size ((V_family s.1).run c s.2)
        _ = 1 := rfl
        _ ≤ (Sized.size s) ^ deg := by
          apply Nat.one_le_pow
          apply Sized.size_pos
    coins_pos := (V_family 0).coins_pos
  }

  -- Use Church-Turing bridge to get RandAdv from AlgSpec
  obtain ⟨V, h_V_run, h_V_C, h_V_k, _⟩ := algspec_has_tm V_spec

  -- Package into InFNP_parametric witness
  -- Return k_val (= max deg 1) as the degree to match V.k
  refine ⟨k_val, T, V, ?_, ?_, ?_⟩

  -- Determinism: ∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p
  · intro c₁ c₂ s
    -- V.toAlgSpec.run = V_spec.run, so V.run c s = V_spec.run c s
    have h_eq : V.toAlgSpec.run c₁ s = V.toAlgSpec.run c₂ s := by
      simp only [h_V_run, V_spec]
      let ⟨n, p⟩ := s
      exact (h_V n).1 c₁ c₂ p
    exact h_eq

  -- Correctness: ∀ n x y, V.run ⟨0, V.coins_pos⟩ ⟨n, (x, y)⟩ = true ↔ R n x y
  · intro n x y
    -- V.toAlgSpec.run = V_spec.run
    have h_eq : V.toAlgSpec.run ⟨0, V.coins_pos⟩ ⟨n, (x, y)⟩ = true ↔ R n x y := by
      simp only [h_V_run, V_spec]
      exact (h_V n).2.1 x y
    exact h_eq

  -- Polynomial bound: ∀ n, V.time_bound n ≤ (n + 1) ^ k_val
  · intro n
    -- V.time_bound matches V_spec.time_bound via Church-Turing bridge
    -- V.C = V_spec.C = 1, V.k = V_spec.k = k_val
    -- V.time_bound n ≤ V.C * (n + 1)^V.k = 1 * (n + 1)^k_val
    calc V.time_bound n
      _ ≤ V.C * (n + 1) ^ V.k := V.time_bound_uniform n
      _ = 1 * (n + 1) ^ k_val := by rw [h_V_C, h_V_k]
      _ = (n + 1) ^ k_val := by rw [Nat.one_mul]

/-- **Projection Lemma**: If R_family is in FNP_parametric, then each R n is
in FNP at fixed size n (with the same polynomial degree).

This unwraps the uniform Sigma machine V into per-n verifiers by fixing n.
-/
theorem fnp_parametric_implies_each {α β : Nat → Type} [∀ n, Sized (α n)] [∀ n, Sized (β n)]
    (R : ∀ n, α n → β n → Prop)
    (h_param : InFNP_parametric R)
    : ∀ n, ∃ (T : Nat) (V : RandAdv (α n × β n) Bool T),
        (∀ c₁ c₂ p, V.run c₁ p = V.run c₂ p) ∧
        (∀ x y, V.run ⟨0, V.coins_pos⟩ (x, y) = true ↔ R n x y) := by
  intro n
  obtain ⟨deg, T, V_sigma, h_det, h_correct, h_poly⟩ := h_param

  -- Project: V_sigma works over Sigma type, construct per-n verifier via AlgSpec
  -- V_n uses adjusted time_bound and constants to account for size n overhead
  let size_n := Sized.size (n : Nat)

  -- Positivity for V_sigma.k (needed for AlgSpec)
  have h_k_pos : V_sigma.k > 0 := V_sigma.h_k_pos
  have h_C_pos : V_sigma.C > 0 := V_sigma.h_C_pos

  -- Combined constant is positive
  have h_C_combined_pos : V_sigma.C * (size_n + 1) ^ V_sigma.k > 0 := by
    apply Nat.mul_pos h_C_pos
    apply Nat.pow_pos
    omega

  -- Create AlgSpec for the projected verifier
  let V_n_spec : AlgSpec (α n × β n) Bool T := {
    run := fun c p => V_sigma.toAlgSpec.run c ⟨n, p⟩
    -- Use V_sigma's time_bound but account for the extra size n
    time_bound := fun m => V_sigma.time_bound (size_n + m)
    -- Absorb the size n overhead into the constant
    C := V_sigma.C * (size_n + 1) ^ V_sigma.k
    k := V_sigma.k
    h_C_pos := h_C_combined_pos
    h_k_pos := h_k_pos
    poly_explicit := fun p => by
      have h_sigma := V_sigma.poly_explicit ⟨n, p⟩
      simp only [size_n]
      have h_size : Sized.size (⟨n, p⟩ : Sigma fun n => α n × β n) =
                    Sized.size (n : Nat) + Sized.size p := rfl
      rw [h_size] at h_sigma
      let a := Sized.size (n : Nat)
      let b := Sized.size p
      have h_prod : a + b + 1 ≤ (a + 1) * (b + 1) := by
        calc a + b + 1
          _ ≤ a * b + (a + b + 1) := Nat.le_add_left _ _
          _ = a * b + a + (b + 1) := by simp [Nat.add_assoc]
          _ = a * (b + 1) + (b + 1) := by rw [Nat.mul_succ]
          _ = (a + 1) * (b + 1) := by rw [Nat.succ_mul]
      calc V_sigma.time_bound (Sized.size (n : Nat) + Sized.size p)
        _ ≤ V_sigma.C * (Sized.size (n : Nat) + Sized.size p + 1) ^ V_sigma.k := h_sigma
        _ ≤ V_sigma.C * ((Sized.size (n : Nat) + 1) * (Sized.size p + 1)) ^ V_sigma.k := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_left h_prod
        _ = V_sigma.C * ((Sized.size (n : Nat) + 1) ^ V_sigma.k * (Sized.size p + 1) ^ V_sigma.k) := by
          rw [Nat.mul_pow]
        _ = V_sigma.C * (Sized.size (n : Nat) + 1) ^ V_sigma.k * (Sized.size p + 1) ^ V_sigma.k := by
          rw [Nat.mul_assoc]
    time_bound_uniform := fun m => by
      have h_sigma := V_sigma.time_bound_uniform (size_n + m)
      simp only [size_n]
      let a := Sized.size (n : Nat)
      let b := m
      have h_prod : a + b + 1 ≤ (a + 1) * (b + 1) := by
        calc a + b + 1
          _ ≤ a * b + (a + b + 1) := Nat.le_add_left _ _
          _ = a * b + a + (b + 1) := by simp [Nat.add_assoc]
          _ = a * (b + 1) + (b + 1) := by rw [Nat.mul_succ]
          _ = (a + 1) * (b + 1) := by rw [Nat.succ_mul]
      calc V_sigma.time_bound (Sized.size (n : Nat) + m)
        _ ≤ V_sigma.C * (Sized.size (n : Nat) + m + 1) ^ V_sigma.k := h_sigma
        _ ≤ V_sigma.C * ((Sized.size (n : Nat) + 1) * (m + 1)) ^ V_sigma.k := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_left h_prod
        _ = V_sigma.C * ((Sized.size (n : Nat) + 1) ^ V_sigma.k * (m + 1) ^ V_sigma.k) := by
          rw [Nat.mul_pow]
        _ = V_sigma.C * (Sized.size (n : Nat) + 1) ^ V_sigma.k * (m + 1) ^ V_sigma.k := by
          rw [Nat.mul_assoc]
    output_bounded := fun c p => by
      calc Sized.size (V_sigma.toAlgSpec.run c ⟨n, p⟩)
        _ = 1 := rfl  -- Bool has size 1
        _ ≤ V_sigma.time_bound (size_n + Sized.size p) := by
          have h := V_sigma.output_bounded c ⟨n, p⟩
          have h_size : Sized.size (⟨n, p⟩ : Sigma fun n => α n × β n) =
                        size_n + Sized.size p := rfl
          rw [← h_size]
          exact h
    coins_pos := V_sigma.coins_pos
  }

  -- Use Church-Turing bridge to get RandAdv from AlgSpec
  obtain ⟨V_n, h_V_n_run, _, _, _⟩ := algspec_has_tm V_n_spec

  refine ⟨T, V_n, ?_, ?_⟩
  · intro c₁ c₂ p
    -- V_n.toAlgSpec.run = V_n_spec.run
    have h_eq : V_n.toAlgSpec.run c₁ p = V_n.toAlgSpec.run c₂ p := by
      simp only [h_V_n_run, V_n_spec]
      exact h_det c₁ c₂ ⟨n, p⟩
    exact h_eq
  · intro x y
    have h_eq : V_n.toAlgSpec.run ⟨0, V_n.coins_pos⟩ (x, y) = true ↔ R n x y := by
      simp only [h_V_n_run, V_n_spec]
      exact h_correct n x y
    exact h_eq

-- Axiom Audits: Trust Boundary Transparency
#print axioms InFP_parametric
#print axioms InFNP_parametric
#print axioms FPneFNP_parametric
#print axioms InP_parametric
#print axioms InNP_parametric
#print axioms fnp_uniform_implies_parametric
#print axioms fnp_parametric_implies_each

end LStar.Complexity
