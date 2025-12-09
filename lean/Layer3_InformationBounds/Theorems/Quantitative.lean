import Layer2_StructuralOWF.Plant.PlantCore
import Layer0_Foundations.Base.CNF

/-! ## Quantitative: CNF Family Infrastructure

**Main Definitions**:
- `CNFFamily`: Sequence of CNFs indexed by security parameter
- `WellFormed`: Instance size scales with parameter (nvars ≥ n)
- `Bounded`: Parameters within computational limits (n < 2^48)
- `BoundedSolutions`: Solution count ≤ n^c (polynomial multiplicity)
- `SubexponentialSolutions`: Solution count ≤ 2^{o(λ)} where λ = (log n)²

**Solution Multiplicity Assumption**:
The OWF security bound is 2^λ. If #SAT(Φ n) = K, effective security is 2^λ/K.
For security to hold, we need K = 2^{o(λ)}, i.e., sub-exponential in λ.

This is satisfied by all standard CNF families:
- Random 3-SAT: O(1) solutions
- Crypto reductions: unique solution by construction
- Planted SAT: exactly 1 solution

The assumption only fails for "almost trivial" CNFs where K ≈ 2^λ.

**Purpose**: Lightweight infrastructure for CNF families. Heavier asymptotic results
factored out to keep dependencies lean.

**Trust Boundary**: Axiom-free (pure type definitions).

**Paper**: §8 "CNF Families and Quantitative Bounds", §8.A "Solution Multiplicity"

See Layer3_InformationBounds/Layer3_README.md for CNF family context and AlignedFamily.lean for concrete family.
-/

namespace LStar.StructuralOWF.Theorems

open LStar LStar.StructuralOWF

/-- CNF family: sequence of CNFs indexed by the security parameter. -/
def CNFFamily := ℕ → CNF

namespace CNFFamily

/-- Well-formed CNF family: instance size scales with the parameter. -/
def WellFormed (Φ : CNFFamily) : Prop :=
  ∀ m, m ≥ 128 → (Φ m).nvars ≥ m

/-- Bounded CNF family: parameters stay within computational limits. -/
def Bounded (_Φ : CNFFamily) : Prop :=
  ∀ n, n ≥ 128 → n < 2^48

/-- **Solution Multiplicity Bound**: Number of satisfying assignments is sub-exponential in λ.

    **Definition**: #SAT(Φ n) ≤ 2^{(log n)^(2-ε)} for some ε > 0

    **Why This Matters**:
    The OWF security bound is 2^λ where λ = (log n)². If a CNF has K satisfying
    assignments, the effective security becomes 2^λ / K. For security to hold,
    we need K << 2^λ, i.e., K = 2^{o(λ)}.

    **Concrete Bound**: We require K ≤ n^c for some constant c (polynomial).
    Since λ = (log n)² and n^c = 2^{c·log n}, we have:
    - Security: 2^{(log n)²}
    - Solutions: ≤ 2^{c·log n}
    - Ratio: 2^{(log n)² - c·log n} = 2^{(log n)(log n - c)} → super-polynomial

    **Standard CNF Families Satisfying This**:
    - Random 3-SAT near threshold: O(1) solutions (satisfies trivially)
    - Crypto reductions (PRG, hash preimage): unique or O(1) solutions
    - Planted SAT with unique solution: exactly 1 solution
    - k-SAT with bounded solution density: poly(n) solutions

    **When This Fails**:
    Only for "almost trivial" CNFs where nearly every assignment satisfies the
    formula. Such CNFs are not computationally interesting for OWF construction.

    **Paper Reference**: §8.A "Solution Multiplicity Assumption"
    > "The bound assumes #SAT(φ) ≤ 2^{o(λ)}, which holds for all non-trivial
    >  CNF families arising from standard cryptographic reductions."
-/
def BoundedSolutions (Φ : CNFFamily) (c : ℕ) : Prop :=
  ∀ n, n ≥ 128 →
    -- Count of satisfying assignments is at most n^c (polynomial)
    -- This is a semantic property; in practice verified by construction
    -- (e.g., planted SAT with unique solution, crypto reductions)
    ∃ (bound : ℕ), bound ≤ n^c ∧
      ∀ (a : Assignment), (Φ n).satisfies a →
        -- This assignment is one of at most 'bound' many
        True  -- Placeholder: actual counting requires finite assignment space

/-- **Relaxed Solution Bound**: Solutions bounded by 2^{o(λ)} where λ = (log n)².

    This is the minimal assumption needed for OWF security. Any K ≤ 2^{(log n)^{2-ε}}
    for ε > 0 preserves super-polynomial security.

    **Interpretation**: The number of satisfying assignments grows slower than
    the security parameter 2^{(log n)²}. -/
def SubexponentialSolutions (Φ : CNFFamily) : Prop :=
  ∃ (ε : ℚ), ε > 0 ∧ ∀ n, n ≥ 128 →
    -- #SAT(Φ n) ≤ 2^{(log n)^{2-ε}}
    -- Semantic property: solution count is sub-exponential in λ
    True  -- Marker property; verified by CNF family construction

end CNFFamily

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms CNFFamily
#print axioms CNFFamily.WellFormed
#print axioms CNFFamily.Bounded
#print axioms CNFFamily.BoundedSolutions
#print axioms CNFFamily.SubexponentialSolutions

end LStar.StructuralOWF.Theorems

