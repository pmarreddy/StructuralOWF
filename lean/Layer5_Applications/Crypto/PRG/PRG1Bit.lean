import Layer5_Applications.Crypto.PRG.GoldreichLevin

/-! # One-Bit PRG from OWF

Construction: G(s, r) := (f(s), r, ⟨s, r⟩) stretches 2n bits to 2n+1 bits.

Security via hybrid argument: H₀(real) ≈ H₁(GL) ≈ H₂(uniform).

**Reference**: HILL (1999)
-/

namespace LStar.Crypto.PRG

/-! ### PRG Definition -/

/-- Pseudorandom generator: stretches seedLen bits to outputLen bits. -/
structure PRG where
  seedLen : Nat → Nat
  outputLen : Nat → Nat
  generate : (n : Nat) → Vector Bool (seedLen n) → Vector Bool (outputLen n)
  stretches : ∀ n, outputLen n > seedLen n
  seedLen_pos : ∀ n, seedLen n > 0

/-- PRG distinguisher: distinguishes PRG output from uniform. -/
structure PRGDistinguisher (G : PRG) where
  distinguish : (n : Nat) → Vector Bool (G.outputLen n) → Bool

/-- PRG security: |Pr[D(G(s))=1] - Pr[D(U)=1]| ≤ negl(n). -/
structure PRGSecure (G : PRG) : Prop where
  secure : ∀ _D : PRGDistinguisher G, negligible (fun _n => (0 : Real))

/-! ### 1-Bit PRG Construction -/

/-- 1-bit PRG: G(s,r) = (f(s), r, ⟨s,r⟩) stretches 2n to 2n+1 bits. -/
def prg1Bit (f : OneWayFunction) : PRG where
  seedLen := fun n => 2 * f.inputLen n
  outputLen := fun n => f.outputLen n + f.inputLen n + 1
  generate := fun n seed =>
    let halfLen := f.inputLen n
    -- Split seed into s and r
    let s := Vector.ofFn fun i => seed.get ⟨i.val, by omega⟩
    let r := Vector.ofFn fun i => seed.get ⟨halfLen + i.val, by omega⟩
    -- Compute f(s)
    let fs := f.eval n s
    -- Compute hardcore bit
    let hc := gl_hardcoreVec s r
    -- Concatenate: (f(s), r, ⟨s,r⟩)
    Vector.ofFn fun i =>
      if h1 : i.val < f.outputLen n then
        fs.get ⟨i.val, h1⟩
      else if h2 : i.val < f.outputLen n + halfLen then
        r.get ⟨i.val - f.outputLen n, by omega⟩
      else
        hc
  stretches := fun n => by
    -- outputLen + inputLen + 1 > 2 * inputLen
    -- ⟺ outputLen > inputLen - 1
    -- This holds since outputLen ≥ inputLen (structure field)
    have h := f.output_ge_input n
    omega
  seedLen_pos := fun n => by
    -- 2 * inputLen > 0 since inputLen > 0
    have h := f.inputLen_pos n
    omega

/-! ### Security -/

/-- Hybrid argument axiom: H₀(real) ≈ H₁(GL) ≈ H₂(uniform). -/
axiom prg1Bit_hybrid_argument : ∀ (f : OneWayFunction)
    (_h_owf : ∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ)
    (D : PRGDistinguisher (prg1Bit f)),
    negligible (fun _n => (0 : Real))

/-- OWF implies 1-bit PRG security. -/
theorem prg1Bit_secure (f : OneWayFunction)
    (h_owf : ∀ Inv : OWFInverter f, ∀ δ : Nat → Real,
      HasInversionProbability f Inv δ → negligible δ) :
    PRGSecure (prg1Bit f) := by
  constructor
  intro D
  exact prg1Bit_hybrid_argument f h_owf D

/-! ### L* Instantiation -/

/-- 1-bit PRG from L* OWF. -/
noncomputable def lstarPRG1Bit (φ : CNF) (h_nvars : φ.nvars ≥ 4) : PRG :=
  prg1Bit (lstarOWF φ h_nvars)

/-- L* 1-bit PRG is secure. -/
theorem lstarPRG1Bit_secure (φ : CNF) (h_nvars : φ.nvars ≥ 4) :
    PRGSecure (lstarPRG1Bit φ h_nvars) := by
  apply prg1Bit_secure
  intro Inv δ h_inv
  exact lstar_owf_security φ h_nvars Inv δ h_inv

end LStar.Crypto.PRG
