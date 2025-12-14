import Layer5_Applications.PvsNP.ComplexityClasses.RandAdv
import Layer5_Applications.PvsNP.ComplexityClasses.StructuralOWFSizedInstances
import Layer5_Applications.PvsNP.ComplexityClasses.EncodingDiscipline
import Layer5_Applications.PvsNP.PrimaryPath.ParametricBitstringBridge
import Layer5_Applications.PvsNP.PrimaryPath.EncodingHelpers
import Layer2_StructuralOWF.FrontierGate.FrontierGate

/-! ## OWFBridgeCommon: Shared Infrastructure for OWF Bridge Proofs

This module contains infrastructure shared between the exponential (flat) and
quasi-polynomial (QP) profiles for the OWF-based P≠NP proof.

**Shared Components**:
- `LStarInstanceFG.ext`: Extensionality lemma for L* instances
- `adapterInputEncoding`: Input encoding adapter for PPT adversary construction
- `formatSeparated_from_early_decode`: Format separation derivation from early_decode
- `encoding_semantics_abstract`: Abstract encoding semantics parameterized over decoding

**Profile-Specific** (in OWFBridge.lean / OWFBridgeQP.lean):
- `OWFInversionRelation`: The specific relation (uses different plant functions)
- `owf_inversion_not_in_fp`: Main FP non-membership proof
- `P_ne_NP`: Final theorem

**Design Rationale**:
The exponential profile uses:
1. Digest length: 64 bits (flat)
2. Plant function: plant_flat
3. OWF security theorem: f_is_one_way_exponential_flat

But they share the same adapter encoding machinery, format separation logic,
and proof structure. This file extracts the common parts to avoid duplication.

**Trust Boundary**: 0 axioms in this file (all lemmas are derived).
-/

namespace LStar.Complexity.StructuralOWFBridgeCommon

open LStar.StructuralOWF
open LStar.StructuralOWF.Foundations
open LStar.Complexity
open BitstringBridge

set_option linter.unusedSimpArgs false

/-! ## Type Infrastructure -/

/-- Extensionality lemma for LStarInstanceFG.

    Two LStarInstanceFG values are equal if their underlying LStarInstanceFull,
    encodedφ, and FrontierGateConfig components are equal (via HEq for dependent field).
    The remaining fields (fg_emergence_bound, fg_emergence_sizing, dag_size_ge_n,
    h_n_eq_nvars) are proof-irrelevant.
-/
@[ext (iff := false)]
lemma LStarInstanceFG.ext {A B : LStarInstanceFG}
    (hfull : A.toLStarInstanceFull = B.toLStarInstanceFull)
    (hencoded : A.encodedφ = B.encodedφ)
    (hfg : A.fg ≍ B.fg) : A = B := by
  cases A; cases B; cases hfull; cases hencoded
  simp at hfg
  cases hfg
  rfl

/-! ## Adapter Encodings

These adapters convert between the sigma-typed RandAdv and concrete PPTAdversary types.
Both profiles use Bits (n + 128) as the witness type, so the input adapter is shared.
-/

/-- Adapter input encoding: L → tape via sigma wrapping.

    Wraps L as ⟨φ.nvars, L⟩ and delegates to M's input encoding.

    **Design**: Uses sigma wrapping to adapt concrete type to sigma type expected by M.
    The size_bounded proof requires scaling constants to account for sigma overhead.

    **Note**: Returns TMInputEncodingBase (no injectivity) to match PPTAdversary's
    TMEncodingBase requirement. Injectivity not needed for correctness proofs.
-/
def adapterInputEncoding
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    : TMInputEncodingBase (Fin T × LStarInstanceFG) (Fin M.alphabetSize) where
  blank := M.encoding.input.blank
  encode := fun (c, L) => M.encoding.input.encode (c, ⟨L.encodedφ.nvars, L⟩)
  min_support := fun (c, L) => M.encoding.input.min_support (c, ⟨L.encodedφ.nvars, L⟩)
  min_support_spec := fun (c, L) i => M.encoding.input.min_support_spec (c, ⟨L.encodedφ.nvars, L⟩) i
  finite_support := fun (c, L) => M.encoding.input.finite_support (c, ⟨L.encodedφ.nvars, L⟩)
  C_encode := 2 ^ M.encoding.input.k_encode * M.encoding.input.C_encode
  k_encode := M.encoding.input.k_encode
  size_bounded := fun (c, L) => by
    let n := L.encodedφ.nvars
    let k := M.encoding.input.k_encode
    let C_M := M.encoding.input.C_encode

    have h_base :
        M.encoding.input.min_support (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) ≤
          C_M * (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k :=
      M.encoding.input.size_bounded (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG))

    have h_n_le_sizeL : n ≤ Sized.size L := by
      have h_n_eq : n = L.n := by simpa [n] using L.h_n_eq_nvars.symm
      have : n ≤ L.dag.n := by simpa [h_n_eq] using L.dag_size_ge_n
      simpa using this

    have h_size_wrapped_le :
        Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1 ≤
          2 * (Sized.size (c, L) + 1) := by
      -- After simp: LHS = T.log2 + 1 + (n + 1 + L.dag.n) + 1
      --             RHS = 2 * (T.log2 + 1 + L.dag.n + 1)
      simp only [Sized.size, sizedProd, sizedSigma, sizedNat]
      -- Use n ≤ L.dag.n (from h_n_le_sizeL after simp)
      simp only [Sized.size, sizedNat] at h_n_le_sizeL
      -- Now omega can handle it since all terms are concrete Nat expressions
      omega

    have h_pow_le :
        (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k ≤
          (2 * (Sized.size (c, L) + 1)) ^ k :=
      Nat.pow_le_pow_left h_size_wrapped_le k

    calc M.encoding.input.min_support (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG))
        ≤ C_M * (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k := h_base
      _ ≤ C_M * (2 * (Sized.size (c, L) + 1)) ^ k := by
        apply Nat.mul_le_mul_left
        exact h_pow_le
      _ = C_M * (2 ^ k * (Sized.size (c, L) + 1) ^ k) := by
        simp [Nat.mul_pow]
      _ = (2 ^ k * C_M) * (Sized.size (c, L) + 1) ^ k := by ring

/-! ## Format Separation -/

/-- **FormatSeparated from early_decode**: Derive FormatSeparated from RandAdv.early_decode.

    **Key insight**: adapterInputEncoding L encodes via M.encoding.input.encode ⟨φ.nvars, L⟩.
    So the initial configuration is the same as using M.encoding.input directly on the sigma.
    M.early_decode then gives us decoded = early_decode_default, and if early_decode_default.1 = 0,
    we have FormatSeparated.

    **Trust Boundary**: 0 axioms - derives from RandAdv structure + adapterInputEncoding definition.
-/
theorem formatSeparated_from_early_decode
  {T : Nat}
  (M : RandAdv (Sigma fun _n => LStarInstanceFG) (Sigma fun n => Bits (n + 128)) T)
  (h_early_zero : M.early_decode_default.1 = 0)
  : EncodingDiscipline.FormatSeparated M (adapterInputEncoding M) M.h_blank_consistent := by
  intro c L t h_t
  -- Goal: (M.encoding.output.decode tape).1 = 0
  -- where tape = getTape0 cfg, cfg = step^[t] init_cfg
  -- and init_cfg = initWithEncodingBase M.M (adapterInputEncoding M) L ...

  -- Key: adapterInputEncoding L encodes L as M.encoding.input.encode ⟨φ.nvars, L⟩
  -- So init_cfg has the same tape as using M.encoding.input on ⟨φ.nvars, L⟩

  -- Apply M.early_decode to ⟨L.encodedφ.nvars, L⟩
  have h_ed := M.early_decode c ⟨L.encodedφ.nvars, L⟩ t h_t

  -- h_ed : (let init_cfg := initWithEncodingBase M.M M.encoding.input ⟨φ.nvars, L⟩ ...
  --         let cfg := step^[t] init_cfg
  --         M.encoding.output.decode (getTape0 cfg M.h_tape_pos)) = M.early_decode_default

  -- The init_cfg in our goal uses adapterInputEncoding:
  -- tapes[0] = (adapterInputEncoding M).encode L = M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩
  -- This is definitionally equal to the init_cfg in h_ed!

  -- Show the init configs are equal by showing the tapes are equal
  -- Simplify to show equality of decoded values
  simp only [EncodingDiscipline.FormatSeparated, adapterInputEncoding] at *

  -- The decoded value equals M.early_decode_default (from h_ed)
  -- And M.early_decode_default.1 = 0 (from h_early_zero)
  simp only [initWithEncodingBase, getTape0] at h_ed ⊢
  rw [h_ed, h_early_zero]

/-! ## Adapter Output Decoding (Profile-Specific Template)

The output decoding depends on the specific bitsToRandomness variant.
Each profile defines its own adapterOutputDecoding using this template.
-/

/-- Template for adapter output decoding.

    **Parameters**:
    - `decodeWitness`: Profile-specific function to decode Bits to Randomness

    **Design**: Each profile instantiates with its specific bitsToRandomness.
-/
def mkAdapterOutputDecoding
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    (decodeWitness : (n : Nat) → Bits (n + 128) → Randomness)
    : TMOutputDecoding Randomness (Fin M.alphabetSize) where
  blank := M.encoding.output.blank
  decode := fun tape =>
    let sigma_result := M.encoding.output.decode tape
    decodeWitness sigma_result.1 sigma_result.2
  reads_finite := by
    obtain ⟨N, h_M_finite⟩ := M.encoding.output.reads_finite
    exact ⟨N, fun tape1 tape2 h_agree => by
      have h_eq := h_M_finite tape1 tape2 h_agree
      rw [h_eq]⟩

/-- Template for adapter TM encoding (combines input and output).

    **Note**: Returns TMEncodingBase (no injectivity) to match PPTAdversary requirements.
-/
def mkAdapterTMEncoding
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    (decodeWitness : (n : Nat) → Bits (n + 128) → Randomness)
    : TMEncodingBase (Fin T × LStarInstanceFG) Randomness (Fin M.alphabetSize) where
  input := adapterInputEncoding M
  output := mkAdapterOutputDecoding M decodeWitness
  blank_consistent := M.encoding.blank_consistent

/-! ## Halting Proof Helper

The halting proof for the PPT adversary is the same structure in both profiles.
-/

/-- Helper lemma for PPT adversary halting proof.

    Shows that the scaled time bound accommodates sigma overhead.
-/
theorem adapter_halts_helper
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    (x : LStarInstanceFG) :
    M.C * (Sized.size (⟨x.encodedφ.nvars, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
    M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := by
  let n := x.encodedφ.nvars
  -- Size relationships
  have h_nvars_eq : n = x.n := x.h_n_eq_nvars.symm
  have h_dag_ge : x.dag.n ≥ x.n := x.dag_size_ge_n
  have h_nvars_le_dag : n ≤ x.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
  have h_size_x : Sized.size x = x.dag.n := rfl

  have h_sigma_size : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size x := by
    simp only [Sized.size, sizedSigma, sizedNat]

  have h_size_bound : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size x + 1) := by
    rw [h_sigma_size, h_size_x]; omega

  have h1 : (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
            (2 * (Sized.size x + 1)) ^ M.k := Nat.pow_le_pow_left h_size_bound M.k
  have h2 : (2 * (Sized.size x + 1)) ^ M.k = 2 ^ M.k * (Sized.size x + 1) ^ M.k :=
    Nat.mul_pow 2 (Sized.size x + 1) M.k

  calc M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k
    _ ≤ M.C * (2 * (Sized.size x + 1)) ^ M.k := Nat.mul_le_mul_left M.C h1
    _ = M.C * (2 ^ M.k * (Sized.size x + 1) ^ M.k) := by rw [h2]
    _ = M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := (Nat.mul_assoc M.C _ _).symm

/-- Configs are equal when adapter encoding produces same tape as M's encoding. -/
theorem adapter_configs_eq
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (n + 128)) T)
    (c : Fin T) (x : LStarInstanceFG)
    (decodeWitness : (n : Nat) → Bits (n + 128) → Randomness) :
    initWithEncodingBase M.M (mkAdapterTMEncoding M decodeWitness).input (c, x) M.h_tape_pos M.h_blank_consistent =
    initWithEncodingBase M.M M.encoding.input (c, ⟨x.encodedφ.nvars, x⟩) M.h_tape_pos M.h_blank_consistent := by
  -- Both use the same encoding function: M.encoding.input.encode ⟨x.encodedφ.nvars, x⟩
  have h_encode_eq : (mkAdapterTMEncoding M decodeWitness).input.encode (c, x) =
                     M.encoding.input.encode (c, ⟨x.encodedφ.nvars, x⟩) := rfl
  -- The configs are equal because tapes are equal
  simp only [initWithEncodingBase, mkAdapterTMEncoding, adapterInputEncoding]

/-! ## Exponential Profile Adapter Functions

These are variants of the above for the TRUE exponential profile where
witness length is `expWLen n = 2n + 64` (with dgLen = n).

We use `EncodingDiscipline.expWLen` which is defined as `2 * n + 64`.
-/

/-- Input encoding adapter for exponential profile.
    Wraps LStarInstanceFG as Sigma type using encodedφ.nvars for the parameter.
-/
def adapterInputEncoding_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (EncodingDiscipline.expWLen n)) T)
    : TMInputEncodingBase (Fin T × LStarInstanceFG) (Fin M.alphabetSize) where
  blank := M.encoding.input.blank
  encode := fun (c, L) => M.encoding.input.encode (c, ⟨L.encodedφ.nvars, L⟩)
  min_support := fun (c, L) => M.encoding.input.min_support (c, ⟨L.encodedφ.nvars, L⟩)
  min_support_spec := fun (c, L) i => M.encoding.input.min_support_spec (c, ⟨L.encodedφ.nvars, L⟩) i
  finite_support := fun (c, L) => M.encoding.input.finite_support (c, ⟨L.encodedφ.nvars, L⟩)
  C_encode := 2 ^ M.encoding.input.k_encode * M.encoding.input.C_encode
  k_encode := M.encoding.input.k_encode
  size_bounded := fun (c, L) => by
    let n := L.encodedφ.nvars
    let k := M.encoding.input.k_encode
    let C_M := M.encoding.input.C_encode

    have h_base :
        M.encoding.input.min_support (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) ≤
          C_M * (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k :=
      M.encoding.input.size_bounded (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG))

    have h_n_le_sizeL : n ≤ Sized.size L := by
      have h_n_eq : n = L.n := by simpa [n] using L.h_n_eq_nvars.symm
      have : n ≤ L.dag.n := by simpa [h_n_eq] using L.dag_size_ge_n
      simpa using this

    have h_size_wrapped_le :
        Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1 ≤
          2 * (Sized.size (c, L) + 1) := by
      simp only [Sized.size, sizedProd, sizedSigma, sizedNat]
      simp only [Sized.size, sizedNat] at h_n_le_sizeL
      omega

    have h_pow_le :
        (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k ≤
          (2 * (Sized.size (c, L) + 1)) ^ k :=
      Nat.pow_le_pow_left h_size_wrapped_le k

    calc M.encoding.input.min_support (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG))
        ≤ C_M * (Sized.size (c, (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG)) + 1) ^ k := h_base
      _ ≤ C_M * (2 * (Sized.size (c, L) + 1)) ^ k := by
        apply Nat.mul_le_mul_left
        exact h_pow_le
      _ = C_M * (2 ^ k * (Sized.size (c, L) + 1) ^ k) := by
        simp [Nat.mul_pow]
      _ = (2 ^ k * C_M) * (Sized.size (c, L) + 1) ^ k := by ring

/-- Output decoding adapter template for exponential profile. -/
def mkAdapterOutputDecoding_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (EncodingDiscipline.expWLen n)) T)
    (decodeWitness : (n : Nat) → Bits (EncodingDiscipline.expWLen n) → Randomness)
    : TMOutputDecoding Randomness (Fin M.alphabetSize) where
  blank := M.encoding.output.blank
  decode := fun tape =>
    let sigma_result := M.encoding.output.decode tape
    decodeWitness sigma_result.1 sigma_result.2
  reads_finite := by
    obtain ⟨N, h_M_finite⟩ := M.encoding.output.reads_finite
    exact ⟨N, fun tape1 tape2 h_agree => by
      have h_eq := h_M_finite tape1 tape2 h_agree
      rw [h_eq]⟩

/-- TM encoding adapter template for exponential profile. -/
def mkAdapterTMEncoding_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (EncodingDiscipline.expWLen n)) T)
    (decodeWitness : (n : Nat) → Bits (EncodingDiscipline.expWLen n) → Randomness)
    : TMEncodingBase (Fin T × LStarInstanceFG) Randomness (Fin M.alphabetSize) where
  input := adapterInputEncoding_exp M
  output := mkAdapterOutputDecoding_exp M decodeWitness
  blank_consistent := M.encoding.blank_consistent

/-- Halting proof helper for exponential profile. -/
theorem adapter_halts_helper_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (EncodingDiscipline.expWLen n)) T)
    (x : LStarInstanceFG) :
    M.C * (Sized.size (⟨x.encodedφ.nvars, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k ≤
    M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := by
  let n := x.encodedφ.nvars
  have h_nvars_eq : n = x.n := x.h_n_eq_nvars.symm
  have h_dag_ge : x.dag.n ≥ x.n := x.dag_size_ge_n
  have h_nvars_le_dag : n ≤ x.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
  have h_size_x : Sized.size x = x.dag.n := rfl

  have h_sigma_size : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size x := by
    simp only [Sized.size, sizedSigma, sizedNat]

  have h_size_bound : Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size x + 1) := by
    rw [h_sigma_size, h_size_x]; omega

  calc M.C * (Sized.size (⟨n, x⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ M.k
    _ ≤ M.C * (2 * (Sized.size x + 1)) ^ M.k := by
        apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; exact h_size_bound
    _ = M.C * (2 ^ M.k * (Sized.size x + 1) ^ M.k) := by rw [Nat.mul_pow]
    _ = M.C * 2 ^ M.k * (Sized.size x + 1) ^ M.k := by ring

/-- Config equality lemma for exponential profile. -/
theorem adapter_configs_eq_exp
    {T : Nat}
    (M : RandAdv (Σ _n : Nat, LStarInstanceFG) (Σ n : Nat, Bits (EncodingDiscipline.expWLen n)) T)
    (c : Fin T) (x : LStarInstanceFG)
    (decodeWitness : (n : Nat) → Bits (EncodingDiscipline.expWLen n) → Randomness) :
    initWithEncodingBase M.M (mkAdapterTMEncoding_exp M decodeWitness).input (c, x) M.h_tape_pos M.h_blank_consistent =
    initWithEncodingBase M.M M.encoding.input (c, ⟨x.encodedφ.nvars, x⟩) M.h_tape_pos M.h_blank_consistent := by
  have h_encode_eq : (mkAdapterTMEncoding_exp M decodeWitness).input.encode (c, x) =
                     M.encoding.input.encode (c, ⟨x.encodedφ.nvars, x⟩) := rfl
  simp only [initWithEncodingBase, mkAdapterTMEncoding_exp, adapterInputEncoding_exp]

/-- FormatSeparated from early_decode property for exponential profile.

    This is the exponential profile version of formatSeparated_from_early_decode.
    Uses adapterInputEncoding_exp for EncodingDiscipline.expWLen witness type.
-/
theorem formatSeparated_from_early_decode_exp
  {T : Nat}
  (M : RandAdv (Sigma fun _n => LStarInstanceFG) (Sigma fun n => Bits (EncodingDiscipline.expWLen n)) T)
  (h_early_zero : M.early_decode_default.1 = 0)
  : EncodingDiscipline.FormatSeparated_exp M (adapterInputEncoding_exp M) M.h_blank_consistent := by
  intro c L t h_t
  -- Apply M.early_decode to the wrapped Sigma input with coin `c`.
  have h_ed := M.early_decode c ⟨L.encodedφ.nvars, L⟩ t h_t
  simp only [EncodingDiscipline.FormatSeparated_exp, adapterInputEncoding_exp] at *
  simp only [initWithEncodingBase, getTape0] at h_ed ⊢
  rw [h_ed, h_early_zero]

end LStar.Complexity.StructuralOWFBridgeCommon
