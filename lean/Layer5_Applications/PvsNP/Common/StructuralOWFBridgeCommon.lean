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
The flat and QP profiles differ in:
1. Digest length: 64 bits (flat) vs (log₂ n)² bits (QP)
2. Plant function: plant_flat vs plant_n
3. OWF security theorem: f_is_one_way_exponential_flat vs owf_qp_security

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
    : TMInputEncodingBase LStarInstanceFG (Fin M.alphabetSize) where
  blank := M.encoding.input.blank
  encode := fun L => M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩
  min_support := fun L => M.encoding.input.min_support ⟨L.encodedφ.nvars, L⟩
  min_support_spec := fun L i => M.encoding.input.min_support_spec ⟨L.encodedφ.nvars, L⟩ i
  finite_support := fun L => M.encoding.input.finite_support ⟨L.encodedφ.nvars, L⟩
  C_encode := 2 ^ M.encoding.input.k_encode * M.encoding.input.C_encode
  k_encode := M.encoding.input.k_encode
  size_bounded := fun L => by
    -- Goal: min_support L ≤ (2^k * C_M) * (size L + 1)^k
    -- where min_support L = M.encoding.input.min_support ⟨φ.nvars, L⟩

    let n := L.encodedφ.nvars
    let k := M.encoding.input.k_encode
    let C_M := M.encoding.input.C_encode

    -- Step 1: M's size_bounded gives bound in terms of sigma size
    have h_M_bound : M.encoding.input.min_support ⟨n, L⟩ ≤ C_M * (Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ k :=
      M.encoding.input.size_bounded ⟨n, L⟩

    -- Step 2: Size relationships
    have h_nvars_eq : n = L.n := L.h_n_eq_nvars.symm
    have h_dag_ge : L.dag.n ≥ L.n := L.dag_size_ge_n
    have h_nvars_le_dag : n ≤ L.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
    have h_size_L : Sized.size L = L.dag.n := rfl

    have h_sigma_size : Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size L := by
      simp only [Sized.size, sizedSigma, sizedNat]

    -- Step 3: Sigma size + 1 ≤ 2 * (size L + 1)
    have h_size_bound : Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size L + 1) := by
      rw [h_sigma_size, h_size_L]; omega

    -- Step 4: Power inequality
    have h_pow_bound : (Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ k ≤ (2 * (Sized.size L + 1)) ^ k :=
      Nat.pow_le_pow_left h_size_bound k

    -- Step 5: Expand (2 * x)^k = 2^k * x^k
    have h_pow_expand : (2 * (Sized.size L + 1)) ^ k = 2 ^ k * (Sized.size L + 1) ^ k :=
      Nat.mul_pow 2 (Sized.size L + 1) k

    -- Step 6: Chain the inequalities
    calc M.encoding.input.min_support ⟨n, L⟩
      _ ≤ C_M * (Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ k := h_M_bound
      _ ≤ C_M * (2 * (Sized.size L + 1)) ^ k := Nat.mul_le_mul_left C_M h_pow_bound
      _ = C_M * (2 ^ k * (Sized.size L + 1) ^ k) := by rw [h_pow_expand]
      _ = 2 ^ k * C_M * (Sized.size L + 1) ^ k := by ring

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
  intro L t h_t
  -- Goal: (M.encoding.output.decode tape).1 = 0
  -- where tape = getTape0 cfg, cfg = step^[t] init_cfg
  -- and init_cfg = initWithEncodingBase M.M (adapterInputEncoding M) L ...

  -- Key: adapterInputEncoding L encodes L as M.encoding.input.encode ⟨φ.nvars, L⟩
  -- So init_cfg has the same tape as using M.encoding.input on ⟨φ.nvars, L⟩

  -- Apply M.early_decode to ⟨L.encodedφ.nvars, L⟩
  have h_ed := M.early_decode ⟨L.encodedφ.nvars, L⟩ t h_t

  -- h_ed : (let init_cfg := initWithEncodingBase M.M M.encoding.input ⟨φ.nvars, L⟩ ...
  --         let cfg := step^[t] init_cfg
  --         M.encoding.output.decode (getTape0 cfg M.h_tape_pos)) = M.early_decode_default

  -- The init_cfg in our goal uses adapterInputEncoding:
  -- tapes[0] = (adapterInputEncoding M).encode L = M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩
  -- This is definitionally equal to the init_cfg in h_ed!

  -- Show the init configs are equal by showing the tapes are equal
  have h_tape_eq : (adapterInputEncoding M).encode L = M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩ := rfl

  -- The blank symbols are the same
  have h_blank_eq : (adapterInputEncoding M).blank = M.encoding.input.blank := rfl

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
    : TMEncodingBase LStarInstanceFG Randomness (Fin M.alphabetSize) where
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
    (x : LStarInstanceFG)
    (decodeWitness : (n : Nat) → Bits (n + 128) → Randomness) :
    initWithEncodingBase M.M (mkAdapterTMEncoding M decodeWitness).input x M.h_tape_pos M.h_blank_consistent =
    initWithEncodingBase M.M M.encoding.input ⟨x.encodedφ.nvars, x⟩ M.h_tape_pos M.h_blank_consistent := by
  -- Both use the same encoding function: M.encoding.input.encode ⟨x.encodedφ.nvars, x⟩
  have h_encode_eq : (mkAdapterTMEncoding M decodeWitness).input.encode x =
                     M.encoding.input.encode ⟨x.encodedφ.nvars, x⟩ := rfl
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
    : TMInputEncodingBase LStarInstanceFG (Fin M.alphabetSize) where
  blank := M.encoding.input.blank
  encode := fun L => M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩
  min_support := fun L => M.encoding.input.min_support ⟨L.encodedφ.nvars, L⟩
  min_support_spec := fun L i => M.encoding.input.min_support_spec ⟨L.encodedφ.nvars, L⟩ i
  finite_support := fun L => M.encoding.input.finite_support ⟨L.encodedφ.nvars, L⟩
  C_encode := 2 ^ M.encoding.input.k_encode * M.encoding.input.C_encode
  k_encode := M.encoding.input.k_encode
  size_bounded := fun L => by
    let n := L.encodedφ.nvars
    let k := M.encoding.input.k_encode
    let C_M := M.encoding.input.C_encode

    have h_M_bound : M.encoding.input.min_support ⟨n, L⟩ ≤ C_M * (Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ k :=
      M.encoding.input.size_bounded ⟨n, L⟩

    have h_nvars_eq : n = L.n := L.h_n_eq_nvars.symm
    have h_dag_ge : L.dag.n ≥ L.n := L.dag_size_ge_n
    have h_nvars_le_dag : n ≤ L.dag.n := by rw [h_nvars_eq]; exact h_dag_ge
    have h_size_L : Sized.size L = L.dag.n := rfl

    have h_sigma_size : Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) = (n + 1) + Sized.size L := by
      simp only [Sized.size, sizedSigma, sizedNat]

    have h_size_bound : Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1 ≤ 2 * (Sized.size L + 1) := by
      rw [h_sigma_size, h_size_L]; omega

    calc M.encoding.input.min_support ⟨n, L⟩
      _ ≤ C_M * (Sized.size (⟨n, L⟩ : Sigma fun _ => LStarInstanceFG) + 1) ^ k := h_M_bound
      _ ≤ C_M * (2 * (Sized.size L + 1)) ^ k := by
          apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left; exact h_size_bound
      _ = C_M * (2 ^ k * (Sized.size L + 1) ^ k) := by rw [Nat.mul_pow]
      _ = (2 ^ k * C_M) * (Sized.size L + 1) ^ k := by ring

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
    : TMEncodingBase LStarInstanceFG Randomness (Fin M.alphabetSize) where
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
    (x : LStarInstanceFG)
    (decodeWitness : (n : Nat) → Bits (EncodingDiscipline.expWLen n) → Randomness) :
    initWithEncodingBase M.M (mkAdapterTMEncoding_exp M decodeWitness).input x M.h_tape_pos M.h_blank_consistent =
    initWithEncodingBase M.M M.encoding.input ⟨x.encodedφ.nvars, x⟩ M.h_tape_pos M.h_blank_consistent := by
  have h_encode_eq : (mkAdapterTMEncoding_exp M decodeWitness).input.encode x =
                     M.encoding.input.encode ⟨x.encodedφ.nvars, x⟩ := rfl
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
  intro L t h_t
  -- Apply M.early_decode to ⟨L.encodedφ.nvars, L⟩
  have h_ed := M.early_decode ⟨L.encodedφ.nvars, L⟩ t h_t
  -- Show the init configs are equal
  have h_tape_eq : (adapterInputEncoding_exp M).encode L = M.encoding.input.encode ⟨L.encodedφ.nvars, L⟩ := rfl
  have h_blank_eq : (adapterInputEncoding_exp M).blank = M.encoding.input.blank := rfl
  simp only [EncodingDiscipline.FormatSeparated_exp, adapterInputEncoding_exp] at *
  simp only [initWithEncodingBase, getTape0] at h_ed ⊢
  rw [h_ed, h_early_zero]

end LStar.Complexity.StructuralOWFBridgeCommon
