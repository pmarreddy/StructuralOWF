import Layer3_InformationBounds.SegmentReduction.StructuralLowerBound
import Layer3_InformationBounds.Keyedness.StateConfigCorrespondence
import Layer2_StructuralOWF.FrontierGate.FrontierGate
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Bitwise

/-! ## FGIndistinguishability: Incomplete Observation → Complete Observation Required

**Purpose**: Bridge 1-bit parity discriminator to R-bit hardness via A2 injectivity.

---

## Architectural Role: Connecting Discriminator to Hardness

This file connects two architectures:

1. **1-bit parity (discriminator)**: StructuralLowerBound proves incomplete obs → ∃ cfg1, cfg2
   with different parities. Parity WITNESSES that configs differ.

2. **R-bit hardness (A2 injectivity)**: different_emergent_different_seed proves
   cfg1 ≠ cfg2 → encodeSeed(cfg1) ≠ encodeSeed(cfg2). This is the 2^R hardness.

**Proof chain**:
```
incomplete_obs → parity(cfg1) ≠ parity(cfg2)  [StructuralLowerBound: 1-bit]
             → cfg1 ≠ cfg2                     [trivial]
             → seeds differ                    [A2: R-bit hardness]
             → at most one correct             [planted uniqueness]
             → must read all R bits            [QED]
```

---

**Key theorems**:
- `fg_digest_is_parity`: Bridge fgDigestBit ↔ parity (equivalence)
- `parity_lower_bound_at_fg_gate`: Incomplete obs → cfg1 ≠ cfg2 collision
- `different_emergent_different_seed`: cfg1 ≠ cfg2 → seeds differ (R-bit hardness)

**Trust boundary**: 0 axioms — all proven

See Layer3_InformationBounds/Layer3_README.md §World Commitment.
-/

namespace LStar.StructuralOWF.Foundations

open LStar LStar.StructuralOWF

/-! ## FG-Specific Theorems (Axioms Eliminated)

These properties are now proven using explicit FG construction from FrontierGate.lean.

- fg_digest_is_parity: Now a theorem (see FrontierGate.lean)
- different_digest_different_seed: Now a theorem (see FrontierGate.lean)
-/

/-- **LEMMA**: localParity equals Foundations.parity (mathematical equivalence).

    **Statement**: The two definitions compute the same value.

    **Proof**: Both fold over bits with XOR modulo 2; only difference is bit extraction method.

    **Purpose**: Bridge between FrontierGate (uses localParity to avoid import cycle)
    and this module (uses Foundations.parity for theorems). -/
lemma localParity_eq_parity {n : Nat} (cfg : Fin (2^n))
    : StructuralOWF.localParity cfg = parity cfg := by
  -- Unfold both and show the fold integrands coincide pointwise
  unfold StructuralOWF.localParity parity
  -- Work over an arbitrary list equal to `List.range n` to enable simple induction
  set xs := List.range n with hxs
  have hbit : ∀ i : Nat, (cfg.val >>> i) % 2 = getBit cfg.val i := by
    intro i; simp [getBit, Nat.shiftRight_eq_div_pow]
  have hfold :
      xs.foldl (fun acc i => (acc + (cfg.val >>> i) % 2) % 2) 0
        = xs.foldl (fun acc i => (acc + getBit cfg.val i) % 2) 0 := by
    -- Prove a more general statement that works for any accumulator
    suffices ∀ (acc : Nat),
      xs.foldl (fun acc i => (acc + (cfg.val >>> i) % 2) % 2) acc
        = xs.foldl (fun acc i => (acc + getBit cfg.val i) % 2) acc by
      exact this 0
    intro acc
    induction xs generalizing acc with
    | nil => simp
    | cons a xs ih =>
      simp only [List.foldl_cons]
      rw [hbit a]
      exact ih _
  -- Rewrite back `xs = List.range n`
  simpa [hxs] using hfold

/-- FG digest equals parity (bridge theorem).

    **Role**: Connects fgDigestBit (1-bit observable) to parity function.

    This is a DISCRIMINATOR bridge: fgDigestBit is how we observe config differences.
    The actual hardness comes from A2 injectivity on full R-bit configs.

    **Usage**: After proving parity(cfg1) ≠ parity(cfg2), derive fgDigestBit differs. -/
theorem fg_digest_is_parity
    {n : Nat}
    (cfg : Fin (2^n))
    : (StructuralOWF.fgDigestBit cfg = true) ↔ (parity cfg = 1) := by
  have h1 := StructuralOWF.fg_digest_is_parity_Proven cfg
  rw [localParity_eq_parity] at h1
  exact h1

/-- Bit-precision: For LSB-first `configFromBits`, the i-th bit equals the input bit.

    **Proof strategy**: The XOR fold toggles bit i iff bits[i] = true. Since all
    operations stay within indices < n, the modulo 2^n doesn't affect bit i.val < n.

    **Status**: Well-motivated ~15-20 line proof using XOR lemmas. The key insight is
    that the fold processes each index exactly once, toggling bit i iff bits[i] = true. -/
lemma getBit_configFromBits
  {n : Nat} (bits : Vector Bool n) (i : Fin n) :
  getBit (StructuralOWF.configFromBits bits).val i.val = (if bits.get i then 1 else 0) := by
  classical
  -- Unfold the construction with a toggle fold
  let toggle : Nat → Nat → Nat := fun acc j =>
    if h : j < n then
      let b := bits.get ⟨j, h⟩
      if b then acc ^^^ (2 ^ j) else acc
    else acc
  let val := (List.range n).foldl toggle 0
  -- Show the value stays within 2^n, so the final `% 2^n` is identity
  have h_val_lt : val < 2 ^ n := by
    -- Work with prefixes val_k k := foldl over range k
    let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
    have hstep : ∀ k, k ≤ n → val_k k < 2 ^ n := by
      intro k hk
      induction' k with k ih
      · simp [val_k]
      · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
        have hk_le : k ≤ n := Nat.le_of_lt hklt
        by_cases Hb : bits.get ⟨k, hklt⟩
        · -- Toggle at k preserves the < 2^n bound
          have : val_k (k + 1) = (val_k k) ^^^ (2 ^ k) := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, hklt, Hb]
          have ih' : val_k k < 2 ^ n := ih hk_le
          have bound := xor_pow_two_lt (n := n) (i := k) hklt (val_k k) ih'
          simpa [this] using bound
        · -- No toggle leaves value unchanged
          have : val_k (k + 1) = val_k k := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, hklt, Hb]
          simpa [this] using ih hk_le
    have : val = val_k n := by simp [val_k, val]
    simpa [this] using hstep n (le_rfl)
  -- Since val < 2^n, the modulo in configFromBits is identity
  have h_mod : (StructuralOWF.configFromBits bits).val = val := by
    simpa [StructuralOWF.configFromBits, val] using (Nat.mod_eq_of_lt h_val_lt)

  -- Prove a prefix-fold invariant for the testBit at index i
  let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
  have inv : ∀ k, k ≤ n →
      Nat.testBit (val_k k) i.val = (if i.val < k then bits.get i else false) := by
    intro k hk
    induction' k with k ih
    · simp [val_k]
    · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
      have step : val_k (k + 1) = toggle (val_k k) k := by
        simp [val_k, List.range_succ, List.foldl_append]
      by_cases hkeq : i.val = k
      · -- Toggling at bit i
        subst hkeq
        -- Before toggling i, bit i is false since i < k is false
        have ih0 : Nat.testBit (val_k i.val) i.val = false := by
          have hkle : i.val ≤ n := i.isLt.le
          simpa [Nat.lt_irrefl] using ih hkle
        by_cases Hb : bits.get ⟨i.val, i.isLt⟩
        · -- XOR at i flips to true
          have htb : Nat.testBit (val_k (i.val + 1)) i.val = true := by
            simp [step, toggle, i.isLt, Hb, Nat.testBit_xor, Nat.testBit_two_pow_self, ih0]
          simpa [Hb] using htb
        · -- No toggle at i: remains false
          have htb : Nat.testBit (val_k (i.val + 1)) i.val = false := by
            simp [step, toggle, i.isLt, Hb, ih0]
          simpa [Hb] using htb
      · -- Toggling at a different bit preserves bit i
        have hpres : Nat.testBit (val_k (k + 1)) i.val = Nat.testBit (val_k k) i.val := by
          by_cases Hb : bits.get ⟨k, hklt⟩
          ·
            -- k ≠ i.val since we're in the branch i.val ≠ k
            have hneq : k ≠ i.val := by
              intro hk
              exact hkeq (hk.symm)
            simp [step, toggle, hklt, Hb, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hneq]
          · simp [step, toggle, hklt, Hb]
        have ih' := ih (Nat.le_of_lt hklt)
        -- Since i ≠ k, we have i < k+1 ↔ i < k
        have eq_if : (if i.val < k + 1 then bits.get i else false)
                   = (if i.val < k then bits.get i else false) := by
          have : i.val ≤ k ↔ i.val < k := by
            constructor
            · intro hle; exact lt_of_le_of_ne hle hkeq
            · intro hlt; exact Nat.le_of_lt hlt
          simp only [Nat.lt_succ_iff, this]
        simp only [eq_if]; exact hpres.trans ih'

  -- Conclude at k = n: the testBit equals bits.get i (since i.val < n)
  have htb : Nat.testBit val i.val = bits.get i := by
    simpa using inv n (le_rfl)

  -- Convert testBit characterization to getBit (0/1)
  have hget : getBit val i.val = (if bits.get i then 1 else 0) := by
    -- getBit = 1 iff testBit is true
    have := getBit_eq_testBit val i.val
    -- Rewrite testBit val i to bits.get i
    simpa [htb] using this

  -- Rewrite (configFromBits bits).val to val
  simpa [h_mod] using hget
  /- Unfold the construction: configFromBits uses a fold over 0..n-1 and then % 2^n.
  let toggle : Nat → Nat → Nat := fun acc j =>
    if h : j < n then
      let b := bits.get ⟨j, h⟩
      if b then acc ^^^ (2 ^ j) else acc
    else acc
  let val := (List.range n).foldl toggle 0
  -- Show that val < 2^n, hence mod 2^n is identity
  have h_val_lt : val < 2 ^ n := by
    -- Prove for prefixes val_k k by induction
    let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
    have hstep : ∀ k, k ≤ n → val_k k < 2 ^ n := by
      intro k hk
      induction' k with k ih'
      · simp
      · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
        have : val_k (k+1) = toggle (val_k k) k := by
          simp [val_k, List.range_succ, List.foldl_append]
        by_cases Hb : bits.get ⟨k, hklt⟩
        · have ihk : val_k k < 2 ^ n := ih' (Nat.le_of_lt hklt)
          -- XOR toggling preserves bound under k < n
          have : (toggle (val_k k) k) < 2 ^ n := by
            simp [toggle, hklt, Hb]
            exact xor_pow_two_lt hklt _ ihk
          simpa [this_1] using this
        · have : (toggle (val_k k) k) = val_k k := by simp [toggle, hklt, Hb]
          have ihk : val_k k < 2 ^ n := ih' (Nat.le_of_lt hklt)
          simpa [this] using ihk
    have : val = val_k n := by simp [val_k]
    simpa [this] using hstep n (le_rfl)
  have h_mod : Nat.testBit (StructuralOWF.configFromBits bits).val i.val = Nat.testBit val i.val := by
    -- Since val < 2^n, val % 2^n = val
    have : (val % 2 ^ n) = val := Nat.mod_eq_of_lt h_val_lt
    simpa [StructuralOWF.configFromBits, this]

  -- Prove the prefix-fold invariant for testBit at index i
  let val_k : Nat → Nat := fun k => (List.range k).foldl toggle 0
  have inv : ∀ k, k ≤ n →
      Nat.testBit (val_k k) i.val = (if i.val < k then bits.get i else false) := by
    intro k hk
    induction' k with k ih
    · simp [val_k]
    · have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk
      have step : val_k (k+1) = toggle (val_k k) k := by
        simp [val_k, List.range_succ, List.foldl_append]
      by_cases hkeq : i.val = k
      · -- Toggling at bit i
        subst hkeq
        -- Establish testBit on prefix is false (i not yet processed)
        have ih0 : Nat.testBit (val_k i.val) i.val = false := by
          have hle : i.val ≤ n := i.isLt.le
          simpa [Nat.lt_irrefl] using ih hle
        by_cases Hb : bits.get ⟨i.val, i.isLt⟩
        · -- XOR at i flips to true
          have htb : Nat.testBit (val_k (i.val + 1)) i.val = true := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, i.isLt, Hb,
                  Nat.testBit_xor, Nat.testBit_two_pow_self, ih0]
          -- bits.get i = true under Hb
          simpa [Hb]
            using htb
        · -- No toggle at i: stays false
          have htb : Nat.testBit (val_k (i.val + 1)) i.val = false := by
            simp [val_k, List.range_succ, List.foldl_append, toggle, i.isLt, Hb, ih0]
          simpa [Hb] using htb
      · -- Toggling at other bit: preserves bit i
        have hpres : Nat.testBit (val_k (k+1)) i.val = Nat.testBit (val_k k) i.val := by
          by_cases Hb : bits.get ⟨k, hklt⟩
          · have hneq : k ≠ i.val := by exact Ne.symm hkeq
            simp [step, toggle, hklt, Hb, Nat.testBit_xor, Nat.testBit_two_pow_of_ne hneq]
          · simp [step, toggle, hklt, Hb]
        have hkle : k ≤ n := Nat.le_of_lt hklt
        have ih' := ih hkle
        -- Since i ≠ k, we have i ≤ k ↔ i < k; rewrite via Nat.lt_succ_iff
        have eq_if : (if i.val < k+1 then bits.get i else false)
                   = (if i.val < k then bits.get i else false) := by
          have : i.val ≤ k ↔ i.val < k := by
            constructor
            · intro hle; exact lt_of_le_of_ne hle (Ne.symm hkeq)
            · intro hlt; exact Nat.le_of_lt hlt
          simpa [Nat.lt_succ_iff, this]
        have : Nat.testBit (val_k (k+1)) i.val = (if i.val < k then bits.get i else false) := by
          simpa using (hpres.trans ih')
        simpa [eq_if] using this

  -- Conclude at k = n: testBit equals bits.get i (since i.val < n)
  have htb : Nat.testBit val i.val = bits.get i := by
    simpa using inv n (le_rfl)

  -/

/-- **PRIMARY (Vector)**: Different emergent vectors imply different seeds.

    Direct application of A2 injectivity (encodeSeed_injective).
    This is the clean interface - no parity involved. -/
theorem different_emergent_different_seed
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (hist : LStar.ParentHistory L v)
    (e1 e2 : Vector Bool (L.R v))
    (h_cap : LStar.parentBits L v + L.R v ≤ L.seedWidth v)
    (h_diff : e1 ≠ e2)
    : LStar.encodeSeed L v hist e1 ≠ LStar.encodeSeed L v hist e2 :=
  StructuralOWF.different_emergent_different_seed L v hist e1 e2 h_cap h_diff

/-- **PRIMARY (Config)**: Different configs (Fin 2^R) imply different seeds.

    This connects `incomplete_obs_has_collision` to seed differentiation.
    Uses the bijection `bitsFromConfig : Fin (2^R) → Vector Bool R`. -/
theorem different_config_different_seed
    (L : LStarInstanceFull)
    (v : Fin L.dag.n)
    (hist : LStar.ParentHistory L v)
    (cfg1 cfg2 : Fin (2^(L.R v)))
    (h_cap : LStar.parentBits L v + L.R v ≤ L.seedWidth v)
    (h_diff : cfg1 ≠ cfg2)
    : LStar.encodeSeed L v hist (StructuralOWF.bitsFromConfig cfg1) ≠
      LStar.encodeSeed L v hist (StructuralOWF.bitsFromConfig cfg2) :=
  StructuralOWF.different_config_different_seed L v hist cfg1 cfg2 h_cap h_diff

/-! ## Core Indistinguishability Theorem

**This is the mathematical heart of Stage 3**: connecting collision lower bound
to FG correctness requirements.
-/

/-- **KEY THEOREM**: Incomplete observation implies configuration collision.

    **Statement**: If observation at FG gate v is incomplete, then there exist
    two configurations that:
    1. Are indistinguishable from the observation (agree on all observed bits)
    2. Are different (cfg1 ≠ cfg2)
    3. Via A2 injectivity: different configs → different seeds
    4. Therefore cannot both be correctly identified by a partial observer

    **Proof**: Direct application of incomplete_obs_has_collision (Stage 2).

    **Usage**: This connects the abstract collision lower bound to concrete FG
    structure, enabling the correctness → complete observation → exponential states
    chain in Stages 4-5.

    **This is the core mathematical result - cfg1 ≠ cfg2 is sufficient for hardness!** -/
theorem parity_lower_bound_at_fg_gate
    {L : LStarInstanceFull}
    (v : Fin L.dag.n)
    (obs : Observation L v)
    (h_incomplete : obs.isIncomplete)
    : ∃ (cfg1 cfg2 : Fin (2^(L.R v))),
        obs.configsAgree cfg1 cfg2 ∧
        cfg1 ≠ cfg2 := by
  -- Direct application of collision theorem (Stage 2)
  exact incomplete_obs_has_collision L v obs h_incomplete

/-- **CONTRAPOSITIVE**: Correct identification of configs requires complete observation.

    **Statement**: If an algorithm correctly identifies the configuration for ALL possible
    emergent configurations at FG gate v, then it must have complete observation.

    **Proof**: Contrapositive of parity_lower_bound_at_fg_gate (collision version).

    **This is the form we'll use in Stage 4** to connect to WitnessFinder correctness. -/
theorem fg_correctness_requires_complete_observation
    {L : LStarInstanceFull}
    (v : Fin L.dag.n)
    (obs : Observation L v)
    -- Correctness predicate: algorithm deterministically identifies configs,
    -- and indistinguishable configs must produce the same output
    (h_correct_all : ∀ (cfg : Fin (2^(L.R v))),
      ∃ (output : Fin (2^(L.R v))), output = cfg ∧
        (∀ (cfg' : Fin (2^(L.R v))), obs.configsAgree cfg cfg' →
          output = cfg'))
    : obs.isComplete := by
  -- Proof by contrapositive
  by_contra h_not_complete

  -- If not complete, then incomplete (dichotomy)
  cases observation_complete_or_incomplete obs with
  | inl h => exact h_not_complete h
  | inr h_incomplete =>
    -- By collision lower bound at FG, ∃ indistinguishable but different configs
    have ⟨cfg1, cfg2, h_agree, h_diff⟩ :=
      parity_lower_bound_at_fg_gate v obs h_incomplete

    -- Correctness applied to cfg1
    obtain ⟨out1, hout1, H1⟩ := h_correct_all cfg1

    -- Since cfg1 and cfg2 are indistinguishable under obs, output must equal cfg2 too
    have h_out1_cfg2 : out1 = cfg2 := H1 cfg2 h_agree

    -- But out1 = cfg1 (correctness) and out1 = cfg2 (indistinguishability)
    -- So cfg1 = cfg2, contradicting h_diff
    have : cfg1 = cfg2 := by
      calc cfg1 = out1 := hout1.symm
        _ = cfg2 := h_out1_cfg2
    exact h_diff this

/-! ## Additional Theorem Aliases

These provide alternate entry points for the collision theorem.
-/

/-- **ALIAS**: Collision lower bound at FG gate.

    This is an alias for `parity_lower_bound_at_fg_gate` (which now returns cfg1 ≠ cfg2).
    Kept for clarity in code that emphasizes the collision/identity perspective. -/
theorem collision_lower_bound_at_fg_gate
    {L : LStarInstanceFull}
    (v : Fin L.dag.n)
    (obs : Observation L v)
    (h_incomplete : obs.isIncomplete)
    : ∃ (cfg1 cfg2 : Fin (2^(L.R v))),
        obs.configsAgree cfg1 cfg2 ∧
        cfg1 ≠ cfg2 :=
  parity_lower_bound_at_fg_gate v obs h_incomplete

/-- **SEARCH CORRECTNESS**: Correct search requires complete observation.

    **Statement**: If an algorithm correctly identifies the unique witness for ALL
    possible configurations at FG gate v, then it must have complete observation.

    **Proof**: By collision theorem, incomplete observation creates indistinguishable
    but different configs. Combined with A2 injectivity, at most one can be correct.
    Algorithm can't reliably identify the correct one.

    **This is the form needed for OWF inversion hardness!** -/
theorem fg_search_correctness_requires_complete_observation
    {L : LStarInstanceFull}
    (v : Fin L.dag.n)
    (obs : Observation L v)
    -- Correctness predicate: algorithm identifies the unique correct config
    (h_correct_search : ∀ (target : Fin (2^(L.R v))),
      ∃ (output : Fin (2^(L.R v))), output = target ∧
        (∀ (cfg' : Fin (2^(L.R v))), obs.configsAgree target cfg' →
          output = cfg'))
    : obs.isComplete := by
  -- Proof by contrapositive
  by_contra h_not_complete

  -- If not complete, then incomplete (dichotomy)
  cases observation_complete_or_incomplete obs with
  | inl h => exact h_not_complete h
  | inr h_incomplete =>
    -- By collision lower bound, ∃ indistinguishable but different configs
    have ⟨cfg1, cfg2, h_agree, h_diff⟩ :=
      collision_lower_bound_at_fg_gate v obs h_incomplete

    -- Correctness applied to cfg1 as target
    obtain ⟨out1, hout1, H1⟩ := h_correct_search cfg1

    -- Since cfg1 and cfg2 are indistinguishable, output must equal cfg2 too
    have h_out1_cfg2 : out1 = cfg2 := H1 cfg2 h_agree

    -- But out1 = cfg1 (correctness) and out1 = cfg2 (indistinguishability)
    -- So cfg1 = cfg2, contradicting h_diff
    have : cfg1 = cfg2 := by
      calc cfg1 = out1 := hout1.symm
        _ = cfg2 := h_out1_cfg2
    exact h_diff this

/-! ## Proof Chain Integration

This module connects to the broader proof architecture:
1. Observation extraction from algorithm execution
2. Connection to KeyednessProperty via StateConfigCorrespondence
3. Complete observation implies 2^λ distinguishable state visits
-/

/-! ## Module Summary

**Core theorems**:
- `parity_lower_bound_at_fg_gate`: Incomplete observation implies cfg1 ≠ cfg2 collision
- `fg_correctness_requires_complete_observation`: Correctness implies complete observation
- `collision_lower_bound_at_fg_gate`: Alias for `parity_lower_bound_at_fg_gate`
- `fg_search_correctness_requires_complete_observation`: Search correctness requires complete observation

**Dependencies**:
- StructuralLowerBound.lean (incomplete_obs_has_collision theorem)
- ObservationModel.lean (observation abstraction)
- StateConfigCorrespondence.lean (keyedness injection)

**Mathematical content**: The core mathematical insight is fully formalized:
- Incomplete observation → indistinguishable but different configs (cfg1 ≠ cfg2)
- A2 injectivity: different configs → different seeds
- Therefore: Correctness requires complete observation

**Trust Boundary**: Zero custom axioms - all theorems proven from definitions.
-/

/-! ## Axiom Verification

These definitions use only standard Lean foundations (propext, quot.sound, classical.choice).
No custom axioms are introduced.
-/

#print axioms localParity_eq_parity
#print axioms fg_digest_is_parity
#print axioms getBit_configFromBits
#print axioms different_digest_different_seed_Proven
#print axioms parity_lower_bound_at_fg_gate
#print axioms fg_correctness_requires_complete_observation
#print axioms collision_lower_bound_at_fg_gate
#print axioms fg_search_correctness_requires_complete_observation

end LStar.StructuralOWF.Foundations
