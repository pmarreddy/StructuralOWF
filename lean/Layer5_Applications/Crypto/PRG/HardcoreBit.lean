import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-! # Goldreich-Levin Hardcore Predicate

The inner product mod 2, `⟨x, r⟩ = (Σᵢ xᵢ·rᵢ) mod 2`, is a hardcore predicate
for any one-way function: given f(x) and r, no PPT adversary can predict ⟨x,r⟩
with non-negligible advantage.

**Reference**: Goldreich-Levin (1989)
-/

namespace LStar.Crypto.PRG

/-! ### Basic Bit Operations -/

/-- XOR of two booleans. -/
@[inline] def xorBool (a b : Bool) : Bool := a != b

/-- AND of two booleans. -/
@[inline] def andBool (a b : Bool) : Bool := a && b

/-! ### XOR Properties -/

@[simp] theorem xorBool_false_left (b : Bool) : xorBool false b = b := by
  cases b <;> rfl

@[simp] theorem xorBool_false_right (b : Bool) : xorBool b false = b := by
  cases b <;> rfl

@[simp] theorem xorBool_self (b : Bool) : xorBool b b = false := by
  cases b <;> rfl

theorem xorBool_comm (a b : Bool) : xorBool a b = xorBool b a := by
  cases a <;> cases b <;> rfl

theorem xorBool_assoc (a b c : Bool) : xorBool (xorBool a b) c = xorBool a (xorBool b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ### AND Properties -/

@[simp] theorem andBool_false_left (b : Bool) : andBool false b = false := rfl

@[simp] theorem andBool_false_right (b : Bool) : andBool b false = false := by
  cases b <;> rfl

theorem andBool_comm (a b : Bool) : andBool a b = andBool b a := by
  cases a <;> cases b <;> rfl

/-! ### Inner Product mod 2 -/

/-- Inner product mod 2: ⟨x, r⟩ = (Σᵢ xᵢ·rᵢ) mod 2. Uses common prefix if lengths differ. -/
def innerProd (x r : List Bool) : Bool :=
  (x.zip r).foldl (fun acc (a, b) => xorBool acc (andBool a b)) false

/-- Inner product for fixed-length vectors. -/
def innerProdVec {n : Nat} (x r : Vector Bool n) : Bool :=
  innerProd x.toList r.toList

/-- Inner product for Fin-indexed functions. -/
def innerProdFin (n : Nat) (x r : Fin n → Bool) : Bool :=
  (List.finRange n).foldl (fun acc i => xorBool acc (andBool (x i) (r i))) false

theorem foldl_xor_swap (l : List (Bool × Bool)) (init : Bool) :
    l.foldl (fun acc (a, b) => xorBool acc (andBool a b)) init =
    l.foldl (fun acc (a, b) => xorBool acc (andBool b a)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [andBool_comm]
    exact ih _

/-! ### Basic Properties -/

/-- Inner product with empty list is false. -/
@[simp] theorem innerProd_nil_left (r : List Bool) : innerProd [] r = false := by
  unfold innerProd
  simp

@[simp] theorem innerProd_nil_right (x : List Bool) : innerProd x [] = false := by
  unfold innerProd
  simp

/-- Inner product is commutative. -/
theorem innerProd_comm (x r : List Bool) : innerProd x r = innerProd r x := by
  induction x generalizing r with
  | nil => simp
  | cons a as ih =>
    cases r with
    | nil => simp
    | cons b bs =>
      unfold innerProd
      simp only [List.zip_cons_cons, List.foldl_cons]
      unfold innerProd at ih
      -- Need to show: foldl with (false xor (a && b)) on (as.zip bs)
      --             = foldl with (false xor (b && a)) on (bs.zip as)
      rw [andBool_comm a b]
      -- Now show the folds are equal
      have h_swap : ∀ (l₁ l₂ : List Bool) (init : Bool),
          (l₁.zip l₂).foldl (fun acc (p : Bool × Bool) => xorBool acc (andBool p.1 p.2)) init =
          (l₂.zip l₁).foldl (fun acc (p : Bool × Bool) => xorBool acc (andBool p.1 p.2)) init := by
        intro l₁ l₂ init
        induction l₁ generalizing l₂ init with
        | nil => simp
        | cons x xs ih_inner =>
          cases l₂ with
          | nil => simp
          | cons y ys =>
            simp only [List.zip_cons_cons, List.foldl_cons]
            rw [andBool_comm x y]
            exact ih_inner ys _
      exact h_swap as bs _

/-- Cons lemma for inner product. -/
theorem innerProd_cons (a b : Bool) (x r : List Bool) :
    innerProd (a :: x) (b :: r) = xorBool (andBool a b) (innerProd x r) := by
  unfold innerProd
  simp only [List.zip_cons_cons, List.foldl_cons]
  -- Need: foldl f (xorBool false (andBool a b)) (x.zip r) = xorBool (andBool a b) (foldl f false (x.zip r))
  -- where f = fun acc (p : Bool × Bool) => xorBool acc (andBool p.1 p.2)
  rw [xorBool_false_left]
  -- Now: foldl f (andBool a b) (x.zip r) = xorBool (andBool a b) (foldl f false (x.zip r))
  -- This follows from: foldl (xor) init l = xor init (foldl (xor) false l)
  have h_foldl_init : ∀ (l : List (Bool × Bool)) (init : Bool),
      l.foldl (fun acc (p : Bool × Bool) => xorBool acc (andBool p.1 p.2)) init =
      xorBool init (l.foldl (fun acc (p : Bool × Bool) => xorBool acc (andBool p.1 p.2)) false) := by
    intro l init
    induction l generalizing init with
    | nil => simp [xorBool_false_right]
    | cons hd tl ih =>
      simp only [List.foldl_cons, xorBool_false_left]
      rw [ih, ih (andBool hd.1 hd.2)]
      rw [xorBool_assoc]
  exact h_foldl_init (x.zip r) (andBool a b)

/-- Inner product with all-false list is false. -/
@[simp] theorem innerProd_zeros (n : Nat) (r : List Bool) :
    innerProd (List.replicate n false) r = false := by
  induction n generalizing r with
  | zero => simp [innerProd]
  | succ k ih =>
    cases r with
    | nil => simp [innerProd]
    | cons b bs =>
      rw [List.replicate_succ, innerProd_cons]
      simp [andBool, ih bs]

/-- Inner product distributes over XOR in second argument. -/
theorem innerProd_xor_right (x r₁ r₂ : List Bool)
    (h_len : r₁.length = r₂.length) :
    innerProd x (List.zipWith xorBool r₁ r₂) =
    xorBool (innerProd x r₁) (innerProd x r₂) := by
  induction x generalizing r₁ r₂ with
  | nil => simp
  | cons a xs ih =>
    cases r₁ with
    | nil =>
      -- h_len : 0 = r₂.length means r₂ = []
      cases r₂ with
      | nil => simp
      | cons _ _ => simp at h_len
    | cons b₁ bs₁ =>
      cases r₂ with
      | nil => simp at h_len
      | cons b₂ bs₂ =>
        simp only [List.length_cons, Nat.succ.injEq] at h_len
        simp only [List.zipWith_cons_cons]
        rw [innerProd_cons, innerProd_cons, innerProd_cons]
        rw [ih bs₁ bs₂ h_len]
        -- Now prove: xorBool (andBool a (xorBool b₁ b₂)) (xorBool (innerProd xs bs₁) (innerProd xs bs₂))
        --          = xorBool (xorBool (andBool a b₁) (innerProd xs bs₁))
        --                   (xorBool (andBool a b₂) (innerProd xs bs₂))
        -- Using distributivity of AND over XOR: a && (b₁ xor b₂) = (a && b₁) xor (a && b₂)
        have and_xor_distrib : andBool a (xorBool b₁ b₂) = xorBool (andBool a b₁) (andBool a b₂) := by
          cases a <;> cases b₁ <;> cases b₂ <;> rfl
        rw [and_xor_distrib]
        -- Now rearrange the xors using associativity and commutativity
        rw [xorBool_assoc, xorBool_assoc]
        congr 1
        rw [← xorBool_assoc (andBool a b₂), xorBool_comm (andBool a b₂), xorBool_assoc]

/-- Inner product distributes over XOR in first argument. -/
theorem innerProd_xor_left (x₁ x₂ r : List Bool)
    (h_len : x₁.length = x₂.length) :
    innerProd (List.zipWith xorBool x₁ x₂) r =
    xorBool (innerProd x₁ r) (innerProd x₂ r) := by
  rw [innerProd_comm, innerProd_comm x₁, innerProd_comm x₂]
  -- Need to show zipWith xorBool commutes with the arguments properly
  have h : List.zipWith xorBool x₁ x₂ = List.zipWith xorBool x₂ x₁ := by
    induction x₁ generalizing x₂ with
    | nil => simp
    | cons a as ih =>
      cases x₂ with
      | nil => simp
      | cons b bs =>
        simp only [List.length_cons, Nat.succ.injEq] at h_len
        simp only [List.zipWith_cons_cons]
        rw [xorBool_comm a b, ih bs h_len]
  rw [h]
  rw [innerProd_xor_right r x₂ x₁ h_len.symm]
  rw [xorBool_comm]

/-! ### Goldreich-Levin Hardcore Bit -/

/-- The GL hardcore bit: gl(x, r) := ⟨x, r⟩ mod 2. -/
def gl_hardcore (x r : List Bool) : Bool := innerProd x r

/-- GL hardcore bit for vectors. -/
def gl_hardcoreVec {n : Nat} (x r : Vector Bool n) : Bool :=
  innerProdVec x r

/-- GL hardcore bit for Fin-indexed functions. -/
def gl_hardcoreFin (n : Nat) (x r : Fin n → Bool) : Bool :=
  innerProdFin n x r

/-! ### Self-Correction via Linearity -/

/-- XOR cancellation: (r ⊕ s) ⊕ s = r. -/
theorem zipWith_xor_cancel (r s : List Bool) (h_len : r.length = s.length) :
    List.zipWith xorBool (List.zipWith xorBool r s) s = r := by
  induction r generalizing s with
  | nil =>
    cases s with
    | nil => rfl
    | cons _ _ => simp at h_len
  | cons a as ih =>
    cases s with
    | nil => simp at h_len
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h_len
      simp only [List.zipWith_cons_cons, List.cons.injEq]
      constructor
      · -- (a xor b) xor b = a
        cases a <;> cases b <;> rfl
      · exact ih bs h_len

/-- Self-correction: ⟨x, r⟩ = ⟨x, r ⊕ s⟩ ⊕ ⟨x, s⟩. Enables noisy-to-exact predictor conversion. -/
theorem gl_self_correction (x r s : List Bool)
    (h_len_r : r.length = x.length) (h_len_s : s.length = x.length) :
    gl_hardcore x r =
    xorBool (gl_hardcore x (List.zipWith xorBool r s)) (gl_hardcore x s) := by
  unfold gl_hardcore
  -- By linearity: ⟨x, r⊕s⟩ ⊕ ⟨x, s⟩ = ⟨x, (r⊕s)⊕s⟩ = ⟨x, r⟩
  have h_len_rs : (List.zipWith xorBool r s).length = s.length := by
    simp [h_len_r, h_len_s]
  rw [← innerProd_xor_right x (List.zipWith xorBool r s) s h_len_rs]
  congr 1
  exact (zipWith_xor_cancel r s (h_len_r.trans h_len_s.symm)).symm

end LStar.Crypto.PRG
