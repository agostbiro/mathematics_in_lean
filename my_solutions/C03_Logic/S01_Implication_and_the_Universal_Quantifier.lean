import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry -- sorry means todo

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

-- my_lemma2 is now |x| < ε → |y| < ε → |x * y| < ε
#check my_lemma2 h₀ h₁
-- my_lemma2 is now |x * y| < ε
#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro
    x y ε
    epos -- 0 < ε
    ele1 -- ε ≤ 1
    xlt -- |x| < ε
    ylt -- |y| < ε
  sorry

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro
    x y ε
    epos -- 0 < ε
    ele1 -- ε ≤ 1
    xlt -- |x| < ε
    ylt -- |y| < ε
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul
    |x| * |y| ≤ |x| * ε := by
      -- Change the goal to proving that preconditions for the `mul_le_mul` theorem hold.
      -- `theorem mul_le_mul: a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d`
      apply mul_le_mul;
      -- Next we have to prove that the four preconditions for `mul_le_mul`
      -- hold:
      -- First, prove `|x| <= |x|` with the `linarith` tactic which will negate
      -- the inequality and tries to find a contraction. `|x| > |x|` is a
      -- contradiction, so it won't have to do much work.
      linarith;
      -- Second, prove `|y| <= ε`. The `linarith` tactic will look at the
      -- hypothesis from the context to find a contradiction. We have as a
      -- hypothesis that `|y| < ε`, so by assuming `|y| >= ε`, `linarith` will
      -- directly find a contradiction.
      linarith;
      -- Third, prove `0 <= |y|`. For this, we have to view the real numbers as
      -- an additive group and a lattice (which provides ordering). The absolute
      -- value of an element in this context is the greater of itself and its
      -- inverse, i.e. `|a| = max(a, a⁻¹)`.
      -- That `0 <= |a|` for some element `a`, can be proven by showing that
      -- `0 <= |a| + |a|`, and then using a theorem that says `0 <= a + a => 0 <= a`.
      -- We can prove `0 <= |a| + |a|` by noting that `|a| + |a| = max(|a| + a, |a| + a⁻¹)`
      -- and `|a| + a = max(a + a, a⁻¹ + a)`. With the `a⁻¹ + a` expression we get a
      -- `0` in the maxes, so we can rewrite our goal `0 <= |a| + |a|` as
      -- `0 <= max(..., 0, ...)`.
      apply abs_nonneg;
      -- Fourth, prove `0 <= |x|` the same way.
      apply abs_nonneg;
    |x| * ε < 1 * ε := by
      -- Cancel ε
      rw [mul_lt_mul_right epos]
      -- Conclude by contradiction that |x| < 1 by assuming the negation which
      -- contradicts the `ele1` and `xlt` hyptothesis.
      linarith
    1 * ε = ε := by
      apply one_mul

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  change f x + g x <= a + b
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  change a + b <= f x + g x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  change 0 <= f x * g x
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
    intro x
    change f x * g x <= a * b
    apply mul_le_mul
    apply hfa
    apply hgb
    apply nng
    apply nna

end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

-- More elegant proof term
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  change c * f a <= c * f b
  apply mul_le_mul_of_nonneg_left
  apply mf aleb
  apply nnc

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  change f (g a) <= f (g b)
  apply mf
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  change f x + g x = f (-x) + g (-x)
  rw [ef, eg]

example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  change f x * g x = f (-x) * g (-x)
  rw [of, og, neg_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  change f x * g x = -(f (-x) * g (-x))
  rw [ef, og, mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  change f (g x) = f (g (-x))
  rw [ef, og, neg_neg]

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

-- ∀ {x : α}, x ∈ s → x ∈ s
theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

-- a ⊆ b means ∀ {x : α}, x ∈ a → x ∈ b
-- The theorem thus expands to:
-- r ⊆ s → s ⊆ t → ∀ {x : α}, x ∈ r → x ∈ t
theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro -- hypotheses
    r_sub_s -- r ⊆ s: ∀ {x : α}, x ∈ r → x ∈ s
    s_sub_t -- s ⊆ t: ∀ {x : α}, x ∈ s → x ∈ t
    x       -- x : α
    x_member_r -- x ∈ r
  -- goal is to prove x ⊆ t based on the above hypotheses
  apply s_sub_t -- prove x ∈ t by proving x ∈ s
  apply r_sub_s -- prove x ∈ s by proving x ∈ r
  exact x_member_r -- we have x ∈ r as a hypothesis

-- The same proof can be written as a proof term in a functional style where the
-- hypotheses are arguments. The goal is again to prove x ⊆ t.
-- `(r_sub_s x_member_r)` means prove x ∈ s by applying the hypothesis x ∈ r to
-- the hypothesis r ⊆ s which expands to ∀ {x : α}, x ∈ r → x ∈ s.
-- `(s_sub_t _)` means prove x ∈ t using s ⊆ t by proving x ∈ s.
theorem Subset.trans_term : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun r_sub_s s_sub_t _x x_member_r ↦ s_sub_t (r_sub_s x_member_r)

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  -- fun x x_member_s ↦ le_trans (h x x_member_s) h'
  intro x x_member_s
  apply le_trans (h x x_member_s) h'

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry

end
