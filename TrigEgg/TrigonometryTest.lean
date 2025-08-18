
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Geometry.Euclidean.Triangle
import Egg

set_option profiler true
set_option egg.timeLimit 5

variable (x y : ℝ)
attribute [egg trig_rules]
/- +     -/ add_comm add_assoc add_zero
/- -     -/ sub_zero zero_sub sub_self
/- *     -/ mul_comm mul_assoc mul_zero zero_mul mul_one
/- /     -/ div_one zero_div
/- + /   -/ add_div
/- * /   -/ mul_div_mul_left mul_div_mul_right mul_div_mul_comm div_mul_div_cancel
            _root_.div_mul_div_comm div_mul_eq_div_mul_one_div
/- + -   -/ sub_sub sub_add add_sub add_comm_sub sub_add_cancel sub_add_eq_add_sub add_sub_assoc
/- + * / -/ left_distrib right_distrib add_div_eq_mul_add_div
-- taken from lean-egg egg real basket
  -- todo: to add simp lemmas

  Real.tan_eq_sin_div_cos -- TR2
  Real.sin_neg Real.cos_neg Real.tan_neg
  Real.sin_antiperiodic Real.cos_antiperiodic Real.tan_periodic

  Real.sin_periodic Real.cos_periodic -- some parts of TR3

  Real.sin_zero Real.cos_zero Real.tan_zero -- TR4: special angles
  Real.sin_pi_div_six Real.cos_pi_div_six Real.tan_pi_div_six
  Real.sin_pi_div_four Real.cos_pi_div_four Real.tan_pi_div_four
  Real.sin_pi_div_three Real.cos_pi_div_three Real.tan_pi_div_three
  Real.sin_pi_div_two Real.cos_pi_div_two

  Real.sin_sq_eq_half_sub -- modification of TR5
  -- todo: cos^2 x = 1 - sin^2 x (TR6)
  -- todo: cos^2 x = (1 + cos(2x))/2 (TR7)


  Real.cos_sq_add_sin_sq
  -- Real.two_mul_sin_mul_cos -- modification of TR8
  -- Real.two_mul_cos_mul_cos
  -- Real.two_mul_sin_mul_sin

  -- TR9
  Real.sin_add_sin -- why isn't this imported???
  Real.sin_sub_sin
  Real.cos_add_cos
  Real.cos_sub_cos

  Real.cos_add Real.sin_add Real.cos_sub Real.sin_sub -- addition formulae (TR10)

  Real.sin_two_mul Real.cos_two_mul Real.cos_two_mul' -- double angle (TR11)


  -- TR12 (tan add formulae)
  Real.tan_add
  Real.tan_sub

  -- todo TR13 (tan mul formulae) (not in mathlib)


  -- constant folding attempt
  -- Mathlib.Meta.NormNum.isRat_eq_true
  -- Mathlib.Meta.NormNum.isRat_eq_true
  -- Mathlib.Meta.NormNum.isRat_add
  -- Mathlib.Meta.NormNum.isRat_div
  -- Mathlib.Meta.NormNum.isRat_mul
  -- Mathlib.Meta.NormNum.isRat_inv_pos
  -- Mathlib.Meta.NormNum.IsNat.to_isRat
  -- Mathlib.Meta.NormNum.isNat_ofNat
  -- Mathlib.Meta.NormNum.IsRat.to_isInt
  -- Mathlib.Meta.NormNum.IsInt.to_isNat
  -- Mathlib.Meta.NormNum.isNat_eq_true
  -- Eq.refl
  -- HAdd.hAdd
  -- HMul.hMul


-- extra rules: TR8
@[egg trig_rules]
theorem sin_mul : Real.sin (x) * Real.sin (y) = (Real.cos (x - y) - Real.cos (x + y)) / 2 :=
  by calc
    _ = (2 * Real.sin x * Real.sin y) / 2 := by ring
    _ = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by rw [Real.two_mul_sin_mul_sin]

@[egg trig_rules]
theorem cos_mul : Real.cos (x) * Real.cos (y) = (Real.cos (x - y) + Real.cos (x + y)) / 2 :=
  by calc
  _ = (2 * Real.cos x * Real.cos y) / 2 := by ring
  _ = (Real.cos (x - y) + Real.cos (x + y)) / 2 := by rw [Real.two_mul_cos_mul_cos]

@[egg trig_rules]
theorem sin_cos_mul : Real.sin (x) * Real.cos (y) = (Real.sin (x + y) + Real.sin (x - y)) / 2 :=
  by calc
  _ = (2 * Real.sin x * Real.cos y) / 2 := by ring
  _ = (Real.sin x * Real.cos y + Real.cos x * Real.sin y
    + (Real.sin x * Real.cos y - Real.cos x * Real.sin y)) / 2 := by ring
  _ = (Real.sin (x + y) + Real.sin (x - y)) / 2 := by rw [Real.sin_add, Real.sin_sub]

@[egg trig_rules]
theorem cos_sin_mul : Real.cos (x) * Real.sin (y) = (Real.sin (x + y) - Real.sin (x - y)) / 2 :=
  by calc
  _ = (2 * Real.cos x * Real.sin y) / 2 := by ring
  _ = (Real.sin x * Real.cos y + Real.cos x * Real.sin y
  - (Real.sin x * Real.cos y - Real.cos x * Real.sin y)) / 2 := by ring
  _ = (Real.sin (x + y) - Real.sin (x - y)) / 2 := by rw [Real.sin_add, Real.sin_sub]

-- rules: TR9


-- some basic examples

example : 0 = 0 := by
  egg

example : Real.sin (-x) = - Real.sin (x) :=
  by egg +trig_rules

example : Real.cos (-x) = Real.cos (x) :=
  by egg +trig_rules

example : Real.sin (-x) + Real.cos (-x) = - Real.sin (x) + Real.cos (x) :=
  by egg +trig_rules

-- example : Real.sin (-x) + Real.cos (-x) = Real.cos (x) - Real.sin (x) :=
--   by egg +trig_rules

example : Real.sin (-1) = - Real.sin (1) :=
  by egg +trig_rules

example : 1 + 1 = 2 :=
  by egg +trig_rules

example : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 :=
  by egg +trig_rules

example : 2 * Real.cos x ^ 2 + 2 * Real.sin x ^ 2 = 2 :=
  by egg +trig_rules

example (w y z k : ℝ) : x * y + x * z + w * y + w * z + k = (x + w) * (y + z) + k :=
  by egg +trig_rules

example (a b c d : ℝ) : a * b + a * c + d * b + d * c = (a + d) * (b + c) :=
  by egg +trig_rules

example : 2503 + 1023 = 3526 :=
  by egg

example : Real.sin ((2 : ℕ) + (1 : ℕ)) = Real.sin ((3 : ℕ)) :=
  by egg +trig_rules [Nat.cast_add]

set_option trace.egg.explanation.steps true
example : Real.sin (2) * Real.cos (1) + Real.cos (2) * Real.sin (1) =
 Real.sin (3) :=
  -- by egg +trig_rules
  by egg +trig_rules [Nat.cast_add, Semiring.toGrindSemiring_ofNat ℝ]

lemma TR2_test_1 : Real.tan x = Real.sin x / Real.cos x :=
  by egg +trig_rules

-- TR2 test 2 involves cotangent

lemma TR2_test_3 : Real.tan (Real.tan x - Real.sin x / Real.cos x) = 0 :=
  by egg +trig_rules

lemma TR2i_test_1 : Real.sin x / Real.cos x = Real.tan x :=
  by egg +trig_rules

set_option trace.egg.rewrites true
lemma TR2i_test_2 : Real.sin (x) * Real.sin (y) / Real.cos (x) = Real.tan (x) * Real.sin (y) :=
  by calc
  _ = (Real.sin (x) / Real.cos (x)) * Real.sin (y) := by calcify ring
  _ = Real.tan (x) * Real.sin (y) := by egg +trig_rules

example (n : Nat) : OfNat.ofNat (α := Real) n = (↑n : Real) := by
egg [Semiring.toGrindSemiring_ofNat]
#version


attribute [egg frac_add]
  Mathlib.Meta.NormNum.isRat_eq_true
  Mathlib.Meta.NormNum.isRat_add
  Mathlib.Meta.NormNum.isRat_div
  Mathlib.Meta.NormNum.isRat_mul
  Mathlib.Meta.NormNum.isRat_inv_pos
  Mathlib.Meta.NormNum.IsNat.to_isRat
  Mathlib.Meta.NormNum.isNat_ofNat
  Mathlib.Meta.NormNum.IsRat.to_isInt
  Mathlib.Meta.NormNum.IsInt.to_isNat
  Mathlib.Meta.NormNum.isNat_eq_true
  Int.ofNat
  Eq.refl
  HAdd.hAdd
  HMul.hMul
  instNatCastInt

set_option trace.egg.rewrites true
set_option egg.timeLimit 5
example : (1 : ℚ) / 2 + 1 / 2 = 1 := by
  -- egg +trig_rules [Nat.cast_add, Int.cast_add, Rat.cast_add, Mathlib.Meta.NormNum.isNat_ofNat ℚ]
  -- egg +frac_add [Nat.cast_add, Mathlib.Meta.NormNum.isNat_ofNat ℚ]
  -- add cast lemmas
  grind only
  -- calc
  --     1 / 2 + 1 / 2
  --     _ = 1 :=
  --       Mathlib.Meta.NormNum.isNat_eq_true
  --         (Mathlib.Meta.NormNum.IsInt.to_isNat
  --           (Mathlib.Meta.NormNum.IsRat.to_isInt
  --             (Mathlib.Meta.NormNum.isRat_add (Eq.refl HAdd.hAdd)
  --               (Mathlib.Meta.NormNum.isRat_div
  --                 (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
  --                   (Mathlib.Meta.NormNum.IsNat.to_isRat
  --                     (Mathlib.Meta.NormNum.isNat_ofNat ℚ (Eq.refl 1)))
  --                   (Mathlib.Meta.NormNum.isRat_inv_pos
  --                     (Mathlib.Meta.NormNum.IsNat.to_isRat
  --                       (Mathlib.Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2))))
  --                   (Eq.refl ((Int.ofNat 1).mul (Int.ofNat 1))) (Eq.refl 2)))
  --               (Mathlib.Meta.NormNum.isRat_div
  --                 (Mathlib.Meta.NormNum.isRat_mul (Eq.refl HMul.hMul)
  --                   (Mathlib.Meta.NormNum.IsNat.to_isRat
  --                     (Mathlib.Meta.NormNum.isNat_ofNat ℚ (Eq.refl 1)))
  --                   (Mathlib.Meta.NormNum.isRat_inv_pos
  --                     (Mathlib.Meta.NormNum.IsNat.to_isRat
  --                       (Mathlib.Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2))))
  --                   (Eq.refl ((Int.ofNat 1).mul (Int.ofNat 1))) (Eq.refl 2)))
  --               (Eq.refl (Int.ofNat 4)) (Eq.refl 4))))
  --         (Mathlib.Meta.NormNum.isNat_ofNat ℚ (Eq.refl 1))

example : (1 : ℚ) / 2 + 1 / 2 = 1 :=
  by norm_num
