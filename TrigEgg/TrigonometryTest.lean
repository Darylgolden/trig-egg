
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Cast.Defs
import Egg

set_option profiler true
set_option egg.timeLimit 5

variable (x y : ℝ)
attribute [egg trig_rules]
  add_comm add_assoc add_left_comm
  add_zero zero_add
  mul_comm mul_assoc mul_left_comm
  mul_one one_mul
  left_distrib right_distrib
  sub_eq_add_neg
  add_neg_cancel
  add_neg_cancel_left add_neg_cancel_right
  neg_add_cancel_left neg_add_cancel_right
  neg_neg
  mul_zero zero_mul
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
  Real.two_mul_sin_mul_cos -- modification of TR8
  Real.two_mul_cos_mul_cos
  Real.two_mul_sin_mul_sin
  -- todo TR9

  Real.cos_add Real.sin_add Real.cos_sub Real.sin_sub -- addition formulae (TR10)

  Real.sin_two_mul Real.cos_two_mul Real.cos_two_mul' -- double angle (TR11)


  -- todo TR12 (tan add formulae)

  -- todo TR13 (tan mul formulae)
  Mathlib.Meta.NormNum.isRat_eq_true

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
  Eq.refl
  HAdd.hAdd
  HMul.hMul


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
lemma TR2i_test_2 : Real.sin (x) * Real.sin (y) / Real.cos (x) = Real.tan (x) :=
  by egg +trig_rules

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
