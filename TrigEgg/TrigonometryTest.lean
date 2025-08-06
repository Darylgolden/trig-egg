
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Egg

variable (x : ℝ)

example : 0 = 0 := by
  egg

example : Real.sin (-x) = - Real.sin (x) :=
  by egg [Real.sin_neg, Real.cos_neg]

example : Real.cos (-x) = Real.cos (x) :=
  by egg [Real.sin_neg, Real.cos_neg]

example : Real.sin (-x) + Real.cos (-x) = - Real.sin (x) + Real.cos (x) :=
  by egg [Real.sin_neg, Real.cos_neg]

example : Real.sin (-x) + Real.cos (-x) = Real.cos (x) - Real.sin (x) :=
  by egg [Real.sin_neg, Real.cos_neg, neg_add_eq_sub]

example : Real.sin (-1) = - Real.sin (1) :=
  by egg [Real.sin_neg, Real.cos_neg, neg_add_eq_sub]
