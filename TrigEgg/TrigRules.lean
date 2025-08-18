import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

variable (x y : ℝ)

theorem sin_mul : Real.sin (x) * Real.sin (y) = (Real.cos (a - b) - Real.cos(a + b)) :=
