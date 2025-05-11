
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
open Real


example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)))) x = Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact Real.differentiableAt_sin
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)))) x = (-1) * Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact Real.differentiableAt_cos
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ))) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)))) x = (((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) / (Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ))))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_tan_ne_zero_1]
ring
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)))) x = Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact Real.differentiableAt_exp
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ))) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)))) x = (((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) / ((Real.exp x) * (x ^ 2 + (3:ℝ))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_1]
ring
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x))) x = Real.cos (Real.cos (Real.log x)) * ((-1) * Real.sin (Real.log x) * (1 / x)) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_5]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact Real.differentiableAt_sin
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x))) x = (-1) * Real.sin (Real.cos (Real.log x)) * ((-1) * Real.sin (Real.log x) * (1 / x)) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_5]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact Real.differentiableAt_cos
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x))) x = ((-1) * Real.sin (Real.log x) * (1 / x)) / (Real.cos (Real.cos (Real.log x)))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
-- field_simp [h_tan_ne_zero_1, h_log_ne_zero_5]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x))) x = Real.exp (Real.cos (Real.log x)) * ((-1) * Real.sin (Real.log x) * (1 / x)) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_5]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact Real.differentiableAt_exp
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x))) x = ((-1) * Real.sin (Real.log x) * (1 / x)) / (Real.cos (Real.log x)) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
-- field_simp [h_log_ne_zero_1, h_log_ne_zero_5]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_sin
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1) * Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ)))) / (Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_tan_ne_zero_1]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_exp
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ)))) / ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_1]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12]
ring
exact Real.differentiableAt_log (h_log_ne_zero_12)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_10)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)
exact h_div_ne_zero_9
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9)
exact Real.differentiableAt_sin
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9))

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1) * Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12]
ring
exact Real.differentiableAt_log (h_log_ne_zero_12)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_10)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)
exact h_div_ne_zero_9
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9)
exact Real.differentiableAt_cos
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9))

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) / (Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ))))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_tan_ne_zero_1, h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12]
ring
exact Real.differentiableAt_log (h_log_ne_zero_12)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_10)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)
exact h_div_ne_zero_9
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9)
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9))

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12]
ring
exact Real.differentiableAt_log (h_log_ne_zero_12)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_10)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)
exact h_div_ne_zero_9
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9)
exact Real.differentiableAt_exp
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9))

example (x: ℝ)  (h_log_ne_zero_1: ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) / ((x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_1, h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12]
ring
exact Real.differentiableAt_log (h_log_ne_zero_12)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_10)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)
exact h_div_ne_zero_9
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9)
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_10)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_12)) (h_div_ne_zero_9))

example (x: ℝ)  (h_log_ne_zero_5: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_5]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)
exact Real.differentiableAt_sin
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)) _

example (x: ℝ)  (h_log_ne_zero_5: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1) * Real.sin ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_5]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)
exact Real.differentiableAt_cos
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)) _

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_5: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) / (Real.cos ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
-- field_simp [h_tan_ne_zero_1, h_log_ne_zero_5]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)) _

example (x: ℝ)  (h_log_ne_zero_5: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_5]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)
exact Real.differentiableAt_exp
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)) _

example (x: ℝ)  (h_log_ne_zero_1: ((Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_5: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
-- field_simp [h_log_ne_zero_1, h_log_ne_zero_5]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_5)) _
