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

example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ sin (2 * x) + 3 * sin (2 * x) * sin x) x0 = 2 * cos (2*x0) := by
  nth_rewrite 1 [deriv_add]
  nth_rewrite 1 [← Function.comp_def]
  nth_rewrite 1 [deriv_comp]
  nth_rewrite 1 [Real.deriv_sin]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 2 [← Function.comp_def]
  nth_rewrite 1 [deriv_comp]
  nth_rewrite 1 [Real.deriv_sin]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [Real.deriv_sin]

  exact differentiableAt_const _
  exact differentiableAt_id
  exact Real.differentiableAt_sin
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
  exact differentiableAt_const _
  exact DifferentiableAt.sin (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
  exact DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.sin (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))
  exact Real.differentiableAt_sin
  exact differentiableAt_const _
  exact differentiableAt_id
  exact Real.differentiableAt_sin
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
  exact DifferentiableAt.sin (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
  exact DifferentiableAt.mul (DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.sin (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))) (Real.differentiableAt_sin)

example (x: ℝ) (h_div_ne_zero: Real.exp (x) ≠ 0)(h_log_ne_zero: x ≠ 0) : deriv (λ x ↦ log x / exp x) x = (((1) / (x)) * (Real.exp (x)) - (Real.log (x)) * (Real.exp (x) * (1))) / (Real.exp (x))^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [Real.deriv_exp]
field_simp [h_div_ne_zero, h_log_ne_zero]
ring
exact Real.differentiableAt_log (h_log_ne_zero)
exact Real.differentiableAt_exp
exact h_div_ne_zero

example (x: ℝ) (h_div_ne_zero: Real.log ((5:ℝ)) ≠ 0)(h_log_ne_zero_1: x ≠ 0)(h_log_ne_zero_2: (5:ℝ) ≠ 0) : deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log 5)) x = (((3 * (x) ^ (2) * (1))) * ((Real.log (x) / Real.log ((5:ℝ))))) + (((x ^ 3)) * (((((1) / (x)) * (Real.log ((5:ℝ))) - (Real.log (x)) * ((0) / ((5:ℝ)))) / (Real.log ((5:ℝ)))^2))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero, h_log_ne_zero_1, h_log_ne_zero_2]
ring
exact Real.differentiableAt_log (h_log_ne_zero_2)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_2)
exact h_div_ne_zero
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_1)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_2)) (h_div_ne_zero)

example (x: ℝ) (h_tan_ne_zero: Real.cos (((5:ℝ)) * x) ≠ 0) : deriv (λ x ↦ Real.tan ((5:ℝ) * x)) x = ((0 * x) + (5:ℝ)) / (Real.cos ((5:ℝ) * x))^2 := by
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
field_simp [h_tan_ne_zero]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero)
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

example (x: ℝ) (h_log_ne_zero: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) + (((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * ((((0 * x) + (5:ℝ))) / ((5:ℝ) * x + (2:ℝ))))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2  [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero)) _

example (x: ℝ) (h_div_ne_zero: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) - ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * ((((0 * x) + (5:ℝ))) / ((5:ℝ) * x + (2:ℝ))))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero, h_log_ne_zero]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero)) _
exact h_div_ne_zero

example (x: ℝ)  (h_div_ne_zero: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_1: x ≠ 0) (h_log_ne_zero_2: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) + ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_div_ne_zero, h_log_ne_zero_1, h_log_ne_zero_2]
ring
exact Real.differentiableAt_log (h_log_ne_zero_2)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_1)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_2)
exact h_div_ne_zero
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_1)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_2)) (h_div_ne_zero)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_1)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_2)) (h_div_ne_zero))
