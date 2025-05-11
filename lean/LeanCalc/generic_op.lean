
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


example (x: ℝ)  (h_log_ne_zero_14: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) + -Real.sin (Real.log x) * (1 / x) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_14]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_14))

example (x: ℝ)  (h_log_ne_zero_14: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) - (-Real.sin (Real.log x) * (1 / x)) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_14]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_14))

example (x: ℝ)  (h_log_ne_zero_14: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * (Real.cos (Real.log x))) + (((Real.exp x) * (x ^ 2 + (3:ℝ))) * (-Real.sin (Real.log x) * (1 / x))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_log_ne_zero_14]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_14))

example (x: ℝ)  (h_div_ne_zero_1: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_14: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * (Real.cos (Real.log x)) - ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (-Real.sin (Real.log x) * (1 / x))) / (Real.cos (Real.log x))^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
field_simp [h_div_ne_zero_1, h_log_ne_zero_14]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_14))
exact h_div_ne_zero_1

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) + 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2 [← Function.comp_def]
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
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) - (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2 [← Function.comp_def]
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
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) + (((Real.exp x) * (x ^ 2 + (3:ℝ))) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2 [← Function.comp_def]
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
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) - ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)))) / ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)^2 := by
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
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_1]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact h_div_ne_zero_1

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) + ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
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
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18))

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) - (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [deriv_sub]
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
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18))

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * (x ^ 3)) + (((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + (((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact differentiableAt_pow _
exact DifferentiableAt.mul (DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))) (differentiableAt_pow _)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)

example (x: ℝ)  (h_div_ne_zero_2: (x ^ 3) ≠ 0) (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * (x ^ 3) - ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * x ^ 2)) / (x ^ 3)^2) * (Real.log x / Real.log (5:ℝ))) + (((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_2, h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact differentiableAt_pow _
exact h_div_ne_zero_2
exact DifferentiableAt.div (DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))) (differentiableAt_pow _) (h_div_ne_zero_2)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) + 3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))) := by
nth_rewrite 1 [deriv_add]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x)) - (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [deriv_sub]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) + (((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) := by
nth_rewrite 1 [deriv_mul]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((Real.exp x) * (x ^ 2 + (3:ℝ))) + ((Real.exp x) * (2 * x))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) - ((Real.exp x) * (x ^ 2 + (3:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)^2 := by
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
field_simp [h_div_ne_zero_1, h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _
exact h_div_ne_zero_1

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = -Real.sin (Real.log x) * (1 / x) + 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = -Real.sin (Real.log x) * (1 / x) - (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((-Real.sin (Real.log x) * (1 / x)) * ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) + ((Real.cos (Real.log x)) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = ((-Real.sin (Real.log x) * (1 / x)) * ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) - (Real.cos (Real.log x)) * (2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)))) / ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_div_ne_zero_1, h_log_ne_zero_4]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact h_div_ne_zero_1

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_12: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_13: x ≠ 0) (h_log_ne_zero_15: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = -Real.sin (Real.log x) * (1 / x) + ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4, h_div_ne_zero_12, h_log_ne_zero_13, h_log_ne_zero_15]
ring
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_13)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)
exact h_div_ne_zero_12
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12))

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_12: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_13: x ≠ 0) (h_log_ne_zero_15: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = -Real.sin (Real.log x) * (1 / x) - (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4, h_div_ne_zero_12, h_log_ne_zero_13, h_log_ne_zero_15]
ring
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_13)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)
exact h_div_ne_zero_12
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12))

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_12: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_13: x ≠ 0) (h_log_ne_zero_15: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((-Real.sin (Real.log x) * (1 / x)) * (x ^ 3)) + ((Real.cos (Real.log x)) * (3 * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_5, h_div_ne_zero_12, h_log_ne_zero_13, h_log_ne_zero_15]
ring
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_13)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)
exact h_div_ne_zero_12
exact differentiableAt_id
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))
exact differentiableAt_pow _
exact DifferentiableAt.mul (DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))) (differentiableAt_pow _)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12)

example (x: ℝ)  (h_div_ne_zero_2: (x ^ 3) ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_12: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_13: x ≠ 0) (h_log_ne_zero_15: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((-Real.sin (Real.log x) * (1 / x)) * (x ^ 3) - (Real.cos (Real.log x)) * (3 * x ^ 2)) / (x ^ 3)^2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_2, h_log_ne_zero_5, h_div_ne_zero_12, h_log_ne_zero_13, h_log_ne_zero_15]
ring
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_13)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)
exact h_div_ne_zero_12
exact differentiableAt_id
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))
exact differentiableAt_pow _
exact h_div_ne_zero_2
exact DifferentiableAt.div (DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))) (differentiableAt_pow _) (h_div_ne_zero_2)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_13)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_15)) (h_div_ne_zero_12)

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_8: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = -Real.sin (Real.log x) * (1 / x) + 3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4, h_log_ne_zero_8]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_8)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)) _

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_8: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = -Real.sin (Real.log x) * (1 / x) - (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4, h_log_ne_zero_8]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_8)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)) _

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_8: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((-Real.sin (Real.log x) * (1 / x)) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) + ((Real.cos (Real.log x)) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_log_ne_zero_4, h_log_ne_zero_8]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_8)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_8: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((-Real.sin (Real.log x) * (1 / x)) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) - (Real.cos (Real.log x)) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
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
field_simp [h_div_ne_zero_1, h_log_ne_zero_4, h_log_ne_zero_8]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_8)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_4)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_4))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_8)) _
exact h_div_ne_zero_1

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) + ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18))

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) - (((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18))

example (x: ℝ)  (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) * (x ^ 3)) + (((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (3 * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + (((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact differentiableAt_pow _
exact DifferentiableAt.mul (DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _) (differentiableAt_pow _)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)

example (x: ℝ)  (h_div_ne_zero_2: (x ^ 3) ≠ 0) (h_div_ne_zero_18: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_19: x ≠ 0) (h_log_ne_zero_21: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = ((((2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) * (x ^ 3) - ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (3 * x ^ 2)) / (x ^ 3)^2) * (Real.log x / Real.log (5:ℝ))) + (((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3)) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_2, h_div_ne_zero_18, h_log_ne_zero_19, h_log_ne_zero_21]
ring
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)
exact h_div_ne_zero_18
exact differentiableAt_id
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact differentiableAt_pow _
exact h_div_ne_zero_2
exact DifferentiableAt.div (DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _) (differentiableAt_pow _) (h_div_ne_zero_2)
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_19)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_21)) (h_div_ne_zero_18)

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) + 3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0)) - (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) + (((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
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
field_simp [h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_14: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * ((0 * x) + (2:ℝ) - 0))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) - ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
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
field_simp [h_div_ne_zero_1, h_log_ne_zero_14]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_14)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_14)) _
exact h_div_ne_zero_1

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) + 3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))) := by
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
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
field_simp [h_div_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_15]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)
exact Real.differentiableAt_log (h_log_ne_zero_11)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_9)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)
exact h_div_ne_zero_8
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)) _

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2)) - (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ)))) := by
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
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
field_simp [h_div_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_15]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)
exact Real.differentiableAt_log (h_log_ne_zero_11)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_9)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)
exact h_div_ne_zero_8
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)) _

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) := by
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
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
field_simp [h_div_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_15]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)
exact Real.differentiableAt_log (h_log_ne_zero_11)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_9)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)
exact h_div_ne_zero_8
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)) _

example (x: ℝ)  (h_div_ne_zero_1: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = ((((3 * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * (((1 / x) * (Real.log (5:ℝ)) - (Real.log x) * (0 / (5:ℝ))) / (Real.log (5:ℝ))^2))) * ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) - ((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * (3 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 2 * (((0 * x) + (5:ℝ)) / ((5:ℝ) * x + (2:ℝ))))) / ((Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)^2 := by
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
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
field_simp [h_div_ne_zero_1, h_div_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_15]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_15)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)
exact Real.differentiableAt_log (h_log_ne_zero_11)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_9)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)
exact h_div_ne_zero_8
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8)
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_9)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_11)) (h_div_ne_zero_8))
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_15)) _
exact h_div_ne_zero_1
