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
  sorry
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

example (x0 : ℝ) (h_ne_zero : 0 < x0^4 + 1) :
    deriv (λ x ↦ cos x / (x^4 + 1)) x0 = 1 / (cos x0)^2 := by
  nth_rewrite 1 [deriv_div]
  nth_rewrite 1 [Real.deriv_cos]
  nth_rewrite 1 [deriv_add]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [deriv_const]
  sorry
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact Real.differentiableAt_cos
  exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
  exact ne_of_gt (h_ne_zero)
