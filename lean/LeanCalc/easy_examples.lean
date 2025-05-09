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

-- 242: y = e^x * (x^2 + 3)
example (x0 : ℝ) :
    deriv (λ x ↦ exp x * (x^2 + 3)) x0 = (exp x0) * x0^2 + (exp x0) * 2 * x0 + 3 * exp x0 := by
  rw [deriv_mul]
  rw [Real.deriv_exp]
  rw [deriv_add]
  rw [deriv_pow'']
  rw [deriv_const]
  ring_nf
  field_simp
  exact differentiableAt_id
  exact differentiableAt_pow 2
  exact differentiableAt_const 3
  exact differentiableAt_exp
  exact DifferentiableAt.add (differentiableAt_pow 2) (differentiableAt_const 3)

example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ cos (log x)) x0 = -sin (log x0) / x0 := by
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [Real.deriv_cos]
  rw [Real.deriv_log]
  ring
  exact Real.differentiableAt_cos
  exact Real.differentiableAt_log (ne_of_gt h)

-- 692: $y=\\sin ^{2}(2 x-1)$
example (x0 : ℝ) : deriv (λ x ↦ (sin (2 * x - 1))^2) x0 = 4 * sin (2 * x0 - 1) * cos (2 * x0 - 1) := by
  rw [deriv_pow'']
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [Real.deriv_sin]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const 1
  exact differentiableAt_sin
  exact DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const 1)
  exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const 1))

-- 707: $y=x^{3} \\log _{5} x$
example (x0 : ℝ) (hx : 0 < x0) : deriv (λ x ↦ x ^ 3 * (Real.log x / Real.log 5)) x0
  = 3 * x0 ^ 2 * Real.log x0 / Real.log 5 + x0 ^ 2 / Real.log 5 := by
  rw [deriv_mul]
  rw [deriv_pow]
  rw [deriv_div]
  rw [Real.deriv_log]
  rw [deriv_const]
  field_simp [hx]
  ring
  exact differentiableAt_log (ne_of_gt hx)
  exact differentiableAt_const (log 5)
  apply log_ne_zero.mpr (by norm_num)
  exact differentiableAt_pow 3
  exact DifferentiableAt.div (differentiableAt_log (ne_of_gt hx)) (differentiableAt_const (log 5)) (log_ne_zero.mpr (by norm_num))

example (x0 : ℝ) (hx : 0 < 5 * x0 + 2) :
  deriv (λ x ↦ (Real.log (5 * x + 2)) ^ 3) x0
  = 15 * (Real.log (5 * x0 + 2)) ^ 2 / (5 * x0 + 2) := by
  rw [deriv_pow'']
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact differentiableAt_log (ne_of_gt hx)
  exact DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)) (ne_of_gt hx)

example (x0 : ℝ) (hx : Real.cos (5 * x0) ≠ 0) :
  deriv (λ x ↦ Real.tan (5 * x)) x0
  = 5 / cos (5 * x0) ^ 2 := by
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [deriv_tan]
  rw [deriv_const_mul]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_tan.mpr hx
  exact DifferentiableAt.const_mul differentiableAt_id _
