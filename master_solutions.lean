import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import «Calc4lean».LLMStep

open Real


/-
--------------------------------------------------------------------------
Remember the protocol to write a new solution
  - First check if the original problem is aligning properly with the formalization
    i.e -- Original Problem: y = """2{t^4} - 10{t^2} + 13t"""
           example (x0: ℝ): deriv (λ t ↦ """2*t^4 - 10*t^2 + 13*t""") x0 = 2*x0^3 + x0*(6*x0^2 - 10) - 10*x0 + 13 := by
    the text inside triple quotes should match
  - Figure out the formulas you would need to solve the derivative
  - Find that in the master file and apply those.
  - If you make partial progress in a problem, but stuck somewhere, mark them as sorry.
    Comment on the problem "TO BE CHECKED BY BINDU"
    I will take a look later.
--------------------------------------------------------------------------
-/


-- Polynomial Solution 1
-- Original Problem: f( x ) = 6{x^3} - 9x + 4
example (x0: ℝ): deriv (λ x ↦ 6*x^3 - 9*x + 4) x0 = 18*x0^2 - 9 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _

-- Polynomial Solution 2
-- Original Problem: y = 2{t^4} - 10{t^2} + 13t
example (x0: ℝ): deriv (λ t ↦ 2*t^4 - 10*t^2 + 13*t) x0 = 2*x0^3 + x0*(6*x0^2 - 10) - 10*x0 + 13 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_pow]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
  exact DifferentiableAt.const_mul differentiableAt_id _


-- Solution for exp and log and function of type f(x)*g(x)
-- Original Problem: f( x ) = e^x * ln(x)
example (x0 : ℝ) (h : 0 < x0) : deriv (fun x => exp x * log x) x0 = exp x0 / x0 + exp x0 * log x0 := by
  -- Apply the product rule
  rw [deriv_mul]
  -- Derivative of log(x), under the condition x > 0
  rw [Real.deriv_log]
  -- Simplify the resulting expression
  rw [Real.deriv_exp]
  ring
  exact differentiableAt_exp
  exact differentiableAt_log (ne_of_gt h)
