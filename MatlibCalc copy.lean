import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Real


example (x0: ℝ): deriv (λ x ↦ 6 * x^3) x0 = 18 * x0^2 := by
  -- First, prove that the function x ↦ x^3 is differentiable at x0
  -- have h_diff : DifferentiableAt ℝ (λ x ↦ x^3) x0 := (hasDerivAt_pow 3 x0).differentiableAt
  -- Apply the constant multiple rule: (c * f)' = c * f'
  rw [deriv_const_mul]
  -- Apply the power rule: (x^n)' = n * x^(n - 1)
  rw [deriv_pow]
  -- Simplify the expression
  ring
  -- apply h_diff
  apply (hasDerivAt_pow 3 x0).differentiableAt
