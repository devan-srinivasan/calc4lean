import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import «Calc4lean».LLMStep

open Real


example (x0: ℝ): deriv (λ x ↦ 6*x^3) x0 = 18*x0^2 := by
  --llmstep ""
  simp [deriv_const_mul, deriv_pow]
  ring
  --llmstep ""
  --sorry


example (x0: ℝ): deriv (λ x ↦ 6*x^3 + 4*x) x0 = 18*x0^2 + 4:= by
  --llmstep ""
  --simp [deriv_add, deriv_mul, deriv_pow]
  sorry

theorem h0_0 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  simp [deriv_add]
  rw [deriv_sub]
  simp [deriv_const_mul]
  rw [deriv_const_mul]
  simp [deriv_id]
  ring
  simp [differentiableAt_id]
  simpa using differentiableAt_id.const_mul 6
  dsimp only [HMul.hMul]
  simpa using differentiableAt_id.const_mul 9


theorem h0_1 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow 3
  exact DifferentiableAt.const_mul (differentiableAt_pow 3) 6
  exact DifferentiableAt.const_mul differentiableAt_id 9
  exact DifferentiableAt.sub (
    DifferentiableAt.const_mul (differentiableAt_pow 3) 6
    ) (
      DifferentiableAt.const_mul differentiableAt_id 9
    )
  exact differentiableAt_const 4


theorem h0_2 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  simp [deriv_add]
  rw [deriv_sub]
  simp [deriv_const_mul]
  rw [deriv_const_mul]
  simp [deriv_id'']
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul (differentiableAt_pow 3) 6
  exact DifferentiableAt.const_mul differentiableAt_id 9


example (x : ℝ) (h : 0 < x) : deriv (fun x => exp x * log x) x = exp x / x + exp x * log x := by
  -- Apply the product rule
  rw [deriv_mul]
  -- Derivative of log(x), under the condition x > 0
  rw [Real.deriv_log]
  -- Simplify the resulting expression
  rw [Real.deriv_exp]
  ring
  exact differentiableAt_exp
  exact differentiableAt_log (ne_of_gt h)
