import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

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


example (x0: ℝ) (h: x0≠0): deriv (λ z ↦ 3/z^7) x0 = -21/x0^8 := by
  -- Rewrite the function in terms of powers
  have h1 : (λ z:ℝ ↦ 3 / z^7) = (λ z:ℝ ↦ 3 * z^(-7: ℤ)) := by
    --funext
    simp [div_eq_mul_inv, zpow_neg]
    rfl
  rw [h1]
  -- Differentiate using the power rule
  rw [deriv_const_mul]
  rw [deriv_zpow]
  ring_nf
  sorry
  sorry
  --simp [rpow_neg, mul_neg, mul_comm, h1]
  --llmstep ""
  -- field_simp
  -- ring_nf
  -- field_simp
  -- ring_nf
