
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp

open Real

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  116 * x - 56 * x ^ 2 + 9 * x ^ 3) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  116 - 112 * x + 27 * x ^ 2 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  112 + 54 * x := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_const _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    