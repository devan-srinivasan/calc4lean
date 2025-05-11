
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 256) (Icc (2: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 32 * x + 256
  let D := Icc (2: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 80 * x + 3200) (Icc (8: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 80 * x + 3200
  let D := Icc (8: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (14: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 1152) (Icc (4: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 1152
  let D := Icc (4: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 108 * x + 1944) (Icc (6: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 108 * x + 1944
  let D := Icc (6: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 16 * x + 40) (Icc (1: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 16 * x + 40
  let D := Icc (1: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 56 * x + 1568) (Icc (7: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 56 * x + 1568
  let D := Icc (7: ℝ) (17: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (17: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 28) (Icc (2: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 28 * x + 28
  let D := Icc (2: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 384) (Icc (4: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 384
  let D := Icc (4: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 1152) (Icc (6: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 48 * x + 1152
  let D := Icc (6: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (16: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 60 * x + 810) (Icc (3: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 60 * x + 810
  let D := Icc (3: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 60 * x + 1620) (Icc (6: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 60 * x + 1620
  let D := Icc (6: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (13: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 16 * x + 64) (Icc (4: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 16 * x + 64
  let D := Icc (4: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 25) (Icc (1: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 10 * x + 25
  let D := Icc (1: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 288) (Icc (2: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 36 * x + 288
  let D := Icc (2: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 120 * x + 1440) (Icc (6: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 120 * x + 1440
  let D := Icc (6: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 1200) (Icc (10: ℝ) (20: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 80 * x + 1200
  let D := Icc (10: ℝ) (20: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (20: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 20 * x + 50) (Icc (5: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 20 * x + 50
  let D := Icc (5: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 350) (Icc (5: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 70 * x + 350
  let D := Icc (5: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (13: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 80 * x + 960) (Icc (8: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 80 * x + 960
  let D := Icc (8: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (14: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 405) (Icc (9: ℝ) (18: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 90 * x + 405
  let D := Icc (9: ℝ) (18: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (18: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn
