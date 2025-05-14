
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 1600) (Icc (10: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 80 * x + 1600
  let D := Icc (10: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 64) (Icc (4: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 32 * x + 64
  let D := Icc (4: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 625) (Icc (5: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 50 * x + 625
  let D := Icc (5: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 200) (Icc (5: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 40 * x + 200
  let D := Icc (5: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (15: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 162 * x + 6561) (Icc (9: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 162 * x + 6561
  let D := Icc (9: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 700) (Icc (10: ℝ) (19: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 140 * x + 700
  let D := Icc (10: ℝ) (19: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (19: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 54 * x + 486) (Icc (9: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 54 * x + 486
  let D := Icc (9: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 108 * x + 3402) (Icc (9: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 108 * x + 3402
  let D := Icc (9: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (12: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 30 * x + 270) (Icc (3: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 30 * x + 270
  let D := Icc (3: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (5: ℝ)
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 36 * x + 972) (Icc (9: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 36 * x + 972
  let D := Icc (9: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 270) (Icc (3: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 18 * x + 270
  let D := Icc (3: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (4: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 576) (Icc (6: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 48 * x + 576
  let D := Icc (6: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (14: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 160) (Icc (2: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 32 * x + 160
  let D := Icc (2: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 126 * x + 3528) (Icc (7: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 126 * x + 3528
  let D := Icc (7: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 70 * x + 245
  let D := Icc (7: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 72 * x + 324) (Icc (9: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 72 * x + 324
  let D := Icc (9: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 28) (Icc (1: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 14 * x + 28
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 96 * x + 768) (Icc (8: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 96 * x + 768
  let D := Icc (8: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (15: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 700) (Icc (5: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 40 * x + 700
  let D := Icc (5: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 72 * x + 1008) (Icc (4: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 72 * x + 1008
  let D := Icc (4: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 3600) (Icc (10: ℝ) (19: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 80 * x + 3600
  let D := Icc (10: ℝ) (19: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (19: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 1000) (Icc (5: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 80 * x + 1000
  let D := Icc (5: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (15: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 1344) (Icc (8: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 48 * x + 1344
  let D := Icc (8: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 2205) (Icc (7: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 70 * x + 2205
  let D := Icc (7: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 216) (Icc (3: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 48 * x + 216
  let D := Icc (3: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 1152) (Icc (4: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 1152
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 448) (Icc (4: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 56 * x + 448
  let D := Icc (4: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 45) (Icc (1: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 10 * x + 45
  let D := Icc (1: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 40 * x + 240) (Icc (2: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 40 * x + 240
  let D := Icc (2: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 60 * x + 810) (Icc (3: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 60 * x + 810
  let D := Icc (3: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 60) (Icc (2: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 12 * x + 60
  let D := Icc (2: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 4) (Icc (1: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 8 * x + 4
  let D := Icc (1: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 144 * x + 2592) (Icc (9: ℝ) (19: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 144 * x + 2592
  let D := Icc (9: ℝ) (19: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (19: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 112 * x + 3136) (Icc (8: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 112 * x + 3136
  let D := Icc (8: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 200) (Icc (5: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 80 * x + 200
  let D := Icc (5: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (14: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 16 * x + 48) (Icc (2: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 16 * x + 48
  let D := Icc (2: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 432) (Icc (3: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 48 * x + 432
  let D := Icc (3: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (8: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 84 * x + 252) (Icc (6: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 84 * x + 252
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 40 * x + 400) (Icc (10: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 40 * x + 400
  let D := Icc (10: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 36 * x + 324
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 112 * x + 2744) (Icc (7: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 112 * x + 2744
  let D := Icc (7: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 160 * x + 4000
  let D := Icc (10: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (15: ℝ)
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 648) (Icc (6: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 24 * x + 648
  let D := Icc (6: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (7: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 70 * x + 245
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 432) (Icc (6: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 48 * x + 432
  let D := Icc (6: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (7: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 36 * x + 108
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 360) (Icc (6: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 24 * x + 360
  let D := Icc (6: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (12: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 40 * x + 320) (Icc (4: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 40 * x + 320
  let D := Icc (4: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (14: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 140 * x + 4410) (Icc (7: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 140 * x + 4410
  let D := Icc (7: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 24 * x + 48) (Icc (2: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 24 * x + 48
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 64) (Icc (2: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 32 * x + 64
  let D := Icc (2: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 160 * x + 4000
  let D := Icc (10: ℝ) (17: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (17: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 48) (Icc (2: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 12 * x + 48
  let D := Icc (2: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (3: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 108) (Icc (3: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 36 * x + 108
  let D := Icc (3: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (12: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 224) (Icc (2: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 28 * x + 224
  let D := Icc (2: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 2025) (Icc (9: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 90 * x + 2025
  let D := Icc (9: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 36 * x + 108
  let D := Icc (2: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 1176) (Icc (7: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 84 * x + 1176
  let D := Icc (7: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 54 * x + 162) (Icc (3: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 54 * x + 162
  let D := Icc (3: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 108 * x + 324) (Icc (6: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 108 * x + 324
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 12) (Icc (1: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 4 * x + 12
  let D := Icc (1: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (5: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 10) (Icc (1: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 10 * x + 10
  let D := Icc (1: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (2: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 12) (Icc (1: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 12 * x + 12
  let D := Icc (1: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 768) (Icc (4: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 768
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 24) (Icc (1: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 12 * x + 24
  let D := Icc (1: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 750) (Icc (5: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 50 * x + 750
  let D := Icc (5: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 4200) (Icc (10: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 140 * x + 4200
  let D := Icc (10: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 100 * x + 2000) (Icc (5: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 100 * x + 2000
  let D := Icc (5: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 160 * x + 1920) (Icc (8: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 160 * x + 1920
  let D := Icc (8: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (15: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 4050) (Icc (9: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 90 * x + 4050
  let D := Icc (9: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 180 * x + 6480) (Icc (9: ℝ) (18: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 180 * x + 6480
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 32 * x + 512) (Icc (8: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 32 * x + 512
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 70) (Icc (1: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 20 * x + 70
  let D := Icc (1: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (4: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 63) (Icc (1: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 14 * x + 63
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 882) (Icc (7: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 84 * x + 882
  let D := Icc (7: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 16 * x + 224) (Icc (4: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 16 * x + 224
  let D := Icc (4: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (8: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1050) (Icc (5: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 70 * x + 1050
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 1215) (Icc (9: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 90 * x + 1215
  let D := Icc (9: ℝ) (17: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (17: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 144 * x + 2880
  let D := Icc (8: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 48 * x + 768) (Icc (4: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 48 * x + 768
  let D := Icc (4: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (8: ℝ)
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

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 144 * x + 2880
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 80 * x + 800) (Icc (4: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 80 * x + 800
  let D := Icc (4: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (8: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 24 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 24 * x + 324
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

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 100) (Icc (1: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 20 * x + 100
  let D := Icc (1: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (6: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 98 * x + 1372) (Icc (7: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 98 * x + 1372
  let D := Icc (7: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (12: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 42 * x + 252) (Icc (3: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 42 * x + 252
  let D := Icc (3: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (12: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 112) (Icc (4: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 56 * x + 112
  let D := Icc (4: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (14: ℝ)
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

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 8) (Icc (1: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 4 * x + 8
  let D := Icc (1: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1750) (Icc (5: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 70 * x + 1750
  let D := Icc (5: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (8: ℝ)
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

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 72 * x + 1296) (Icc (6: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 72 * x + 1296
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

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 128) (Icc (4: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 128
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 192) (Icc (4: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 32 * x + 192
  let D := Icc (4: ℝ) (13: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (13: ℝ)
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 189) (Icc (3: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 18 * x + 189
  let D := Icc (3: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 12) (Icc (1: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 8 * x + 12
  let D := Icc (1: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (1: ℝ) (9: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 126 * x + 5670) (Icc (9: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 126 * x + 5670
  let D := Icc (9: ℝ) (16: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (16: ℝ)
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

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 60 * x + 1080) (Icc (6: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 60 * x + 1080
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

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 300) (Icc (5: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 40 * x + 300
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

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 576) (Icc (8: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 48 * x + 576
  let D := Icc (8: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (11: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 168) (Icc (2: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 28 * x + 168
  let D := Icc (2: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (10: ℝ)
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

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 336) (Icc (4: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 56 * x + 336
  let D := Icc (4: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (8: ℝ)
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
