
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 4 * x ^ 6 + 7 * x ^ 5 + 3 * x ^ 4 + 15 * x ^ 3 + 10 * x ^ 2 + 4) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 7 + 4 * x ^ 6 + 7 * x ^ 5 + 3 * x ^ 4 + 15 * x ^ 3 + 10 * x ^ 2 + 4
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 20 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 42 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 6 * x ^ 4 + 4 * x ^ 3) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 6 * x ^ 4 + 4 * x ^ 3
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 12 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 3 + 17 * x ^ 2 + 7 * x + 6) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 3 + 17 * x ^ 2 + 7 * x + 6
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 7 := by linarith [hx.1]

    have h2: 0 < 34 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 48 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 6 + 7 * x ^ 4 + 17 * x ^ 3 + 4) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 18 * x ^ 6 + 7 * x ^ 4 + 17 * x ^ 3 + 4
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 28 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 108 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 3 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 3 * x ^ 2
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx

    have h0: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 13 * x ^ 6 + 8 * x ^ 5 + 19 * x ^ 4 + 15 * x ^ 3 + 8 * x ^ 2 + 19 * x + 5) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 13 * x ^ 6 + 8 * x ^ 5 + 19 * x ^ 4 + 15 * x ^ 3 + 8 * x ^ 2 + 19 * x + 5
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 76 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 40 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h7: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6, h7]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 112 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 9 * x ^ 3 + 12 * x ^ 2 + 2 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 5 + 9 * x ^ 3 + 12 * x ^ 2 + 2 * x + 12
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 2 := by linarith [hx.1]

    have h2: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 50 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 4 + 19 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 4 + 19 * x ^ 3 + 4 * x ^ 2
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 57 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 25 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 2 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 7 + 2 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 19 * x + 12
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 8 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 140 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 18 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 18 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 2
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 25 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 108 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 18 * x ^ 6 + 2 * x ^ 5 + 17 * x ^ 3 + 7 * x) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 18 * x ^ 6 + 2 * x ^ 5 + 17 * x ^ 3 + 7 * x
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 10 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 108 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 18 * x ^ 6 + 11 * x ^ 5 + 14 * x ^ 4 + 20 * x ^ 3 + 13 * x ^ 2 + 5 * x + 8) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 7 + 18 * x ^ 6 + 11 * x ^ 5 + 14 * x ^ 4 + 20 * x ^ 3 + 13 * x ^ 2 + 5 * x + 8
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 5 := by linarith [hx.1]

    have h2: 0 < 26 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 108 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h7: 0 < 70 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6, h7]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 3 + 15 * x ^ 2 + 8 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 3 + 15 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]

    have h1: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 96 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 15 * x ^ 6 + 9 * x ^ 4 + 8 * x ^ 2 + 17 * x + 15) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 15 * x ^ 6 + 9 * x ^ 4 + 8 * x ^ 2 + 17 * x + 15
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 17 := by linarith [hx.1]

    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 36 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 8 * x ^ 5 + 15 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 6 + 8 * x ^ 5 + 15 * x ^ 2
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 40 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 6 * x ^ 2 + 5 * x + 4) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 6 + 6 * x ^ 2 + 5 * x + 4
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 5 := by linarith [hx.1]

    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 11 * x ^ 6 + 2 * x ^ 4 + 19 * x ^ 2) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 11 * x ^ 6 + 2 * x ^ 4 + 19 * x ^ 2
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 38 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 8 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 66 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 112 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 7 * x ^ 6 + 13 * x ^ 5 + 13 * x ^ 3) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 7 * x ^ 6 + 13 * x ^ 5 + 13 * x ^ 3
  let D := Icc (0: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (2: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 39 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 65 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 3 * x ^ 6 + 17 * x ^ 4 + 13 * x ^ 3 + 2 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 7 + 3 * x ^ 6 + 17 * x ^ 4 + 13 * x ^ 3 + 2 * x ^ 2 + 18 * x + 13
  let D := Icc (0: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (2: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 18 := by linarith [hx.1]

    have h2: 0 < 4 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 39 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 18 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 42 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 3 + 11 * x + 4) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 3 + 11 * x + 4
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    have h1: 0 < 11 := by linarith [hx.1]

    have h2: 0 < 6 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 14 * x ^ 3 + 2 * x ^ 2 + 18 * x + 19) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 14 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 14 * x ^ 3 + 2 * x ^ 2 + 18 * x + 19
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 18 := by linarith [hx.1]

    have h2: 0 < 4 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 15 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 98 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 4 + 3 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 4 + 3 * x ^ 2 + 19 * x + 12
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 36 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 14 * x ^ 6 + 3 * x ^ 3 + 20 * x ^ 2 + 13 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 7 + 14 * x ^ 6 + 3 * x ^ 3 + 20 * x ^ 2 + 13 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 13 := by linarith [hx.1]

    have h1: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 9 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 84 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 14 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 2 + 6) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 2 + 6
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 18 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 105 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 6 * x ^ 2 + 12 * x + 4) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 6 * x ^ 2 + 12 * x + 4
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 11 * x ^ 5 + 19 * x + 10) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 6 + 11 * x ^ 5 + 19 * x + 10
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 18 * x ^ 5 + 9 * x ^ 3 + 4 * x ^ 2 + 3 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 18 * x ^ 5 + 9 * x ^ 3 + 4 * x ^ 2 + 3 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 3 := by linarith [hx.1]

    have h1: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 90 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 19 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 18) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 19 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 18
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 114 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 11 * x ^ 5 + 17 * x ^ 4 + 5 * x ^ 3 + 18 * x ^ 2 + 13 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 6 + 11 * x ^ 5 + 17 * x ^ 4 + 5 * x ^ 3 + 18 * x ^ 2 + 13 * x
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 13 := by linarith [hx.1]

    have h1: 0 < 36 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 7 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 4 + 9 * x ^ 2 + 16 * x) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 7 + 7 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 4 + 9 * x ^ 2 + 16 * x
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 16 := by linarith [hx.1]

    have h1: 0 < 18 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 36 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 85 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 105 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 6 + 4 * x ^ 5 + 20 * x ^ 4 + 11 * x ^ 3 + 2 * x ^ 2 + 9 * x + 7) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 18 * x ^ 6 + 4 * x ^ 5 + 20 * x ^ 4 + 11 * x ^ 3 + 2 * x ^ 2 + 9 * x + 7
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 9 := by linarith [hx.1]

    have h2: 0 < 4 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 33 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 108 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 10 * x ^ 6 + 20 * x ^ 5 + 8 * x ^ 3 + 15 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 10 * x ^ 6 + 20 * x ^ 5 + 8 * x ^ 3 + 15 * x ^ 2 + 19 * x
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 19 := by linarith [hx.1]

    have h1: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 24 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 100 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 60 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 17 * x ^ 6 + 10 * x ^ 2 + 12 * x + 13) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 7 + 17 * x ^ 6 + 10 * x ^ 2 + 12 * x + 13
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 20 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 102 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 56 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 8 * x + 14) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 8 * x + 14
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    have h1: 0 < 8 := by linarith [hx.1]

    have h2: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 4 + 20 * x ^ 3 + 5 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 4 + 20 * x ^ 3 + 5 * x ^ 2 + 19 * x
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 19 := by linarith [hx.1]

    have h1: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 60 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 15 * x ^ 6 + 8 * x ^ 5 + 2 * x ^ 4 + 7 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 15 * x ^ 6 + 8 * x ^ 5 + 2 * x ^ 4 + 7 * x ^ 2 + 18 * x + 13
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 18 := by linarith [hx.1]

    have h2: 0 < 14 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 8 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 40 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 57 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 63 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 4 + 15 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 4 + 15 * x ^ 2 + 18 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 18 := by linarith [hx.1]

    have h1: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 32 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 6 + 14 * x ^ 5 + 14 * x ^ 4) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 6 + 14 * x ^ 5 + 14 * x ^ 4
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 70 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 18 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 6 * x ^ 5 + 3 * x ^ 4 + 6 * x ^ 3 + 16 * x + 14) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 19 * x ^ 7 + 6 * x ^ 5 + 3 * x ^ 4 + 6 * x ^ 3 + 16 * x + 14
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 16 := by linarith [hx.1]

    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 30 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 133 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 15 * x ^ 6 + 20 * x ^ 5 + 17 * x ^ 4 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 15 * x ^ 6 + 20 * x ^ 5 + 17 * x ^ 4 + 4 * x ^ 2
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 100 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 3 * x ^ 3 + 6 * x ^ 2 + 17 * x + 6) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 5 + 3 * x ^ 3 + 6 * x ^ 2 + 17 * x + 6
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 17 := by linarith [hx.1]

    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 9 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 50 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 5 + 17 * x ^ 4 + 9 * x ^ 3 + 12 * x + 18) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 7 + 11 * x ^ 5 + 17 * x ^ 4 + 9 * x ^ 3 + 12 * x + 18
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 140 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 9 * x ^ 6 + 3 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 18 * x) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 9 * x ^ 6 + 3 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 18 * x
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 18 := by linarith [hx.1]

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 24 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 54 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 12 * x ^ 6 + 14 * x ^ 5 + 13 * x ^ 4 + 18 * x ^ 3 + 5 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 12 * x ^ 6 + 14 * x ^ 5 + 13 * x ^ 4 + 18 * x ^ 3 + 5 * x ^ 2 + 18 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 18 := by linarith [hx.1]

    have h1: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 54 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 52 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 70 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 4 * x ^ 6 + 19 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 4 * x ^ 6 + 19 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 4 * x ^ 2
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 30 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 40 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 95 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 13 * x ^ 6 + 9 * x ^ 5 + 16 * x ^ 4 + 15 * x ^ 3 + 5 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 7 + 13 * x ^ 6 + 9 * x ^ 5 + 16 * x ^ 4 + 15 * x ^ 3 + 5 * x ^ 2
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 91 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 5 + 15 * x ^ 3 + 20 * x ^ 2) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 5 + 15 * x ^ 3 + 20 * x ^ 2
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 25 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 12 * x ^ 5 + 15 * x ^ 4 + 4 * x ^ 2 + 11 * x + 4) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 7 + 12 * x ^ 5 + 15 * x ^ 4 + 4 * x ^ 2 + 11 * x + 4
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 11 := by linarith [hx.1]

    have h2: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 56 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 4 + 6 * x ^ 3 + 2 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 4 + 6 * x ^ 3 + 2 * x ^ 2 + 7 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 4 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 10 * x ^ 5 + 13 * x ^ 4 + 3 * x) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 18 * x ^ 7 + 10 * x ^ 5 + 13 * x ^ 4 + 3 * x
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 3 := by linarith [hx.1]

    have h1: 0 < 52 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 50 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 126 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 12 * x ^ 5 + 14 * x ^ 4 + 12 * x ^ 2 + 7 * x) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 7 + 12 * x ^ 5 + 14 * x ^ 4 + 12 * x ^ 2 + 7 * x
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 49 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 12 * x ^ 4 + 18 * x ^ 3 + 8) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 7 + 12 * x ^ 4 + 18 * x ^ 3 + 8
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 54 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 9 * x ^ 5 + 5 * x ^ 3) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 9 * x ^ 5 + 5 * x ^ 3
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 15 * x ^ 5 + 15 * x ^ 3 + 15 * x ^ 2 + 7 * x + 3) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 19 * x ^ 7 + 15 * x ^ 5 + 15 * x ^ 3 + 15 * x ^ 2 + 7 * x + 3
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 7 := by linarith [hx.1]

    have h2: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 75 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 133 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x
  let D := Icc (0: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (2: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 32 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 65 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 66 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 9 * x ^ 3 + 18 * x ^ 2 + 12 * x + 16) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 9 * x ^ 3 + 18 * x ^ 2 + 12 * x + 16
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 36 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 6 * x ^ 6 + 17 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 7 + 6 * x ^ 6 + 17 * x ^ 3 + 12 * x ^ 2 + 9 * x
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 9 := by linarith [hx.1]

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 36 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 105 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 12 * x ^ 6 + 12 * x ^ 5 + 3 * x ^ 4 + 7 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 7 + 12 * x ^ 6 + 12 * x ^ 5 + 3 * x ^ 4 + 7 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 140 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 5 * x ^ 3 + 16 * x ^ 2 + 7) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 5 * x ^ 3 + 16 * x ^ 2 + 7
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 32 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 20 * x ^ 4 + 4 * x ^ 2 + 18 * x + 15) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 20 * x ^ 4 + 4 * x ^ 2 + 18 * x + 15
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 18 := by linarith [hx.1]

    have h2: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 112 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 19 * x ^ 5 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 7 + 19 * x ^ 5 + 4 * x ^ 3 + 20 * x
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 20 := by linarith [hx.1]

    have h1: 0 < 12 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 95 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 14 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 5 * x ^ 6 + 12 * x ^ 5 + 17 * x ^ 4 + 8 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 5 * x ^ 6 + 12 * x ^ 5 + 17 * x ^ 4 + 8 * x ^ 3
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 24 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 30 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 6 + 13 * x ^ 5 + 17 * x ^ 4 + 17 * x ^ 3 + 7 * x ^ 2 + 10 * x + 2) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 6 + 13 * x ^ 5 + 17 * x ^ 4 + 17 * x ^ 3 + 7 * x ^ 2 + 10 * x + 2
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 10 := by linarith [hx.1]

    have h2: 0 < 14 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 65 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 11 * x ^ 4 + 8 * x ^ 2 + 20 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 5 + 11 * x ^ 4 + 8 * x ^ 2 + 20 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 20 := by linarith [hx.1]

    have h1: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 44 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 6 + 4 * x ^ 4 + 11 * x ^ 2 + 19 * x + 3) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 6 + 4 * x ^ 4 + 11 * x ^ 2 + 19 * x + 3
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 22 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 16 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 12 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 14 * x ^ 4 + 12 * x + 10) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 5 + 14 * x ^ 4 + 12 * x + 10
  let D := Icc (0: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (2: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 4 * x ^ 5 + 8 * x ^ 4 + 3 * x ^ 3 + 20 * x ^ 2 + 8 * x) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 6 + 4 * x ^ 5 + 8 * x ^ 4 + 3 * x ^ 3 + 20 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]

    have h1: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 9 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 32 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 120 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 5 + 16 * x ^ 4) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 5 + 16 * x ^ 4
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx

    have h0: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 100 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 3 + 20 * x ^ 2 + 17 * x + 8) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 3 + 20 * x ^ 2 + 17 * x + 8
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 17 := by linarith [hx.1]

    have h2: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 4 + 10 * x ^ 3 + 13 * x ^ 2) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 4 + 10 * x ^ 3 + 13 * x ^ 2
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 26 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 30 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 6 * x ^ 4 + 7 * x ^ 3 + 12 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 6 * x ^ 4 + 7 * x ^ 3 + 12 * x ^ 2 + 6 * x
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 6 := by linarith [hx.1]

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 5 * x ^ 6 + 15 * x ^ 4 + 3 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 18 * x ^ 7 + 5 * x ^ 6 + 15 * x ^ 4 + 3 * x ^ 2 + 7 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 7 := by linarith [hx.1]

    have h1: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 60 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 30 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 126 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 28 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 20 * x ^ 2 + 14 * x + 20) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 20 * x ^ 2 + 14 * x + 20
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 14 := by linarith [hx.1]

    have h2: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 15 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 16 * x ^ 4 + 5 * x ^ 3 + 19 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 6 + 16 * x ^ 4 + 5 * x ^ 3 + 19 * x ^ 2
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 38 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 5 + 19 * x ^ 4 + 6 * x ^ 3 + 12 * x + 14) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 5 + 19 * x ^ 4 + 6 * x ^ 3 + 12 * x + 14
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 76 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 15 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 70 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 3 * x ^ 5 + 8 * x ^ 4 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 3 * x ^ 5 + 8 * x ^ 4 + 4 * x ^ 3 + 20 * x
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 20 := by linarith [hx.1]

    have h1: 0 < 12 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 32 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 15 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 2 * x ^ 6 + 9 * x ^ 5 + 10 * x + 13) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 2 * x ^ 6 + 9 * x ^ 5 + 10 * x + 13
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 10 := by linarith [hx.1]

    have h2: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 12 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 11 * x ^ 5 + 20 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 12 * x + 3) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 11 * x ^ 5 + 20 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 12 * x + 3
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 12 := by linarith [hx.1]

    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 4 + 19 * x + 13) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 4 + 19 * x + 13
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    have h1: 0 < 19 := by linarith [hx.1]

    have h2: 0 < 60 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 4 + 6 * x ^ 3 + 14 * x ^ 2 + 6) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 4 + 6 * x ^ 3 + 14 * x ^ 2 + 6
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 28 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 28 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 9 * x ^ 5 + 14 * x ^ 4 + 3 * x ^ 2 + 17) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 6 + 9 * x ^ 5 + 14 * x ^ 4 + 3 * x ^ 2 + 17
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 60 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 14 * x ^ 4 + 18 * x ^ 3 + 3 * x ^ 2 + 8 * x) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 14 * x ^ 4 + 18 * x ^ 3 + 3 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]

    have h1: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 54 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 19 * x ^ 5 + 13 * x ^ 4 + 4 * x ^ 2 + 8 * x + 12) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 7 + 19 * x ^ 5 + 13 * x ^ 4 + 4 * x ^ 2 + 8 * x + 12
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 8 := by linarith [hx.1]

    have h2: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 52 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 95 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 21 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 2 + 12 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 2 + 12 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 12 := by linarith [hx.1]

    have h1: 0 < 26 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 13 * x ^ 6 + 18 * x ^ 5 + 15 * x ^ 4 + 9 * x ^ 3 + 17 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 7 + 13 * x ^ 6 + 18 * x ^ 5 + 15 * x ^ 4 + 9 * x ^ 3 + 17 * x ^ 2 + 6 * x
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 6 := by linarith [hx.1]

    have h1: 0 < 34 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 90 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 21 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 26 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 70 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 120 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 8 * x ^ 5 + 3 * x ^ 3 + 18 * x ^ 2 + 2 * x) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 7 + 8 * x ^ 5 + 3 * x ^ 3 + 18 * x ^ 2 + 2 * x
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 2 := by linarith [hx.1]

    have h1: 0 < 36 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 9 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 40 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 49 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 2 + 8 * x + 7) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 2 + 8 * x + 7
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 8 := by linarith [hx.1]

    have h2: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 4 * x ^ 6 + 16 * x ^ 5 + 11 * x ^ 4 + 5 * x ^ 3 + 15 * x ^ 2 + 20) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 7 + 4 * x ^ 6 + 16 * x ^ 5 + 11 * x ^ 4 + 5 * x ^ 3 + 15 * x ^ 2 + 20
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 44 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 80 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 91 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 4 + 14 * x ^ 3 + 8 * x ^ 2 + 13 * x + 11) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 18 * x ^ 4 + 14 * x ^ 3 + 8 * x ^ 2 + 13 * x + 11
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 13 := by linarith [hx.1]

    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 42 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 72 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 10 * x ^ 6 + 11 * x ^ 4 + 10 * x ^ 3 + 13) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 7 + 10 * x ^ 6 + 11 * x ^ 4 + 10 * x ^ 3 + 13
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]

    ring
    rw [interior_Icc] at hx

    have h1: 0 < 30 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 44 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 56 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 17 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 2 + 2 * x + 10) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 17 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 2 + 2 * x + 10
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 2 := by linarith [hx.1]

    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 102 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 12 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 6 + 12 * x ^ 5 + 20 * x ^ 2
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 40 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 60 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 60 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 6 * x ^ 6 + 6 * x ^ 5 + 10 * x ^ 4 + 2 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 6 * x ^ 6 + 6 * x ^ 5 + 10 * x ^ 4 + 2 * x ^ 3 + 12 * x ^ 2 + 9 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 9 := by linarith [hx.1]

    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 6 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 40 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 30 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 36 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h6: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 2 + 8 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']

    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]

    have h1: 0 < 18 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 85 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 15 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 14 * x ^ 7 + 15 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
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
    rw [interior_Icc] at hx

    have h0: 0 < 12 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 20 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h2: 0 < 75 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 98 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
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
    have h1: 0 < 18 := by linarith [hx.1]

    have h2: 0 < 34 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h3: 0 < 48 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h4: 0 < 66 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h5: 0 < 140 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

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
