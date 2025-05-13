
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 13)
  (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p)
  (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 13 * q x > 26 * x := by
  let f := (λ x ↦ p x + 13 * q x - 26 * x)
  let D := Icc (0: ℝ) (1: ℝ)

  have gt_zero: f 0 > 0 := by
    simp [f, h0.left]
    rw [← one_add_mul]
    apply mul_pos
    · norm_num
    · exact h0.right
  have monotonic: MonotoneOn f D := by
    have hfDifferentiableInReal : Differentiable ℝ f := by
        exact ((hpDeriv).add (hqDeriv.const_mul _)).sub (differentiable_id.const_mul _)
    have hfDifferentiable: DifferentiableOn ℝ f (interior D) := by
      exact hfDifferentiableInReal.differentiableOn.mono interior_subset
    have hfContinuous: ContinuousOn f D:= by
      exact hfDifferentiableInReal.continuous.continuousOn

    have interior_increasing: ∀ x2 ∈ interior D, deriv f x2 ≥ 0 := by
      intros x2 hx2
      let hpX2 := hP x2
      have reciprocal_deriv: deriv q x2 = 13 / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = 13 ↔ deriv q x2 = 13 / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + 13 * (13 / deriv p x2) - 26) ↔
        0 ≤ deriv p x2 + 13 * (13 / deriv p x2) - 26 := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + 13 * (13 / deriv p x2) - 26)
              = deriv p x2 ^ 2 + 13 * 13 - 26 * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + 13 * 13 - 26 * deriv p x2 = (deriv p x2 - 13) ^ 2 := by ring
      have simplify: deriv p x2 + 13 * (13 / deriv p x2) - 26 * (fun x2 ↦ 1) x = deriv p x2 + 13 * (13 / deriv p x2) - 26 := by ring
      rw [quad_eq, quad_sq] at sq_iff
      rw [simplify]
      exact sq_iff.mp (by apply sq_nonneg)
      exact differentiableAt_id
      exact hqDeriv x2
      exact hpDeriv x2
      exact DifferentiableAt.const_mul (hqDeriv x2) _
      exact DifferentiableAt.add (hpDeriv x2) (DifferentiableAt.const_mul (hqDeriv x2) _)
      exact DifferentiableAt.const_mul differentiableAt_id _

    apply monotoneOn_of_deriv_nonneg (convex_Icc (0: ℝ) 1) (hfContinuous) (hfDifferentiable) (interior_increasing)
  have f_pos: f x > 0 := by
    have x_pos: x ≥ 0 := by
      apply (mem_Icc.mp hD).1
    have fx_gt_f_zero: f x ≥ f 0 := by
      apply monotonic (left_mem_Icc.mpr (by norm_num)) hD
      exact x_pos
    apply lt_of_lt_of_le gt_zero fx_gt_f_zero
  have equiv: p x + 13 * q x > 26 * x ↔ p x + 13 * q x - 26 * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos
