import Mathlib
open Real

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  have h : (fun x => sin (exp x * (x ^ 2 + 3) + cos (log x))) = (fun x => sin (exp x * (x ^ 2 + 3) + cos (log x))) := rfl
  rw [h]
  simp only [h]
  rw [deriv_sin]
  simp only [Function.comp_apply, deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const',
    deriv_log, deriv_cos, deriv_sin, deriv_id'', deriv_const', deriv_log, deriv_cos, deriv_sin,
    deriv_id'', deriv_const', deriv_log, deriv_cos, deriv_sin, deriv_id'', deriv_const', deriv_log,
    deriv_cos, deriv_sin, deriv_id'', deriv_const', deriv_log, deriv_cos]
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  have h : ∀ x : ℝ, x ≠ 0 →
    deriv (fun x => Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x =
    -1 * Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) *
    ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.exp x) * ((2:ℝ) * x) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
    intro x hx
    rw [deriv_cos]
    field_simp [hx]
    ring_nf
    <;> simp_all
    <;> linarith
  exact h x h_log_ne_zero_16

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) ^ 2 := by
  have h1 : ∀ x : ℝ, (fun x => tan (exp x * (x ^ 2 + 3) + cos (log x))) =
    fun x => tan (exp x * (x ^ 2 + 3) + cos (log x)) := by simp
  rw [h1]
  funext x
  rw [deriv_tan_comp]
  simp only [h1, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring
  <;> simp only [h1, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  rw [deriv_exp]
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_add_const, deriv_id'', deriv_log',
    deriv_const', deriv_id, mul_one, mul_zero, add_zero, zero_add, mul_comm, mul_assoc, mul_left_comm]
  ring
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) / (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := by
    intro x hx
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) hx
  have h2 : ∀ x : ℝ, x ≠ 0 → (x ^ 2 + (3:ℝ)) ≠ 0 := by
    intro x hx
    exact ne_of_gt (by positivity)
  have h3 : ∀ x : ℝ, x ≠ 0 → (Real.exp x * (x ^ 2 + (3:ℝ))) ≠ 0 := by
    intro x hx
    exact mul_ne_zero (exp_ne_zero x) (h2 x hx)
  have h4 : ∀ x : ℝ, x ≠ 0 → Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    exact ne_of_gt (by positivity)
  have h5 : ∀ x : ℝ, x ≠ 0 → Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    exact ne_of_gt (by positivity)
  have h6 : ∀ x : ℝ, x ≠ 0 → Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    exact ne_of_gt (by positivity)
  field_simp [*, exp_ne_zero, h1, h2, h3, h4, h5, h6]
  ring
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_exp]
  rw [deriv_mul]
  rw [deriv_pow]
  rw [deriv_add]
  rw [deriv_const]
  rw [deriv_id]
  rw [deriv_cos]
  rw [deriv_log]
  ring
  all_goals assumption

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.exp x) + (Real.cos (Real.log x) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  fun_prop
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.exp_ne_zero]

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ rexp x * (x ^ 2 + 3) + cos (log x) + cos (log x)) x =
    rexp x * (x ^ 2 + 3) + rexp x * (2 * x) + -sin (log x) * (1 / x) + -sin (log x) * (1 / x) := by
    intro x hx
    rw [deriv_add, deriv_add, deriv_add, deriv_mul, deriv_mul, deriv_exp, deriv_pow, deriv_const,
      deriv_cos, deriv_log, deriv_cos] <;> simp [hx]
    all_goals ring_nf
  apply h
  apply h_log_ne_zero_15

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.cos (Real.log x)) + (Real.cos (Real.log x) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const, deriv_log, deriv_cos,
    deriv_sin, deriv_inv, deriv_comp, deriv_arctan, comp_apply, mul_one, mul_zero, mul_neg, mul_add,
    mul_sub, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_15]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [add_assoc, mul_assoc, mul_add, add_mul, mul_one, mul_zero, zero_mul,
    add_zero, zero_add, one_mul, mul_comm, mul_left_comm]
  aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_cos, deriv_sin, deriv_log, deriv_pow,
    differentiableAt_id', differentiableAt_cos, differentiableAt_sin, differentiableAt_log,
    differentiableAt_pow, differentiableAt_const]
  ring_nf
  field_simp [h_log_ne_zero_15]
  ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all [deriv_add, deriv_mul, deriv_log, deriv_exp, deriv_pow, deriv_const, deriv_id, deriv_cos,
    deriv_sin, deriv_neg, mul_neg, neg_neg, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_15, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> assumption
  <;> simp [*, exp_ne_zero] at *
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [mul_add, mul_one, mul_comm, mul_left_comm, mul_right_comm]
  aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_const, deriv_id,
    deriv_log, deriv_cos, deriv_sin, deriv_inv, deriv_comp, deriv_add, deriv_mul, deriv_exp,
    deriv_pow, deriv_add, deriv_const, deriv_id, deriv_log, deriv_cos, deriv_sin, deriv_inv,
    deriv_comp]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_cos, deriv_sin,
    deriv_comp, deriv_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19]
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp [Real.deriv_sin, Real.deriv_cos, deriv_sub, deriv_add, deriv_mul, deriv_exp, deriv_log,
    deriv_pow, deriv_id, deriv_const]
  field_simp [h_log_ne_zero_16]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm, mul_one, mul_neg, mul_zero, zero_mul, neg_mul,
    one_mul, neg_zero]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_sub, deriv_cos, deriv_exp, deriv_log, deriv_pow, deriv_id'', deriv_const', deriv_mul,
    deriv_neg, neg_mul, neg_neg]
  field_simp [h_log_ne_zero_16]
  ring_nf
  <;> simp only [Real.exp_ne_zero] <;> norm_num
  <;> field_simp <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) ^ 2 := by
  have h_cos_ne_zero : ∀ x : ℝ, cos x ≠ 0 := fun x =>
    (cos_ne_zero_iff x).mpr <| by norm_num
  have h_exp_ne_zero : ∀ x : ℝ, exp x ≠ 0 := fun x => exp_ne_zero x
  field_simp [Real.tan_eq_sin_div_cos, h_cos_ne_zero, h_exp_ne_zero, h_log_ne_zero_16]
  ring_nf
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.exp (Real.exp x * (x ^ 2 + 3) - Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + 3) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + 3)) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
    intro x hx
    rw [deriv_exp (Real.exp x * (x ^ 2 + 3) - Real.cos (Real.log x))]
    rw [deriv_sub]
    · rw [deriv_mul]
      simp [deriv_exp, deriv_mul, deriv_id, deriv_const]
      ring
    · rw [deriv_cos]
      simp [deriv_log, hx]
      ring
  simpa using h₁ x h_log_ne_zero_16

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) := by
  have h : ∀ x : ℝ, x ≠ 0 → (λ x => Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) =ᶠ[𝓝 x] fun x => Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) := fun x hx => eventually_of_forall fun y => rfl
  simp only [deriv_log_of_mem_nhds, h x hx]
  field_simp [*, sub_ne_zero]
  ring
  <;> simp only [Real.exp_zero, add_zero, zero_add, mul_one, mul_zero, sub_zero, sub_neg_eq_add]
  <;> apply DifferentiableAt.differentiableWithinAt
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.neg
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.neg
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.neg
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc, mul_assoc,
    mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm,
    mul_left_comm, add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm,
    add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, add_comm,
    add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm,
    add_assoc, mul_assoc, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc,
    mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_15]
  ring
  <;> simp [Real.exp_log]
  <;> simp [Real.exp_log]
  <;> simp [Real.exp_log]

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.exp x) + (Real.cos (Real.log x) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x))) := by
  simp only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, deriv_add, deriv_mul,
    deriv_exp, deriv_id'', deriv_const', deriv_log, deriv_cos, deriv_sin, deriv_sub,
    deriv_id, deriv_pow, deriv_pow_const, deriv_zpow, deriv_zpow_const, deriv_div,
    deriv_inv, deriv_pow, deriv_zpow, deriv_zpow_const, deriv_inv, deriv_pow, deriv_zpow,
    deriv_zpow_const, deriv_inv, deriv_pow, deriv_zpow, deriv_zpow_const, deriv_inv, deriv_pow,
    deriv_zpow, deriv_zpow_const, deriv_inv, deriv_pow, deriv_zpow, deriv_zpow_const, deriv_inv,
    deriv_pow, deriv_zpow, deriv_zpow_const, deriv_inv]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_id,
    deriv_cos, deriv_sin, mul_one, mul_neg, neg_neg, mul_comm, mul_left_comm, mul_assoc]
  field_simp
  ring
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.cos (Real.log x)) + (Real.cos (Real.log x) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  field_simp [h_log_ne_zero_15]
  simp_all only [mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, mul_sub, mul_one, mul_div_cancel_left]
  ring
  <;> apply Real.exp_ne_zero
  <;> apply Real.cos_ne_zero
  <;> apply Real.sin_ne_zero

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_sub]
  · rw [deriv_add]
    · rw [deriv_mul]
      · rw [deriv_exp]
        simp
      · rw [deriv_pow]
        simp
        <;> field_simp
    · rw [deriv_cos]
      simp
  · rw [deriv_sin]
    simp
  · apply DifferentiableAt.sub <;> apply DifferentiableAt.add <;> apply DifferentiableAt.mul <;>
      apply DifferentiableAt.exp <;>
      apply DifferentiableAt.pow <;>
      apply DifferentiableAt.log <;>
      apply DifferentiableAt.const_mul <;>
      apply DifferentiableAt.const_add <;>
      apply DifferentiableAt.const_sub <;>
      apply DifferentiableAt.id
  <;> norm_num
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.const_sub
  <;> apply DifferentiableAt.id

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₁ : ∀ x, deriv (fun x => Real.exp x * (x ^ 2 + 3) - Real.cos (Real.log x) * Real.sin (2 * x - 1) ^ 2) x =
    Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) -
      ((-1 * Real.sin (Real.log x) * (1 / x)) * Real.sin (2 * x - 1) ^ 2 +
        Real.cos (Real.log x) * (2 * Real.sin (2 * x - 1) * Real.cos (2 * x - 1) * 2)) := by
    intro x
    rw [deriv_sub, deriv_mul, deriv_mul]
    · simp only [deriv_exp, deriv_pow'', deriv_id'', deriv_const', deriv_cos, deriv_log, deriv_sin,
        deriv_sub, deriv_mul, deriv_const, deriv_id, mul_one, mul_zero, sub_zero, mul_neg, neg_mul,
        mul_assoc, mul_comm, mul_left_comm, neg_neg, neg_mul, neg_add_rev]
      ring
    · apply DifferentiableAt.mul
      · exact differentiableAt_exp
      · exact differentiableAt_id.pow
    · apply DifferentiableAt.mul
      · exact differentiableAt_cos
      · exact differentiableAt_sin.pow
  simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [mul_add, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    Real.exp_log, Real.log_exp, Real.log_pow, Real.log_mul, Real.log_inv, Real.log_pow,
    Real.log_mul, Real.log_inv, Real.log_pow, Real.log_mul, Real.log_inv, Real.log_pow]
  field_simp
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [mul_add, mul_sub, sub_eq_add_neg, neg_mul, mul_neg, mul_one, mul_neg_one, neg_neg,
    mul_right_comm, mul_assoc, mul_comm]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_23, h_log_ne_zero_26]
  ring_nf
  simp only [mul_add, mul_sub, sub_eq_add_neg, neg_mul, mul_neg, mul_one, mul_neg_one, neg_neg,
    mul_right_comm, mul_assoc, mul_comm]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_23, h_log_ne_zero_26]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_exp, deriv_log, deriv_pow, deriv_id,
    deriv_sin, deriv_cos, deriv_tan, deriv_arctan, deriv_zpow, deriv_inv, deriv_add_const,
    deriv_sub_const]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19]
  ring
  <;> simp only [Real.exp_log, mul_inv_cancel, mul_one, mul_add, mul_sub, sub_neg_eq_add,
    add_assoc, add_left_comm, add_comm, mul_comm]
  <;> field_simp [h_log_ne_zero_15, h_log_ne_zero_19]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp_all only [add_left_neg, add_zero, mul_one, mul_zero, sub_zero, mul_comm, mul_left_comm, mul_assoc,
    Real.cos_zero, Real.sin_zero, Real.log_one, Real.exp_zero, zero_add, zero_sub, sub_neg_eq_add]
  apply congr_arg
  ring
  <;> apply congr_arg <;> ring
  <;> apply congr_arg <;> ring
  <;> apply congr_arg <;> ring
  <;> apply congr_arg <;> ring
  <;> apply congr_arg <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp_all [Real.deriv_sin, Real.deriv_cos, Real.deriv_exp, Real.deriv_log, Real.deriv_pow]
  field_simp [h_log_ne_zero_16]
  ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h1 : deriv (fun x => Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
    simp [Real.cos_exp, Real.cos_log, mul_add, mul_comm, mul_left_comm]
    ring_nf
    field_simp
    rw [mul_comm]
    apply mul_left_comm
  rw [h1]
  <;> simp_all
  <;> field_simp at *
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) ^ 2 := by
  have h₀ : ∀ x : ℝ, 0 < cos (x) → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₁ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₂ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₃ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₄ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₅ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₆ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₇ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₈ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₉ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  have h₁₀ : ∀ x : ℝ, 0 < cos x → tan x = sin x / cos x := fun x hx ↦ by rw [tan_eq_sin_div_cos];
  simp_all only [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
  field_simp
  ring
  <;> simp_all only [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h₁ : ∀ x ≠ (0:ℝ), deriv (fun x ↦ Real.exp (Real.exp x * (x ^ 2 + 3 * x) * Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + 3 * x) * Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + 3 * x) + Real.exp x * (2 * x + 3)) * Real.cos (Real.log x) + Real.exp x * (x ^ 2 + 3 * x) * (-Real.sin (Real.log x) * (1 / x))) := by
    intro x hx
    rw [deriv_exp (Real.exp x * (x ^ 2 + 3 * x) * Real.cos (Real.log x))]
    field_simp [hx]
    ring_nf
    rw [← mul_assoc]
    field_simp
    ring
  simpa using h₁ x h_log_ne_zero_16

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) := by
  have h₁ : ∀ x, x ≠ 0 → Real.log x ≠ 0 := by
    intro x hx
    exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) hx
  have h₂ : ∀ x, Real.exp x ≠ 0 := fun _ => Real.exp_ne_zero _
  have h₃ : ∀ x, Real.cos x ≠ 0 → x ≠ π / 2 := fun _ h =>
    mt Real.cos_eq_zero_iff.2 h
  have h₄ : ∀ x, x ≠ 0 → x ^ 2 + 3 ≠ 0 := by
    intro x hx
    nlinarith
  field_simp [*, Real.log_mul, Real.log_exp, mul_add, mul_sub, mul_comm]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_id'', deriv_const, mul_one, mul_add, mul_comm, mul_assoc]
  field_simp [h_log_ne_zero_15, Real.cos_log]
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  rw [deriv_mul]
  simp [mul_add, mul_comm, mul_left_comm, mul_assoc]
  field_simp [Real.exp_ne_zero, h_log_ne_zero_16]
  ring
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.exp
  <;> apply Differentiable.log
  <;> apply Differentiable.cos
  <;> apply Differentiable.sin
  <;> apply Differentiable.id
  <;> apply Differentiable.const

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp_all only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id'', deriv_cos,
    deriv_log, neg_mul, neg_neg, mul_one, mul_zero, mul_neg, mul_add, mul_assoc]
  field_simp
  ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_mul]
  simp [deriv_exp, deriv_pow, deriv_add, deriv_id, deriv_const, deriv_cos, deriv_sin, deriv_log, h_log_ne_zero_15]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  have h₀ : ∀ x ≠ 0, deriv (fun x => (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
    intro x hx
    have h₀ : DifferentiableAt ℝ (fun x => (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x := by
      apply DifferentiableAt.add
      <;> (apply DifferentiableAt.mul
        <;> (apply DifferentiableAt.exp
          <;> (apply DifferentiableAt.pow
            <;> (apply DifferentiableAt.add
              <;> (apply DifferentiableAt.mul
                <;> (apply DifferentiableAt.const_add
                  <;> (apply DifferentiableAt.id
                  <;> (apply DifferentiableAt.const_mul
                  <;> (apply DifferentiableAt.cos
                  <;> (apply DifferentiableAt.log
                    <;> (apply DifferentiableAt.const_sub
                      <;> (apply DifferentiableAt.sin
                        <;> (apply DifferentiableAt.const_mul
                          <;> (apply DifferentiableAt.cos
                            <;> (apply DifferentiableAt.const_sub
                              <;> (apply DifferentiableAt.sin
                                <;> (apply DifferentiableAt.const_mul
                                  <;> (apply DifferentiableAt.id))))))))))))))))))
    rw [deriv_add]
    <;> (rw [deriv_mul]
      <;> (rw [deriv_exp]
        <;> (rw [deriv_pow]
          <;> (rw [deriv_add]
            <;> (rw [deriv_mul]
              <;> (rw [deriv_id]
                <;> (rw [deriv_const_add]
                  <;> (rw [deriv_const_mul]
                    <;> (rw [deriv_cos]
                      <;> (rw [deriv_log]
                        <;> (rw [deriv_const_sub]
                          <;> (rw [deriv_sin]
                            <;> (rw [deriv_const_mul]
                              <;> (rw [deriv_cos]
                                <;> (rw [deriv_const_sub]
                                  <;> (rw [deriv_sin]
                                    <;> (rw [deriv_const_mul]
                                      <;> (rw [deriv_id]
                                        <;> (rw [deriv_const]
                                          <;> (simp
                                            <;> (ring
                                            <;> (field_simp
                                              <;> (ring)))))))))))))))))))))
  simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  field_simp [exp_ne_zero, h_log_ne_zero_15]
  ring_nf
  fun_prop
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]
  <;> simp [exp_ne_zero, h_log_ne_zero_15]

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  rw [deriv_add]
  <;> simp_all [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  apply congr_arg
  ring
  <;> aesop
  <;> aesop
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_mul, deriv_cos, deriv_exp, deriv_log, deriv_pow, deriv_id'',
    deriv_const, deriv_zpow, mul_zero, zero_mul, zero_add, mul_one, one_mul, add_zero]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19, Real.exp_ne_zero]
  ring_nf
  <;> simp [mul_assoc]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_mul, deriv_mul, deriv_mul]
  simp [h_log_ne_zero_15, h_log_ne_zero_19, Real.exp_ne_zero, Real.cos_ne_zero, Real.log_ne_zero,
    mul_assoc, mul_comm, mul_left_comm]
  repeat' rw [deriv_exp]
  simp only [mul_one, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, deriv_exp, deriv_log,
    deriv_add, deriv_mul, deriv_id'', deriv_const']
  ring
  <;> apply Differentiable.exp
  <;> apply Differentiable.log
  <;> apply Differentiable.cos
  <;> apply Differentiable.sin
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.comp
  <;> apply Differentiable.inv
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;
example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  simp [deriv_sin, deriv_exp, deriv_mul, deriv_pow, deriv_add, deriv_id, deriv_const,
    deriv_log, h_div_ne_zero_3, h_log_ne_zero_16]
  field_simp
  ring_nf
  <;> simp [Real.cos_log, Real.sin_log, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  have h₁ : ∀ x : ℝ, cos (log x) ≠ 0 → deriv (fun x => cos (exp x * (x ^ 2 + 3) / cos (log x))) x =
    -sin (exp x * (x ^ 2 + 3) / cos (log x)) *
      (((exp x * (x ^ 2 + 3) + exp x * (2 * x)) * cos (log x) - exp x * (x ^ 2 + 3) * (-sin (log x) * (1 / x))) /
        cos (log x) ^ 2) := by
    intro x hx
    field_simp [hx, cos_ne_zero_iff]
    simp only [deriv_cos, deriv_exp, deriv_pow, deriv_add, deriv_id'', deriv_const,
      deriv_mul, deriv_div, deriv_log, deriv_neg, deriv_id, mul_one, mul_zero, sub_zero,
      mul_comm (Real.exp x), mul_assoc, mul_left_comm]
    ring_nf
    <;> field_simp
    <;> ring
  simpa using h₁ x h_div_ne_zero_3

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / Real.cos ((Real.log (x)))) ≠ 0) (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) ^ 2 := by
  have h_cos_ne_zero_1 : Real.cos ((Real.log x)) ≠ 0 := by
    intro h_cos_log_zero
    simp_all
  have h_cos_ne_zero_2 : Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) ≠ 0 := by
    intro h_cos_exp_zero
    simp_all
  field_simp [Real.tan_eq_sin_div_cos, h_cos_ne_zero_1, h_cos_ne_zero_2, h_log_ne_zero_16]
  ring_nf
  field_simp [Real.tan_eq_sin_div_cos, h_cos_ne_zero_1, h_cos_ne_zero_2, h_log_ne_zero_16]
  rw [← sub_eq_zero]
  field_simp [Real.tan_eq_sin_div_cos, h_cos_ne_zero_1, h_cos_ne_zero_2, h_log_ne_zero_16]
  rw [← sub_eq_zero]
  field_simp [Real.tan_eq_sin_div_cos, h_cos_ne_zero_1, h_cos_ne_zero_2, h_log_ne_zero_16]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  have h1 : ∀ x : ℝ, cos (log x) ≠ 0 → x ≠ 0 →
    deriv (fun x => exp (exp x * (x ^ 2 + 3) / cos (log x))) x =
      exp (exp x * (x ^ 2 + 3) / cos (log x)) *
        (((exp x * (x ^ 2 + 3) + exp x * (2 * x)) * cos (log x) - exp x * (x ^ 2 + 3) * (-1 * sin (log x) * (1 / x))) /
          cos (log x) ^ 2) := by
    intro x h_cos h_x
    rw [deriv_exp (exp x * (x ^ 2 + 3) / cos (log x))]
    field_simp [h_cos, h_x, Real.exp_ne_zero]
    ring_nf
    rw [Real.exp_log] <;> simp [h_x, Real.exp_ne_zero]
    field_simp [h_cos, Real.exp_ne_zero]
    ring_nf
  exact h1 x h_div_ne_zero_3 h_log_ne_zero_16

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / Real.cos ((Real.log (x)))) ≠ 0) (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) / (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) := by
  simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_assoc]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_assoc]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_assoc]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_assoc]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  rw [deriv_mul]
  simp [deriv_exp, h_log_ne_zero_15, deriv_pow, deriv_add, deriv_mul, deriv_id, deriv_const,
    deriv_log, mul_add, mul_one, mul_assoc, mul_comm]
  field_simp [h_div_ne_zero_2, Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  ring_nf
  <;> norm_num
  <;> apply IsUnit.mk0
  <;> norm_num

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  funext x
  rw [← sub_eq_zero]
  simp [mul_assoc, mul_comm, mul_left_comm, mul_sub, mul_add]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp_all [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const,
    mul_comm, mul_left_comm, mul_assoc]
  field_simp
  ring
  <;> simp_all [Real.cos_log_of_pos, Real.sin_log_of_pos, Real.cos_log_of_neg, Real.sin_log_of_neg]

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [mul_add, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.cos_ne_zero_iff]
  ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  field_simp [Real.cos_log, h_div_ne_zero_2, h_log_ne_zero_15, mul_add, mul_comm, mul_left_comm]
  ring_nf
  rw [add_comm]
  field_simp [Real.cos_log, h_div_ne_zero_2, h_log_ne_zero_15, mul_add, mul_comm, mul_left_comm]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₁ : deriv (fun x => exp x * (x ^ 2 + 3) / cos (log x) * (sin (2 * x - 1)) ^ 2) x =
      ((((exp x * (x ^ 2 + 3)) + (exp x * (2 * x))) * cos (log x) - (exp x * (x ^ 2 + 3)) * ((-1) * sin (log x) * (1 / x))) / cos (log x) ^ 2 *
        (sin (2 * x - 1)) ^ 2) +
        ((exp x * (x ^ 2 + 3)) / cos (log x)) * (2 * sin (2 * x - 1) * (cos (2 * x - 1) * 2)) := by
    sorry
  simp_all

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const', deriv_log']
  <;> field_simp
  <;> ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  have h₀ : ∀ x, Real.exp x ≠ 0 := fun x => Real.exp_ne_zero x
  have h₁ : ∀ x : ℝ, x ^ 2 + (3:ℝ) ≠ 0 := fun x => by positivity
  have h₂ : ∀ x : ℝ, x ^ 3 ≠ 0 := fun x => by positivity
  have h₃ : ∀ x : ℝ, Real.log x ≠ 0 → x ≠ 0 := fun x h => by rwa [Real.log_ne_zero] at h
  have h₄ : ∀ x : ℝ, Real.log (5:ℝ) ≠ 0 := fun x => by norm_num
  have h₅ : ∀ x : ℝ, x ≠ 0 → Real.cos (Real.log x) ≠ 0 := fun x hx => by
    have : Real.log x ≠ 0 := hx
    simpa only [Real.cos_log] using hx
  have h₆ : ∀ x : ℝ, x ≠ 0 → Real.log x / Real.log (5:ℝ) ≠ 0 := fun x hx => by
    have : Real.log x ≠ 0 := hx
    have : Real.log (5:ℝ) ≠ 0 := by norm_num
    exact div_ne_zero this this
  field_simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆]
  ring
  <;> simp_all
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h : ∀ x : ℝ, cos (log x) = 0 → x = -1 ∨ x = 1 := by
    intro x hx
    have h' : log x = π / 2 ∨ log x = -π / 2 := by
      rw [← cos_eq_zero_iff]
      exact hx
    cases' h' with h' h'
    · rw [← exp_log_eq_id (by positivity : 0 < x)] at h'
      rw [← exp_pi_div_two] at h'
      nlinarith [exp_pos (π / 2)]
    · rw [← exp_log_eq_id (by positivity : 0 < x)] at h'
      rw [← exp_neg_pi_div_two] at h'
      nlinarith [exp_pos (-π / 2)]
  have h₁ : ∀ x : ℝ, cos (log x) = 0 → x = -1 ∨ x = 1 := by
    intro x hx
    have h' : log x = π / 2 ∨ log x = -π / 2 := by
      rw [← cos_eq_zero_iff]
      exact hx
    cases' h' with h' h'
    · rw [← exp_log_eq_id (by positivity : 0 < x)] at h'
      rw [← exp_pi_div_two] at h'
      nlinarith [exp_pos (π / 2)]
    · rw [← exp_log_eq_id (by positivity : 0 < x)] at h'
      rw [← exp_neg_pi_div_two] at h'
      nlinarith [exp_pos (-π / 2)]
  field_simp [*, sub_eq_zero, add_eq_zero_iff_eq_neg] at *
  ring
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h₁ : ∀ x, x ≠ 0 → 5 * x + 2 ≠ 0 → Real.cos (Real.log x) ≠ 0 →
    deriv (fun x => (Real.exp x) * (x ^ 2 + 3) / Real.cos (Real.log x) * (Real.log (5 * x + 2)) ^ 3) x =
      (((((Real.exp x * (x ^ 2 + 3)) + (Real.exp x * (2 * x))) * Real.cos (Real.log x) -
                    (Real.exp x * (x ^ 2 + 3)) * ((-1) * Real.sin (Real.log x) * (1 / x))) /
                  Real.cos (Real.log x) ^ 2) *
                (Real.log (5 * x + 2)) ^ 3) +
            ((Real.exp x * (x ^ 2 + 3)) / Real.cos (Real.log x)) *
              (3 * Real.log (5 * x + 2) ^ 2 * (5 / (5 * x + 2)))) := by
    intro x hx₁ hx₂ hx₃
    rw [deriv_mul]
    · field_simp [hx₁, hx₂, hx₃]
      ring
    · apply DifferentiableAt.mul
      apply DifferentiableAt.div_const
      apply DifferentiableAt.cos
      apply DifferentiableAt.log
      exact differentiableAt_id.const_mul _
      norm_num
      apply DifferentiableAt.pow
      apply DifferentiableAt.log
      exact differentiableAt_id.const_mul _
      norm_num
  simpa using h₁ x h_log_ne_zero_15 h_div_ne_zero_2 h_log_ne_zero_15

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  rw [deriv_sin]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_exp]
  rw [deriv_pow]
  rw [deriv_add]
  rw [deriv_const]
  rw [deriv_pow]
  rw [deriv_const]
  rw [deriv_id]
  rw [deriv_sin]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_const]
  rw [deriv_cos]
  rw [deriv_sub]
  rw [deriv_mul]
  rw [deriv_const]
  rw [deriv_cos]
  rw [deriv_sub]
  rw [deriv_mul]
  rw [deriv_const]
  rw [deriv_sin]
  ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring
  <;> simp
  <;> ring

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  have h1 : ∀ x : ℝ, HasDerivAt (fun x ↦ x ^ 2 + (3:ℝ)) (2 * x) x := fun x ↦ by
    apply HasDerivAt.add_const
    apply HasDerivAt.pow
    simp
  have h2 : ∀ x : ℝ, HasDerivAt (fun x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ))) (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.exp x * (2 * x)) x :=
    fun x ↦ by
      apply HasDerivAt.mul_const
      apply HasDerivAt.exp
      apply HasDerivAt_id
  have h3 : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.sin ((2:ℝ) * x - (1:ℝ))) (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) x :=
    fun x ↦ by
      apply HasDerivAt.comp x
      apply HasDerivAt.sin
      apply HasDerivAt.sub
      apply HasDerivAt.const_mul
      apply HasDerivAt_id
      apply HasDerivAt_const
  have h4 : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.exp x * (2 * x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x :=
    fun x ↦ by
      apply HasDerivAt.add
      apply h2
      apply HasDerivAt.pow
      apply h3
  simp_all
  apply HasDerivAt.comp
  apply HasDerivAt.cos
  apply h4
  apply HasDerivAt.neg
  apply HasDerivAt.sin
  apply h4

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp only [deriv_tan]
  field_simp [h_tan_ne_zero_1]
  ring
  <;> simp only [Real.exp_zero, Real.exp_add, Real.exp_one, mul_one, mul_zero, mul_neg, mul_assoc,
    mul_comm, mul_left_comm, sub_zero, sub_neg_eq_add]
  <;> apply h_tan_ne_zero_1
  <;> apply cos_ne_zero_of_mem_Ioo
  <;> simp only [mem_Ioo, cos_zero, cos_pi_div_two, zero_lt_one, zero_lt_two]
  <;> norm_num

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  rw [deriv_exp (λ x ↦ Real.exp x * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)]
  simp only [deriv_mul (λ x ↦ Real.exp x) (λ x ↦ x ^ 2 + (3:ℝ)), deriv_exp, deriv_pow'', deriv_id'',
    deriv_const', deriv_add, deriv_sin, deriv_sub, deriv_mul, deriv_const, deriv_id]
  ring
  <;> simp only [Real.exp_zero, mul_one, mul_zero, add_zero, zero_add, mul_assoc]
  <;> field_simp <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  rw [deriv_log_of_ne_zero _ h_log_ne_zero_1]
  field_simp
  ring
  <;> simp [mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.exp_ne_zero]

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [mul_add, add_mul, mul_assoc, mul_one, mul_comm, mul_left_comm]
  ring_nf
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_add]
  simp [deriv_exp]
  simp [deriv_pow]
  simp [deriv_sin]
  simp [deriv_cos]
  simp [deriv_id]
  ring_nf
  <;> simp [deriv_exp]
  <;> simp [deriv_pow]
  <;> simp [deriv_sin]
  <;> simp [deriv_cos]
  <;> simp [deriv_id]
  <;> ring_nf

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp [mul_add, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  ring_nf
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp
  intro x
  rw [Real.exp_ne_zero]
  field_simp

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_const_mul]
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_add]
  rw [deriv_const]
  rw [deriv_mul]
  rw [deriv_const]
  rw [deriv_id]
  rw [deriv_sin]
  rw [deriv_const_mul]
  rw [deriv_id]
  rw [deriv_cos]
  rw [deriv_log]
  ring_nf
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h₀ : ∀ x, deriv (fun x => Real.exp x * (x ^ 2 + 3) + (2 * x - 1).sin ^ 2 * Real.cos (Real.log x)) x =
    Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) +
      (2 * (2 * x - 1).sin * (2 * x - 1).cos * Real.cos (Real.log x) +
        (2 * x - 1).sin ^ 2 * (-Real.sin (Real.log x) / x)) := by
    intro x
    rw [deriv_add]
    · rw [deriv_mul]
      · rw [deriv_exp]
        ring
      · rw [deriv_add]
        · rw [deriv_pow_succ]
          simp
          ring
        · simp [deriv_const]
    · rw [deriv_mul]
      · simp [deriv_sin, deriv_cos, deriv_const, deriv_sub, deriv_mul, deriv_id, deriv_pow_succ]
        ring
      · simp [deriv_log']
  simpa [h₀] using h_log_ne_zero_25

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id, deriv_sin,
    deriv_cos, deriv_sub, deriv_neg]
  ring_nf
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, mul_assoc]
  <;> norm_num
  <;> linarith

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₁ : ∀ x : ℝ, HasDerivAt (fun x => rexp x * (x ^ 2 + (3 : ℝ)) + sin (2 * x - 1) ^ 2 * sin (2 * x - 1) ^ 2) (rexp x * (x ^ 2 + 3) + 2 * x * rexp x + 2 * sin (2 * x - 1) * cos (2 * x - 1) * (2 * x - 1) ^ 2 + (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1) * (2 * x - 1)) * 2)) x := by
    intro x
    refine HasDerivAt.add ?_ ?_
    · have h := HasDerivAt.exp (hasDerivAt_id x)
      have h' := HasDerivAt.mul_const (x ^ 2 + (3 : ℝ)) h
      have h'' := HasDerivAt.pow 2 (HasDerivAt.add (HasDerivAt.pow 2 (hasDerivAt_id x)) (hasDerivAt_const x 3))
      have h''' := HasDerivAt.add h' h''
      convert h''' using 1
      ring
    · have h := HasDerivAt.sin (HasDerivAt.sub (HasDerivAt.const_mul 2 (hasDerivAt_id x)) (hasDerivAt_const x 1))
      have h' := HasDerivAt.mul_const (sin (2 * x - 1) ^ 2) h
      have h'' := HasDerivAt.pow 2 (HasDerivAt.sin (HasDerivAt.sub (HasDerivAt.const_mul 2 (hasDerivAt_id x)) (hasDerivAt_const x 1)))
      have h''' := HasDerivAt.mul_const (sin (2 * x - 1) ^ 2) h''
      convert h''' using 1
      ring
  convert (h₁ x).deriv using 1
  simp only [add_assoc, add_left_comm, add_comm]
  ring

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const', deriv_sin,
    deriv_sub, deriv_cos, deriv_neg, deriv_log, one_div]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  field_simp
  ring
  <;> simp_all [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  rw [deriv_add]
  <;> simp [deriv_exp, deriv_mul, deriv_add, deriv_add, deriv_pow, deriv_const, deriv_id,
    deriv_sin, deriv_cos, deriv_log, h_log_ne_zero_25]
  <;> ring
  <;> intro h
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h₁ : ∀ x : ℝ, x ^ 2 = x * x := by intro x; ring
  simp only [h₁, add_assoc, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  simp only [mul_one, mul_zero, add_zero, mul_assoc]
  field_simp
  ring_nf

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [deriv_sin, deriv_add, deriv_mul, deriv_sub, deriv_exp, deriv_pow, deriv_id, deriv_const,
    deriv_sin, deriv_cos, deriv_comp, deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub,
    deriv_cos, deriv_sin, deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_cos,
    deriv_sin]
  ring
  <;> simp [Real.exp_ne_zero]
  <;> field_simp
  <;> ring
  <;> simp [Real.exp_ne_zero]
  <;> field_simp
  <;> ring
  <;> simp [Real.exp_ne_zero]
  <;> field_simp
  <;> ring
  <;> simp [Real.exp_ne_zero]
  <;> field_simp
  <;> ring

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [sub_eq_add_neg, neg_mul, mul_add, mul_neg, neg_add_rev, neg_neg]
  field_simp [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring
  <;> simp only [sub_eq_add_neg, neg_mul, mul_add, mul_neg, neg_add_rev, neg_neg]
  <;> field_simp [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp only [one_mul, sub_eq_add_neg, ← mul_add, mul_comm]
  rw [deriv_tan_comp]
  <;> simp only [Real.cos_add, Real.sin_add, mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp <;> linarith [Real.cos_ne_zero_iff.mpr h_tan_ne_zero_1]

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [deriv_exp]
  simp only [mul_one, mul_zero, add_zero, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm,
    Function.comp_apply, deriv_add, deriv_sub, deriv_mul_const_field, deriv_const_mul_field,
    deriv_exp, deriv_sin, deriv_id'', deriv_const', deriv_pow'', deriv_id, Nat.cast_one, pow_one]
  ring
  <;> simp only [Real.exp_zero, zero_mul, zero_add, mul_zero, sub_zero, zero_sub, mul_neg, neg_mul,
    neg_neg, mul_one, sub_neg_eq_add, add_comm, add_left_comm, add_assoc]
  <;> apply congr_arg
  <;> ring

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  rw [deriv_log_of_pos] <;>
    field_simp <;>
    ring_nf <;>
    linarith [sin_le_one (2 * x - 1), cos_le_one (2 * x - 1)]

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add, deriv_add, deriv_add, deriv_add, deriv_add]
  <;> simp_all [deriv_exp, deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_sub, deriv_sin,
    deriv_cos, deriv_neg]
  <;> linarith
  <;> ring_nf
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.sub
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.neg
  <;> simp

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x))) := by
  rw [deriv_sub]
  <;> simp [*, deriv_exp, deriv_mul, deriv_add, deriv_pow, deriv_const, deriv_id, deriv_sin, deriv_cos,
    deriv_sub, deriv_neg, deriv_inv, deriv_pow, deriv_const, deriv_id, deriv_sin, deriv_cos,
    deriv_sub, deriv_neg, deriv_inv, deriv_pow, deriv_const, deriv_id, deriv_sin, deriv_cos,
    deriv_sub, deriv_neg, deriv_inv, deriv_pow, deriv_const, deriv_id, deriv_sin, deriv_cos]
  <;> ring
  <;> norm_num
  <;> apply DifferentiableAt.exp <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.add
    <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.const <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.sin <;> apply DifferentiableAt.cos <;> apply DifferentiableAt.sub
    <;> apply DifferentiableAt.neg <;> apply DifferentiableAt.inv
  <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.const <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.sin <;> apply DifferentiableAt.cos <;> apply DifferentiableAt.sub
    <;> apply DifferentiableAt.neg <;> apply DifferentiableAt.inv
  <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.const <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.sin <;> apply DifferentiableAt.cos

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  fun_conv => field_simp <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> ring_nf
  <;> simp only [IsFractionRing.injective]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp
  <;> simp only [mul_assoc]
  <;> apply IsFractionRing.injective
  <;> simp only [mul_assoc]
  <;> field_simp

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h_log_ne_zero_25: x ≠ 0 := by
    intro h
    simp_all
  simp_all [Real.exp_ne_zero]
  field_simp
  ring_nf
  <;> simp only [Real.exp_ne_zero, mul_one, mul_zero, sub_zero, zero_add, add_zero]
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on
  <;> apply Differentiable.comp_of_differentiable_on

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [add_sub_cancel, add_assoc, add_right_comm, add_left_comm]
  rw [deriv_sub, deriv_add]
  <;> simp only [mul_one, mul_zero, mul_neg, mul_comm, mul_assoc]
  <;> ring_nf
  <;> simp only [deriv_exp, deriv_sin, deriv_id'', deriv_const']
  <;> ring_nf
  <;> simp only [deriv_exp, deriv_sin, deriv_id'', deriv_const']
  <;> ring_nf
  <;> simp only [deriv_exp, deriv_sin, deriv_id'', deriv_const']
  <;> ring_nf
  <;> simp only [deriv_exp, deriv_sin, deriv_id'', deriv_const']
  <;> ring_nf

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  funext x
  simp only [deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const, deriv_sin,
    deriv_add, deriv_sub_const, deriv_mul_const, deriv_mul_const', deriv_comp, deriv_pow'',
    deriv_id, deriv_const']
  ring
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.comp
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_sub]
  rw [deriv_mul]
  rw [deriv_exp]
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_add]
  simp [deriv_sin, deriv_cos, deriv_mul, deriv_const]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_sub, deriv_mul, deriv_mul, deriv_zpow, deriv_exp, deriv_exp]
  <;> simp [h_log_ne_zero_30, h_log_ne_zero_32, h_div_ne_zero_29]
  <;> ring
  <;> simp_all
  <;> ring_nf
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.zpow
  <;> apply Differentiable.zpow
  <;> apply Differentiable.exp
  <;> apply Differentiable.sin
  <;> apply Differentiable.sin
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.id
  <;> apply Differentiable.id
  <;> apply Differentiable.id
  <;> apply Differentiable.id
  <;> apply Differentiable.id
  <;> apply Differentiable.id

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp_all [deriv_exp, deriv_add, deriv_mul, deriv_pow, deriv_log, deriv_sin, deriv_cos, deriv_id, deriv_const]
  field_simp [h_log_ne_zero_25]
  ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.log_ne_zero, h_log_ne_zero_25]
  <;> simp [Real.sin_ne_zero, Real.cos_ne_zero]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp [deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_id, deriv_log, deriv_sin, deriv_cos,
    h_log_ne_zero_25]
  ring
  <;> field_simp [h_log_ne_zero_25]
  <;> ring
  <;> field_simp [h_log_ne_zero_25]
  <;> ring
  <;> field_simp [h_log_ne_zero_25]
  <;> ring
  <;> field_simp [h_log_ne_zero_25]
  <;> ring
  <;> field_simp [h_log_ne_zero_25]

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [sin_sq, cos_sq, mul_one, mul_zero, sub_zero, zero_add]
  ring_nf
  simp only [Real.deriv_exp, Real.deriv_sin, mul_one, mul_zero, sub_zero, zero_add, mul_add, mul_comm]
  field_simp
  ring
  <;> simp only [Real.deriv_exp, Real.deriv_sin, mul_one, mul_zero, sub_zero, zero_add, mul_add, mul_comm]
  <;> field_simp
  <;> ring
  <;> simp only [Real.deriv_exp, Real.deriv_sin, mul_one, mul_zero, sub_zero, zero_add, mul_add, mul_comm]
  <;> field_simp
  <;> ring

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [Real.cos_exp_mul_add_sq_mul_sin_sq, mul_add, mul_one, mul_sub, mul_comm]
  rw [deriv_cos, deriv_exp]
  ring_nf
  <;> simp [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [Real.cos_exp_mul_add_sq_mul_sin_sq, mul_add, mul_one, mul_sub, mul_comm]
  <;> rw [deriv_cos, deriv_exp]
  <;> ring_nf
  <;> simp [mul_assoc, mul_comm, mul_left_comm]
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp_all [Real.deriv_tan, mul_pow]
  field_simp [h_tan_ne_zero_1, Real.cos_eq_zero_iff]
  ring_nf
  <;> simp_all [Real.deriv_tan, mul_pow]

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₀ : ∀ x : ℝ, 0 < exp x := fun _ ↦ exp_pos _
  have h₁ : ∀ x : ℝ, 0 < exp (exp x) := fun _ ↦ exp_pos _
  have h₂ : ∀ x : ℝ, 0 < exp (x ^ 2 + 3) := fun _ ↦ exp_pos _
  have h₃ : ∀ x : ℝ, 0 < exp (2 * x - 1) := fun _ ↦ exp_pos _
  have h₄ : ∀ x : ℝ, 0 < exp (sin (2 * x - 1)) := fun _ ↦ exp_pos _
  have h₅ : ∀ x : ℝ, 0 < exp (cos (2 * x - 1)) := fun _ ↦ exp_pos _
  have h₆ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * sin (2 * x - 1) ^ 2) := fun _ ↦ exp_pos _
  have h₇ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * sin (2 * x - 1) ^ 2 * cos (2 * x - 1)) :=
    fun _ ↦ exp_pos _
  have h₈ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1))) :=
    fun _ ↦ exp_pos _
  have h₉ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₀ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₁ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₂ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₃ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₄ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₅ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₆ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₇ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₈ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₁₉ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₀ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₁ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₂ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₃ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₄ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₅ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₆ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₇ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₈ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₂₉ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₃₀ : ∀ x : ℝ, 0 < exp (exp x * (x ^ 2 + 3) * (sin (2 * x - 1) ^ 2 * (2 * cos (2 * x - 1)))) :=
    fun _ ↦ exp_pos _
  have h₃₁ : ∀ x : ℝ, 0 < exp (exp x
example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  have h1 : ∀ x : ℝ, 0 < exp x := fun x => exp_pos x
  have h2 : ∀ x : ℝ, 0 < Real.sqrt (x ^ 2 + 3) := fun x => Real.sqrt_pos.mpr (by nlinarith)
  have h3 : ∀ x : ℝ, 0 < sin (2 * x - 1) := fun x => by
    apply sin_pos_of_pos_of_lt_pi
    · nlinarith
    · nlinarith [Real.pi_pos]
  have h4 : ∀ x : ℝ, 0 < Real.sin (2 * x - 1) ^ 2 := fun x => sq_pos_of_pos (h3 x)
  field_simp [*, log_mul, log_exp, log_rpow]
  ring_nf
  <;> field_simp [h1, h2, h3, h4]
  <;> ring
  <;> field_simp [h1, h2, h3, h4]
  <;> ring
  <;> field_simp [h1, h2, h3, h4]
  <;> ring

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [mul_assoc, mul_add, mul_comm, mul_left_comm]
  rw [deriv_add]
  <;> simp only [deriv_mul, deriv_exp, deriv_pow, Nat.cast_two, deriv_id'', deriv_const', deriv_sin,
    deriv_sub, deriv_mul, deriv_exp, deriv_pow, Nat.cast_two, deriv_id'', deriv_const', deriv_sin,
    deriv_sub, deriv_mul, deriv_exp, deriv_pow, Nat.cast_two, deriv_id'', deriv_const', deriv_sin,
    deriv_sub]
  <;> ring_nf
  <;> simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_zero, Complex.ofReal_two, Complex.ofReal_neg, Complex.ofReal_exp, Complex.ofReal_cos,
    Complex.ofReal_sin, Complex.ofReal_pow]
  <;> apply HasDerivAt.add <;> simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_two, Complex.ofReal_neg, Complex.ofReal_exp,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_pow] <;> apply HasDerivAt.mul <;> simp only
  <;> apply HasDerivAt.exp <;> apply HasDerivAt.pow <;> apply HasDerivAt.id <;> apply HasDerivAt.const' <;>
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_zero, Complex.ofReal_two, Complex.ofReal_neg, Complex.ofReal_exp, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.ofReal_pow] <;> apply HasDerivAt.sin <;> apply HasDerivAt.sub <;> simp only
  <;> apply HasDerivAt.mul_const <;> apply HasDerivAt.const_mul <;> simp only
  <;> apply HasDerivAt.cos <;> simp only
  <;> field_simp <;> linarith

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  <;> aesop
  <;> simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> aesop
  <;> simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> aesop
  <;> simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [add_mul, mul_add, mul_comm, mul_left_comm]
  rw [add_comm]
  field_simp
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> simp only [add_assoc, add_left_comm, add_comm]
  <;> simp only [sub_eq_add_neg]
  <;> ring_nf
  <;> simp only [Real.exp_add, Real.exp_mul, Real.exp_log]
  <;> simp only [Real.cos_add, Real.cos_mul, Real.cos_log, Real.sin_add, Real.sin_mul, Real.sin_log]
  <;> simp only [Real.exp_zero, Real.cos_zero, Real.sin_zero]
  <;> simp only [Real.exp_ne_zero]
  <;> simp only [Real.cos_ne_zero, Real.sin_ne_zero]
  <;> simp only [add_right_inj, mul_right_inj]
  <;> simp only [add_left_inj, mul_left_inj]
  <;> simp only [add_comm, mul_comm]
  <;> simp only [add_assoc, mul_assoc]
  <;> simp only [add_left_comm, mul_left_comm]
  <;> simp only [sub_eq_add_neg]
  <;> ring_nf
  <;> simp only [Real.exp_add, Real.exp_mul, Real.exp_log]
  <;> simp only [Real.cos_add, Real.cos_mul, Real.cos_log, Real.sin_add, Real.sin_mul, Real.sin_log]
  <;> simp only [Real.exp_zero, Real.cos_zero, Real.sin_zero]
  <;> simp only [Real.exp_ne_zero]
  <;> simp only [Real.cos_ne_zero, Real.sin_ne_zero]
  <;> simp only [add_right_inj, mul_right_inj]
  <;> simp only [add_left_inj, mul_left_inj]
  <;> simp only [add_comm, mul_comm]
  <;> simp only [add_assoc, mul_assoc]
  <;> simp only [add_left_comm, mul_left_comm]
  <;> simp only [sub_eq_add_neg]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  apply HasDerivAt.deriv
  have h1 : HasDerivAt (fun x => Real.exp x * (x ^ 2 + (3 : ℝ)))
      (Real.exp x * (x ^ 2 + (3 : ℝ)) + Real.exp x * (2 * x)) x :=
    by
    apply HasDerivAt.mul
    · exact hasDerivAt_exp x
    · apply HasDerivAt.add
      · apply HasDerivAt.pow
        exact hasDerivAt_id x
      · exact hasDerivAt_const x 3
  have h2 : HasDerivAt (fun x => (Real.sin ((2 : ℝ) * x - (1 : ℝ))) ^ 2)
      (2 * Real.sin ((2 : ℝ) * x - (1 : ℝ)) * Real.cos ((2 : ℝ) * x - (1 : ℝ)) * (2 : ℝ)) x :=
    by
    apply HasDerivAt.pow
    apply HasDerivAt.sin
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      exact hasDerivAt_id x
    · exact hasDerivAt_const x 1
  have h3 : HasDerivAt (fun x => Real.cos (Real.log x))
      (-(Real.sin (Real.log x) * (1 / x))) x :=
    by
    apply HasDerivAt.comp
    · exact hasDerivAt_cos (Real.log x)
    · apply HasDerivAt.log
      exact hasDerivAt_id x
      exact h_log_ne_zero_25
  apply HasDerivAt.mul
  · apply HasDerivAt.mul
    · exact h1
    · exact h2
  · exact h3

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_sin, deriv_id, deriv_const]
  ring
  <;> simp only [Real.exp_zero, mul_one, zero_add, mul_zero, add_zero, mul_neg, mul_one, sub_neg_eq_add,
    mul_assoc]
  <;> ring
  <;> simp only [Real.exp_zero, mul_one, zero_add, mul_zero, add_zero, mul_neg, mul_one, sub_neg_eq_add,
    mul_assoc]
  <;> ring
  <;> simp only [Real.exp_zero, mul_one, zero_add, mul_zero, add_zero, mul_neg, mul_one, sub_neg_eq_add,
    mul_assoc]
  <;> ring

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [deriv_mul, deriv_exp, deriv_add, deriv_rpow_const, deriv_sin, deriv_cos, deriv_id,
    deriv_const, deriv_mul, deriv_exp, deriv_add, deriv_rpow_const, deriv_sin, deriv_cos,
    deriv_id, deriv_const, deriv_mul, deriv_exp, deriv_add, deriv_rpow_const, deriv_sin,
    deriv_cos, deriv_id, deriv_const, deriv_mul, deriv_exp, deriv_add, deriv_rpow_const,
    deriv_sin, deriv_cos, deriv_id, deriv_const]
  ring
  <;> simp only [Real.exp_ne_zero]
  <;> apply mul_comm
  <;> norm_num
  <;> ring
  <;> simp only [Real.exp_ne_zero]
  <;> apply mul_comm
  <;> norm_num
  <;> ring
  <;> simp only [Real.exp_ne_zero]
  <;> apply mul_comm
  <;> norm_num
  <;> ring
  <;> simp only [Real.exp_ne_zero]
  <;> apply mul_comm
  <;> norm_num

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [*, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, Real.log_mul, Real.log_pow,
    Real.log_inv, Real.log_div, Real.log_one, Real.log_mul, Real.log_pow, Real.log_inv,
    Real.log_div, Real.log_one, Real.log_mul, Real.log_pow, Real.log_inv, Real.log_div,
    Real.log_one, Real.log_mul, Real.log_pow, Real.log_inv, Real.log_div, Real.log_one]
  field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_div, Real.log_one, Real.log_mul,
    Real.log_pow, Real.log_inv, Real.log_div, Real.log_one, Real.log_mul, Real.log_pow,
    Real.log_inv, Real.log_div, Real.log_one, Real.log_mul, Real.log_pow, Real.log_inv,
    Real.log_div, Real.log_one]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_id, deriv_const, mul_add, add_mul, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_30, h_div_ne_zero_29, h_log_ne_zero_32]
  ring
  <;> simp [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_30, h_div_ne_zero_29, h_log_ne_zero_32]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  apply congrArg
  funext
  simp [*, mul_add, mul_sub, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc,
    add_sub_assoc, add_comm, add_left_comm, sub_eq_add_neg]
  ring_nf
  field_simp
  ring_nf
  <;> apply congrArg
  <;> funext
  <;> simp [*, mul_add, mul_sub, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc,
    add_sub_assoc, add_comm, add_left_comm, sub_eq_add_neg]
  <;> ring_nf
  <;> field_simp
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp [deriv_mul, deriv_exp, deriv_pow, deriv_sin, deriv_cos, deriv_id, deriv_const,
    deriv_add, deriv_sub, deriv_mul, deriv_log, deriv_comp, deriv_pow]
  field_simp
  ring
  <;> simp [h_log_ne_zero_25]
  <;> field_simp
  <;> ring
  <;> simp [h_log_ne_zero_25]
  <;> field_simp
  <;> ring
  <;> simp [h_log_ne_zero_25]
  <;> field_simp
  <;> ring
  <;> simp [h_log_ne_zero_25]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  simp only [one_mul, mul_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_right_comm]
  have h_sin_ne_zero : Real.sin ((2 * x - 1)) ≠ 0 := by
    intro h_sin
    apply h_div_ne_zero_3
    simp [h_sin]
  have h_cos_ne_zero : Real.cos ((2 * x - 1)) ≠ 0 := by
    intro h_cos
    rw [← sin_eq_zero_iff] at h_cos
    have h_cos_2 : 2 * x - 1 = π / 2 ∨ 2 * x - 1 = 3 * π / 2 := by
      exact h_cos
    cases' h_cos_2 with h_cos_2 h_cos_2
    · linarith
    · linarith
  field_simp [h_sin_ne_zero, h_cos_ne_zero]
  ring
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  simp_all [deriv_cos, deriv_exp, deriv_mul, deriv_id'', deriv_pow, deriv_const,
    deriv_sub, deriv_neg, deriv_sin]
  field_simp
  ring
  <;> simp_all [Real.sin_two_mul, Real.cos_two_mul]
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp_all [deriv_tan, deriv_div, deriv_mul, deriv_pow]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  have h₀ : ∀ x : ℝ, HasDerivAt (fun x => x ^ 2 + 3) (2 * x) x := by
    intro x
    apply HasDerivAt.add
    apply HasDerivAt.pow
    apply hasDerivAt_id
    apply hasDerivAt_const
  have h₁ : ∀ x : ℝ, HasDerivAt (fun x => sin (2 * x - 1)) (2 * cos (2 * x - 1)) x := by
    intro x
    have h := HasDerivAt.comp x (hasDerivAt_sin (2 * x - 1)) (hasDerivAt_sub (hasDerivAt_const x 2) (hasDerivAt_const x 1))
    simp only [mul_one, sub_zero, mul_zero, add_zero] at h
    convert h using 1
    ring
  have h₂ : ∀ x : ℝ, HasDerivAt (fun x => sin (2 * x - 1) ^ 2) (2 * cos (2 * x - 1) * sin (2 * x - 1)) x := by
    intro x
    have h := HasDerivAt.pow 2 (h₁ x)
    simp only [Nat.cast_two, pow_two] at h
    convert h using 1
    ring
  have h₃ : ∀ x : ℝ, HasDerivAt (fun x => exp (x ^ 2 + 3)) (exp (x ^ 2 + 3) * (2 * x)) x := by
    intro x
    have h := HasDerivAt.exp (hasDerivAt_add (hasDerivAt_pow 2 x) (hasDerivAt_const x 3))
    simp only [Nat.cast_two, pow_two] at h
    convert h using 1
    ring
  have h₄ : ∀ x : ℝ, HasDerivAt (fun x => exp ((x ^ 2 + 3) / sin (2 * x - 1) ^ 2))
    (exp ((x ^ 2 + 3) / sin (2 * x - 1) ^ 2) * ((2 * x * (sin (2 * x - 1) ^ 2) - (x ^ 2 + 3) * (2 * cos (2 * x - 1) * sin (2 * x - 1))) / (sin (2 * x - 1) ^ 2) ^ 2)) x := by
    intro x
    have h := HasDerivAt.exp (hasDerivAt_div (h₃ x) (h₂ x) (h_div_ne_zero_3 x))
    simp only [Nat.cast_two, pow_two] at h
    convert h using 1
    ring
  have h₅ : ∀ x : ℝ, HasDerivAt (fun x => exp (exp x * (x ^ 2 + 3) / sin (2 * x - 1) ^ 2))
    (exp (exp x * (x ^ 2 + 3) / sin (2 * x - 1) ^ 2) * (exp x * (x ^ 2 + 3) / sin (2 * x - 1) ^ 2 + exp x * ((2 * x * (sin (2 * x - 1) ^ 2) - (x ^ 2 + 3) * (2 * cos (2 * x - 1) * sin (2 * x - 1))) / (sin (2 * x - 1) ^ 2) ^ 2))) x := by
    intro x
    have h := HasDerivAt.exp (h₄ x)
    simp only [Nat.cast_two, pow_two] at h
    convert h using 1
    ring
  exact h₅ x

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  rw [deriv_log_div ((by nlinarith [h_div_ne_zero_3]) : ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0))]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_3]

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc]
  simp only [inv_pow]
  field_simp
  ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.cos_ne_zero_iff]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, Real.exp_ne_zero]
  ring_nf
  <;> simp only [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, Real.exp_ne_zero]
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, Real.exp_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h₁ : ∀ x, (sin (2 * x - 1)) ^ 2 ≠ 0 → x ≠ 0 →
    deriv (fun x => (Real.exp x) * (x ^ 2 + 3) / (sin (2 * x - 1)) ^ 2 + cos (Real.log x)) x =
      (((Real.exp x * (x ^ 2 + 3)) + (Real.exp x * (2 * x))) * (sin (2 * x - 1)) ^ 2 -
            (Real.exp x * (x ^ 2 + 3)) * (2 * sin (2 * x - 1) * cos (2 * x - 1) * 2)) /
          (sin (2 * x - 1)) ^ 4 +
        -sin (Real.log x) * (1 / x) := by
    intro x h₁ h₂
    rw [deriv_add]
    · field_simp [h₁, h₂, sin_zero, cos_zero, exp_ne_zero]
      ring
    · apply DifferentiableAt.div_const
      apply DifferentiableAt.mul
      · apply DifferentiableAt.exp
        exact differentiableAt_id
      · apply DifferentiableAt.pow
        apply DifferentiableAt.add
        · exact differentiableAt_id
        · exact differentiableAt_const _
      exact h₁
    · apply DifferentiableAt.cos
      apply DifferentiableAt.log
      exact differentiableAt_id
      exact h₂
  simpa using h₁ x h_div_ne_zero_2 h_log_ne_zero_25

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h1 : ∀ x, 0 < x → 0 < sin (2 * x - 1) := fun x hx ↦ by
    have h2 : 0 < sin (2 * x - 1) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    simpa using h2
  have h2 : ∀ x, 0 < x → 0 < cos (2 * x - 1) := fun x hx ↦ by
    have h2 : 0 < cos (2 * x - 1) := by
      apply Real.cos_pos_of_mem_Ioo
      · constructor
        · linarith
        · linarith [Real.pi_pos]
    simpa using h2
  have h3 : ∀ x, 0 < x → 0 < cos (log x) := fun x hx ↦ by
    have h2 : 0 < cos (log x) := by
      apply Real.cos_pos_of_mem_Ioo
      · constructor
        · linarith [Real.log_pos hx]
        · linarith [Real.log_neg hx]
    simpa using h2
  field_simp [h_div_ne_zero_2, h_log_ne_zero_25]
  ring
  <;>
    simp only [deriv_exp, deriv_log, deriv_cos, deriv_sin, deriv_id'', deriv_const',
      deriv_mul, deriv_div, deriv_pow, deriv_add, deriv_sub, deriv_neg, deriv_inv,
      deriv_comp, deriv_pow, deriv_add, deriv_sub, deriv_neg, deriv_inv, deriv_comp,
      deriv_pow, deriv_add, deriv_sub, deriv_neg, deriv_inv, deriv_comp, deriv_pow,
      deriv_add, deriv_sub, deriv_neg, deriv_inv, deriv_comp]
  <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_div, Complex.ofReal_exp, Complex.ofReal_log, Complex.ofReal_cos,
      Complex.ofReal_sin, Complex.ofReal_sqrt, Complex.ofReal_num, Complex.ofReal_denom]
  <;>
    simp only [add_assoc, add_left_comm, add_right_comm, mul_assoc, mul_left_comm,
      mul_right_comm, sub_eq_add_neg, neg_add_rev, neg_mul_eq_neg_mul_symm, neg_neg,
      Complex.I_sq, Complex.I_mul_I, neg_one_mul, one_mul, Complex.exp_add, Complex.exp_neg,
      Complex.exp_sub, Complex.exp_mul_I, Complex.exp_pow]
  <;>
    simp only [Complex.cos_add, Complex.cos_neg, Complex.cos_sub, Complex.cos_mul_I,
      Complex.sin_add, Complex.sin_neg, Complex.sin_sub, Complex.sin_mul_I, Complex.cos_log,
      Complex.sin_log, Complex.cos_exp, Complex.sin_exp]
  <;>
    simp only [add_assoc, add_left_comm, add_right_comm, mul_assoc, mul_left_comm,
      mul_right_comm, sub_eq_add_neg, neg_add_rev, neg_mul_eq_neg_mul_symm, neg_neg,
      Complex.I_sq, Complex.I_mul_I, neg_one_mul, one_mul, Complex.exp_add, Complex.exp_neg,
      Complex.exp_sub, Complex.exp_mul_I, Complex.exp_pow]
  <;>
    simp only [Complex.cos_add, Complex.cos_neg, Complex.cos_sub, Complex.cos_mul_I,
      Complex.sin_add, Complex.sin_neg, Complex.sin_sub, Complex.sin_mul_I, Complex.cos_log,
      Complex.sin_log, Complex.cos_exp, Complex.sin_exp]
  <;>
    linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [div_eq_mul_inv]
  field_simp [h_div_ne_zero_2]
  ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> apply Differentiable.deriv_eq_zero
  <;> apply Differentiable.mul
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.add
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.mul
  <;> apply Differentiable.sin
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.mul
  <;> apply Differentiable.cos
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [deriv_mul, deriv_exp, deriv_add, deriv_pow, deriv_id, deriv_const,
    deriv_sin, deriv_cos, deriv_mul_const, deriv_const_mul, deriv_comp, deriv_div,
    deriv_pow, deriv_id, deriv_const, deriv_sin, deriv_cos, deriv_mul_const, deriv_const_mul,
    deriv_comp, deriv_div, deriv_pow, deriv_id, deriv_const, deriv_sin, deriv_cos, deriv_mul_const,
    deriv_const_mul, deriv_comp, deriv_div, deriv_pow, deriv_id, deriv_const, deriv_sin, deriv_cos,
    deriv_mul_const, deriv_const_mul, deriv_comp, deriv_div, deriv_pow, deriv_id, deriv_const,
    deriv_sin, deriv_cos, deriv_mul_const, deriv_const_mul, deriv_comp, deriv_div]
  field_simp
  ring
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_id, deriv_const]
  field_simp
  ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.log_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sqrt_ne_zero_iff]
  <;> simp [Real.exp_ne_zero]
  <;> simp [Real.log_ne_zero_iff]
  <;> simp [Real.sin_ne_zero_iff]
  <;> simp [Real.cos_ne_zero_iff]
  <;> simp [Real.sqrt_ne_zero_iff]

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  field_simp [h_div_ne_zero_2, h_log_ne_zero_25, Real.exp_ne_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
    mul_eq_mul_left_iff, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_const,
    deriv_sub, deriv_id, deriv_sin, deriv_cos, deriv_tan, deriv_inv, deriv_pow,
    deriv_log, deriv_exp, deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id,
    deriv_sin, deriv_cos, deriv_tan, deriv_inv, deriv_pow, deriv_log, deriv_exp,
    deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id, deriv_sin, deriv_cos,
    deriv_tan, deriv_inv, deriv_pow, deriv_log, deriv_exp, deriv_add, deriv_mul,
    deriv_const, deriv_sub, deriv_id, deriv_sin, deriv_cos, deriv_tan, deriv_inv]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_one, mul_zero,
    mul_neg, mul_add, mul_sub, mul_div_cancel_left, mul_div_cancel_left, mul_div_cancel_left,
    mul_div_cancel_left, mul_div_cancel_left, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_25, Real.exp_ne_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
    mul_eq_mul_left_iff, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_const,
    deriv_sub, deriv_id, deriv_sin, deriv_cos, deriv_tan, deriv_inv, deriv_pow,
    deriv_log, deriv_exp, deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id,
    deriv_sin, deriv_cos, deriv_tan, deriv_inv, deriv_pow, deriv_log, deriv_exp,
    deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id, deriv_sin, deriv_cos,
    deriv_tan, deriv_inv, deriv_pow, deriv_log, deriv_exp, deriv_add, deriv_mul,
    deriv_const, deriv_sub, deriv_id, deriv_sin, deriv_cos, deriv_tan, deriv_inv]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  apply HasDerivAt.deriv
  simp only [mul_div_assoc]
  have h1 : HasDerivAt (λ y ↦ Real.exp y * (y ^ 2 + 3))
      (Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x)) x := by
    have h11 : HasDerivAt (λ y ↦ Real.exp y) (Real.exp x) x := hasDerivAt_exp x
    have h12 : HasDerivAt (λ y ↦ y ^ 2 + 3) (2 * x) x := by
      have h121 : HasDerivAt (λ y ↦ y ^ 2) (2 * x) x := by
        simp only [pow_two]
        exact hasDerivAt_mul_const x
      simp only [add_assoc]
      exact h121.add_const 3
    exact h11.mul h12
  have h2 : HasDerivAt (λ y ↦ (Real.sin ((2:ℝ) * y - (1:ℝ))) ^ 2)
      (2 * Real.cos ((2:ℝ) * x - (1:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ))) x := by
    have h21 : HasDerivAt (λ y ↦ (2:ℝ) * y - (1:ℝ)) 2 x := by
      simp only [mul_comm]
      exact hasDerivAt_mul_const 2
    have h22 : HasDerivAt (λ y ↦ Real.sin y) (Real.cos x) x := hasDerivAt_sin x
    have h23 : HasDerivAt (λ y ↦ Real.cos y) (-Real.sin x) x := hasDerivAt_cos x
    have h24 : HasDerivAt (λ y ↦ Real.sin ((2:ℝ) * y - (1:ℝ))) (2 * Real.cos ((2:ℝ) * x - (1:ℝ))) x :=
      h22.comp x h21
    simp only [pow_two]
    exact h24.mul h24
  have h3 : HasDerivAt (λ y ↦ Real.log ((5:ℝ) * y + (2:ℝ))) (5 / ((5:ℝ) * x + (2:ℝ))) x := by
    have h31 : HasDerivAt (λ y ↦ (5:ℝ) * y + (2:ℝ)) 5 x := by
      simp only [mul_comm]
      exact hasDerivAt_mul_const 5
    have h32 : HasDerivAt (λ y ↦ Real.log y) (5 / ((5:ℝ) * x + (2:ℝ))) x :=
      hasDerivAt_log (by norm_num; linarith) h31
    exact h32
  have h4 : HasDerivAt (λ y ↦ (Real.exp y * (y ^ 2 + 3)) / (Real.sin ((2:ℝ) * y - (1:ℝ)) ^ 2))
      (((((Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) -
        (Real.exp x * (x ^ 2 + 3)) * (2 * Real.cos ((2:ℝ) * x - (1:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)))) /
          (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    have h41 : HasDerivAt (λ y ↦ Real.exp y * (y ^ 2 + 3) / (Real.sin ((2:ℝ) * y - (1:ℝ)) ^ 2))
        (((((Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) -
          (Real.exp x * (x ^ 2 + 3)) * (2 * Real.cos ((2:ℝ) * x - (1:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)))) /
            (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
      exact h1.div h2 (by simpa using h_div_ne_zero_2)
    have h42 : HasDerivAt (λ y ↦ Real.log ((5:ℝ) * y + (2:ℝ)) ^ 3)
        ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * (5 / ((5:ℝ) * x + (2:ℝ)))) x := by
      have h421 : HasDerivAt (λ y ↦ Real.log ((5:ℝ) * y + (2:ℝ))) (5 / ((5:ℝ) * x + (2:ℝ))) x := h3
      have h422 : HasDerivAt (λ y ↦ Real.log y ^ 3) (3 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2) x :=
        hasDerivAt_pow 3 (Real.log ((5:ℝ) * x + (2:ℝ)))
      exact h421.pow 3
    exact h41.mul h42
  exact h4

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc, Real.log_mul, Real.log_rpow, Real.log_pow,
    Real.log_inv, Real.log_one, Real.log_exp, mul_inv_rev, mul_right_comm, mul_left_comm, mul_assoc,
    mul_comm, mul_left_comm, mul_assoc, Real.log_mul, Real.log_rpow, Real.log_pow, Real.log_inv, Real.log_one,
    Real.log_exp, mul_inv_rev, mul_right_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc,
    Real.log_mul, Real.log_rpow, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, mul_inv_rev,
    mul_right_comm, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  ring
  <;> field_simp <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [show (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))))
    = (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) by rfl]
  rw [deriv.comp]
  simp [mul_comm, mul_assoc, mul_left_comm]
  ring_nf
  field_simp
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> ring_nf

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp_all [Real.tan_eq_sin_div_cos, Real.exp_ne_zero, Real.log_ne_zero]
  field_simp [Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  ring_nf
  field_simp [Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  ring_nf
  <;> simp_all [Real.tan_eq_sin_div_cos, Real.exp_ne_zero, Real.log_ne_zero]
  <;> field_simp [Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp_all [Real.tan_eq_sin_div_cos, Real.exp_ne_zero, Real.log_ne_zero]
  <;> field_simp [Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp_all [Real.tan_eq_sin_div_cos, Real.exp_ne_zero, Real.log_ne_zero]
  <;> field_simp [Real.cos_ne_zero_iff, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp_all [Real.tan_eq_sin_div_cos, Real.exp_ne_zero, Real.log_ne_zero]

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_exp]
  simp only [deriv_exp, deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const', deriv_log,
    deriv_div, deriv_pow, deriv_id'', deriv_const', deriv_log]
  ring_nf
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h1 : deriv (fun x => Real.log (Real.exp x * (x ^ 2 + 3) + x ^ 3 * Real.log x / Real.log 5)) x =
    deriv (fun x => Real.log (Real.exp x * (x ^ 2 + 3) + x ^ 3 * Real.log x / Real.log 5)) x := rfl
  rw [h1]
  have h2 : deriv (fun x => Real.log (Real.exp x * (x ^ 2 + 3) + x ^ 3 * Real.log x / Real.log 5)) x =
    ((Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) + 3 * x ^ 2 * (Real.log x / Real.log 5) +
        x ^ 3 * ((1 / x) * Real.log 5 / Real.log 5 ^ 2)) /
      (Real.exp x * (x ^ 2 + 3) + x ^ 3 * (Real.log x / Real.log 5))) := by
    rw [deriv_log_comp] <;> simp [Real.exp_ne_zero, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
    field_simp <;> ring
  rw [h2]

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add] <;>
  simp_all [deriv_mul, deriv_const, deriv_exp, deriv_rpow_const, deriv_add, deriv_pow, deriv_id,
    deriv_log, exp_ne_zero] <;>
  ring_nf <;>
  field_simp <;>
  linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  rw [deriv_add]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp [Real.log_exp, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  <;> simp

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_const, deriv_id'', deriv_sin,
    deriv_sub, deriv_div, deriv_log, deriv_pow, deriv_add, deriv_mul, deriv_exp, deriv_pow,
    deriv_const, deriv_id'', deriv_sin, deriv_sub, deriv_div, deriv_log, deriv_pow]
  field_simp
  ring
  <;> simp only [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, mul_inv_rev, mul_div_assoc,
    mul_div_cancel_left]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id'', deriv_sin,
    deriv_cos, deriv_log]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22]
  ring
  <;> simp_all
  <;> field_simp
  <;> linarith
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => y) x = 1 := by
    intro x hx
    rw [deriv_id]
  have h2 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    intro x hx
    rw [deriv_pow]
    norm_num
  have h3 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => Real.sin y) x = Real.cos x := by
    intro x hx
    rw [deriv_sin]
  have h4 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => Real.cos y) x = -Real.sin x := by
    intro x hx
    rw [deriv_cos]
  have h5 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => Real.log y) x = 1 / x := by
    intro x hx
    rw [deriv_log]
  have h6 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => Real.exp y) x = Real.exp x := by
    intro x hx
    rw [deriv_exp]
  have h7 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => x ^ 2 + 3) x = 2 * x := by
    intro x hx
    rw [deriv_add]
    simp [deriv_const, deriv_pow]
  have h8 : ∀ x : ℝ, x ≠ 0 → deriv (fun y : ℝ => Real.exp y * (y ^ 2 + 3) + Real.cos (Real.log y)) x = Real.exp x * (x ^ 2 + 3) + Real.exp x * ((2:ℝ) * x) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
    intro x hx
    rw [deriv_add]
    rw [deriv_mul]
    simp [h6, h7, h5]
    ring
  simp [h8]

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  simp [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub, mul_add, mul_sub, add_mul,
    sub_mul, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_16, Real.cos_log, Real.sin_log, Real.exp_ne_zero, Real.log_ne_zero_of_pos_of_ne_one]
  ring
  <;> simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero, mul_zero, mul_one, add_zero, mul_neg, mul_assoc, mul_comm, mul_left_comm, sub_neg_eq_add, sub_zero]
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) ^ 2 := by
  have h₁ : ∀ x : ℝ, cos (Real.exp x * (x ^ 2 + 3) + Real.cos (Real.log x)) ≠ 0 := by
    intro x
    apply cos_ne_zero_of_mem_Ioo
    have : π / 2 < Real.exp x * (x ^ 2 + 3) + Real.cos (Real.log x) := by
      linarith [exp_pos x, cos_pos_of_mem_Ioo ⟨by linarith [log_neg_iff (by linarith : (0 : ℝ) < x)], by linarith [log_pos_iff (by linarith : (1 : ℝ) < x)]⟩]
    have : Real.exp x * (x ^ 2 + 3) + Real.cos (Real.log x) < π / 2 := by
      linarith [exp_pos x, cos_pos_of_mem_Ioo ⟨by linarith [log_neg_iff (by linarith : (0 : ℝ) < x)], by linarith [log_pos_iff (by linarith : (1 : ℝ) < x)]⟩]
    constructor <;> linarith
  have h₂ : ∀ x : ℝ, x ≠ 0 → x ^ 2 + 3 ≠ 0 := by
    intro x hx
    nlinarith
  simp_all only [deriv_tan, h₁, h₂]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.exp (Real.exp x * (x ^ 2 + 3) + Real.cos (Real.log x))) x =
    Real.exp (Real.exp x * (x ^ 2 + 3) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + 3)) +
    (Real.exp x * (2 * x)) +
    (-1 : ℝ) * Real.sin (Real.log x) * (1 / x)) := by
    intro x hx
    rw [deriv_exp]
    field_simp [hx]
    ring_nf
    rw [add_comm]
    apply congrArg
    ring_nf
  simpa using h₁ x h_log_ne_zero_16

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) / (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) := by
  have h : ∀ x, x ≠ 0 →  Real.log x ≠ 0 := by
    intro x hx
    rw [← Real.log_exp 0]
    intro h_log_ne_zero
    apply hx
    apply eq_of_log_eq_log
    simp_all
  rw [deriv.log]
  field_simp [h x h_log_ne_zero_16, h x h_log_ne_zero_16]
  ring_nf
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id'', deriv_cos, deriv_log, deriv_neg, neg_one_mul]
  field_simp [h_log_ne_zero_15]
  ring
  <;> norm_num
  <;> linarith
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.exp x) + (Real.cos (Real.log x) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  fun_prop
  simp [deriv_add_const, deriv_mul_const, deriv_const_mul, deriv_log, deriv_exp, deriv_pow, deriv_id, deriv_cos, deriv_sin, deriv_neg, deriv_inv, deriv_add_const, deriv_mul_const, deriv_const_mul, deriv_log, deriv_exp, deriv_pow, deriv_id, deriv_cos, deriv_sin, deriv_neg, deriv_inv]
  ring_nf
  field_simp
  linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  rw [deriv_add]
  <;> simp [deriv_mul, deriv_const, deriv_exp, deriv_id'', deriv_pow, deriv_cos, deriv_log, h_log_ne_zero_15]
  <;> field_simp [h_log_ne_zero_15]
  <;> ring
  <;> apply Differentiable.exp
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.pow
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.sin
  <;> apply Differentiable.inv
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.cos (Real.log x)) + (Real.cos (Real.log x) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_id'', deriv_const, mul_add,
    mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_log_ne_zero_15]
  ring
  <;> simp [Real.cos_sq, Real.sin_sq]
  <;> ring
  <;> simp [Real.cos_sq, Real.sin_sq]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  fun_conv =>
    simp [Real.exp_add, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
    fun_conv =>
      simp [Real.exp_add, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm,
        Real.log_mul, Real.log_inv, Real.log_pow, Real.log_exp, Real.exp_log, Real.exp_neg, Real.exp_sub,
        Real.exp_one, Real.exp_zero, Real.log_one, Real.log_zero, Real.sin_add, Real.cos_add,
        Real.sin_sub, Real.cos_sub, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi,
        Real.sin_neg, Real.cos_neg, Real.sin_int_mul_pi, Real.cos_int_mul_pi, Real.sinh, Real.cosh,
        Real.tanh, Real.arctanh, Real.arcsin, Real.arccos, Real.sqrt, pow_two, mul_comm, mul_left_comm,
        mul_assoc, add_assoc, add_comm, add_left_comm, sub_eq_add_neg, neg_add_rev]
    ring_nf
  <;> simp_all
  <;> ring_nf
  <;> simp_all
  <;> ring_nf
  <;> simp_all
  <;> ring_nf
  <;> simp_all
  <;> ring_nf
  <;> simp_all
  <;> ring_nf
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp_all [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id,
    deriv_sin, deriv_cos, deriv_log, deriv_sub, deriv_inv, deriv_comp,
    Real.exp_ne_zero]
  field_simp [mul_assoc, mul_comm, mul_left_comm]
  ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id, deriv_comp, deriv_inv,
    deriv_log, deriv_exp, deriv_cos, deriv_sin]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_rpow_const, deriv_log, h_log_ne_zero_16,
    h_div_ne_zero_23, h_log_ne_zero_26, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_comm, add_left_comm, sub_eq_add_neg, neg_add_rev]
  ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id'', deriv_add_const, deriv_sub, deriv_log, deriv_comp, deriv_inv, deriv_sin, deriv_cos]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19]
  ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [mul_add, mul_one, add_mul, add_assoc, mul_comm, mul_assoc, mul_left_comm,
    Real.exp_add, Real.exp_mul, Real.exp_sub, Real.exp_one, Real.exp_zero, Real.log_mul,
    Real.log_div, Real.log_rpow, Real.log_pow, Real.log_inv, Real.log_exp, Real.log_one,
    Real.log_zero, Real.cos_add, Real.cos_sub, Real.cos_mul, Real.cos_neg, Real.sin_add,
    Real.sin_sub, Real.sin_mul, Real.sin_neg, Real.tan_add, Real.tan_sub, Real.tan_mul,
    Real.tan_neg, Real.log_tan, Real.log_cos, Real.log_sin, Real.log_sqrt, Real.log_rpow,
    Real.log_rpow, Real.log_rpow, Real.log_rpow, Real.log_rpow, Real.log_rpow, Real.log_rpow]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h_log_ne_zero_16 : x ≠ 0 := by
    intro h_contra
    simp_all
  simp_all only [deriv_sin, deriv_exp, deriv_mul, deriv_add, deriv_one, deriv_id'',
    deriv_sub, deriv_cos, deriv_log, deriv_const, zero_mul, zero_add, mul_zero,
    sub_zero, one_mul, mul_one]
  field_simp [h_log_ne_zero_16]
  ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_sub, deriv_cos, deriv_exp, deriv_mul, deriv_id'', deriv_const', deriv_pow, deriv_add]
  simp only [mul_one, mul_zero, zero_add, mul_comm, mul_assoc, mul_left_comm]
  field_simp
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) ^ 2 := by
  simp_all only [Real.cos_zero, Real.cos_pi, mul_zero, mul_one, sub_self, zero_mul, zero_sub,
    neg_zero, zero_div, zero_mul, zero_add, mul_neg, mul_one, neg_neg, neg_mul, neg_sub,
    sub_neg_eq_add, mul_neg_one, neg_mul, neg_neg, neg_add_rev]
  apply Eq.symm
  rw [← mul_one (Real.exp x)]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring_nf
  norm_num
  rw [Real.tan_eq_sin_div_cos]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [deriv_exp]
  rw [deriv_sub]
  rw [deriv_mul]
  simp [h_log_ne_zero_16]
  ring_nf
  rw [deriv_cos]
  rw [deriv_log]
  simp [h_log_ne_zero_16]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x)) := by
  have h_exp_pos : 0 < Real.exp x := Real.exp_pos _
  have h_exp_ne_zero : Real.exp x ≠ 0 := ne_of_gt h_exp_pos
  have h_pow_two : x ^ 2 = x ^ (2:ℕ) := by norm_cast
  rw [h_pow_two]
  field_simp [h_exp_ne_zero, h_log_ne_zero_1, h_log_ne_zero_16]
  rw [← sub_eq_zero]
  ring_nf
  rw [Real.log_exp]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm,
    mul_right_comm]
  field_simp
  ring
  <;> simp only [Real.exp_zero, add_zero, mul_one, mul_zero, zero_add, mul_neg, mul_assoc]
  <;> ring
  <;> simp only [Real.exp_zero, add_zero, mul_one, mul_zero, zero_add, mul_neg, mul_assoc]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.exp x) + (Real.cos (Real.log x) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x))) := by
  simp_all [exp_ne_zero, deriv_mul, deriv_sub, deriv_add, deriv_neg, deriv_pow,
    deriv_comp, deriv_log, deriv_id, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_log_ne_zero_16]
  ring
  <;> aesop
  <;> aesop
  <;> aesop
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_cos,
    deriv_sin, mul_one, mul_zero, mul_neg, mul_comm, mul_left_comm, mul_assoc, one_mul, zero_mul,
    neg_mul, sub_neg_eq_add, add_assoc, add_left_comm, add_comm]
  field_simp
  ring
  <;> simp_all
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * Real.cos (Real.log x)) + (Real.cos (Real.log x) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp_all [deriv_mul, deriv_exp, deriv_cos, deriv_log, deriv_id, deriv_pow, mul_add, mul_sub,
    mul_one, mul_comm, mul_left_comm, mul_assoc]
  field_simp
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [mul_add, mul_one, mul_zero, sub_zero, zero_add, mul_assoc, mul_comm, mul_left_comm]
  field_simp [Real.exp_ne_zero, Real.sin_ne_zero_iff, Real.cos_ne_zero_iff]
  ring_nf
  <;> norm_num
  <;> apply Real.exp_ne_zero
  <;> apply Real.sin_ne_zero_iff.mpr
  <;> apply Real.cos_ne_zero_iff.mpr
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x => Real.exp x * (x ^ 2 + 3) - Real.cos (Real.log x) * (Real.sin (2 * x - 1)) ^ 2) x =
    Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) -
      ((-1 * Real.sin (Real.log x) * (1 / x)) * (Real.sin (2 * x - 1) ^ 2) +
        Real.cos (Real.log x) * (2 * Real.sin (2 * x - 1) * (Real.cos (2 * x - 1) * 2))) := by
    intro x hx
    rw [deriv_sub, deriv_mul, deriv_mul, deriv_exp, deriv_exp, deriv_pow'', deriv_add,
      deriv_id' (x := x), deriv_const, deriv_cos, deriv_log hx, deriv_sub, deriv_mul,
      deriv_const, deriv_id' (x := x), deriv_mul, deriv_const, deriv_id' (x := x),
      deriv_pow'', deriv_sin, deriv_sub, deriv_mul, deriv_const, deriv_id' (x := x),
      deriv_mul, deriv_const, deriv_id' (x := x), deriv_mul, deriv_const, deriv_id' (x := x)]
    · simp [add_comm, mul_comm, mul_assoc]
    · apply DifferentiableAt.mul_const
      apply DifferentiableAt.exp
      apply DifferentiableAt.log
      exact differentiableAt_id.2 hx
    · apply DifferentiableAt.mul_const
      apply DifferentiableAt.exp
      apply DifferentiableAt.log
      exact differentiableAt_id.2 hx
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        apply DifferentiableAt.cos
        apply DifferentiableAt.log
        exact differentiableAt_id.2 hx
        apply DifferentiableAt.pow
        apply DifferentiableAt.sin
        apply DifferentiableAt.sub
        · apply DifferentiableAt.mul
          apply DifferentiableAt.const_mul
          exact differentiableAt_id
          exact differentiableAt_id
        · apply DifferentiableAt.const_mul
          exact differentiableAt_id
          exact differentiableAt_id
      · apply DifferentiableAt.const_mul
        apply DifferentiableAt.sin
        apply DifferentiableAt.sub
        · apply DifferentiableAt.mul
          apply DifferentiableAt.const_mul
          exact differentiableAt_id
          exact differentiableAt_id
        · apply DifferentiableAt.const_mul
          exact differentiableAt_id
          exact differentiableAt_id
    · apply DifferentiableAt.add
      · apply DifferentiableAt.mul
        apply DifferentiableAt.exp
        apply DifferentiableAt.log
        exact differentiableAt_id.2 hx
        apply DifferentiableAt.pow
        exact differentiableAt_id
      · apply DifferentiableAt.const_mul
        exact differentiableAt_id
        exact differentiableAt_id
    · apply DifferentiableAt.cos
      apply DifferentiableAt.log
      exact differentiableAt_id.2 hx
    · apply DifferentiableAt.sin
      apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        apply DifferentiableAt.const_mul
        exact differentiableAt_id
        exact differentiableAt_id
      · apply DifferentiableAt.const_mul
        exact differentiableAt_id
        exact differentiableAt_id
  simpa using h₁ x h_log_ne_zero_15

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_const_mul]
  rw [deriv_log]
  ring_nf
  field_simp
  ring_nf
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp_all [deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_id, deriv_const, deriv_log,
    deriv_cos, deriv_sin, deriv_neg, deriv_id, deriv_const, deriv_log, deriv_mul,
    deriv_pow, deriv_add, deriv_id, deriv_const, deriv_log, deriv_cos, deriv_sin,
    deriv_neg, deriv_id, deriv_const, deriv_log, deriv_mul, deriv_pow, deriv_add,
    deriv_id, deriv_const, deriv_log, deriv_cos, deriv_sin, deriv_neg, deriv_id,
    deriv_const, deriv_log, deriv_mul, deriv_pow, deriv_add, deriv_id, deriv_const,
    deriv_log, deriv_cos, deriv_sin, deriv_neg]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  rw [deriv_sub, deriv_sub, deriv_exp, deriv_exp] <;>
    simp [Real.deriv_log, deriv_pow, deriv_add, deriv_mul, deriv_id, deriv_const]
  <;> field_simp <;> ring_nf <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  rw [deriv_sub]
  <;> simp_all [Real.exp_ne_zero]
  <;> field_simp
  <;> ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h₁ : deriv (fun x => sin (exp x * (x ^ 2 + 3) * cos (log x))) x = cos (exp x * (x ^ 2 + 3) * cos (log x)) * (((exp x * (x ^ 2 + 3)) + (exp x * (2 * x))) * cos (log x) + (exp x * (x ^ 2 + 3)) * ((-1) * sin (log x) * (1 / x))) := by
    simp only [mul_add, mul_comm, mul_left_comm, mul_assoc]
    rw [deriv_sin]
    field_simp [h_log_ne_zero_16]
    ring
  rw [h₁]

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 →  Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    exact ⟨by linarith [log_neg_iff hx, log_pos_iff hx], by linarith [log_neg_iff hx, log_pos_iff hx]⟩
  simp_all only [mul_assoc, mul_add, add_mul, mul_comm, mul_left_comm]
  field_simp
  ring
  <;> simp_all only [mul_assoc, mul_add, add_mul, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) ^ 2 := by
  rw [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring
  <;> simp_all
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → deriv (fun x => rexp (rexp x * (x ^ 2 + 3) * cos (log x))) x =
    rexp (rexp x * (x ^ 2 + 3) * cos (log x)) *
      (((rexp x * (x ^ 2 + 3)) + (rexp x * (2 * x))) * cos (log x) +
        (rexp x * (x ^ 2 + 3)) * (-1 * sin (log x) * (1 / x))) := by
    intro x hx
    rw [deriv_exp (by simpa only [mul_assoc] using DifferentiableAt.mul (DifferentiableAt.exp
      (DifferentiableAt.log (differentiableAt_id.pow 2 (by norm_num)) hx))
        (differentiableAt_id.pow 2 (by norm_num)))]
    field_simp [Real.exp_ne_zero, hx, Real.log_ne_zero_iff, hx, Real.exp_ne_zero]
    ring
  simpa only [mul_assoc] using h₀ x h_log_ne_zero_16

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * Real.cos ((Real.log (x)))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → ∀ x : ℝ, x ≠ 0 → (λ x => Real.log (Real.exp x * (x ^ 2 + 3) * Real.cos (Real.log x))) x = (λ x => Real.log (Real.exp x * (x ^ 2 + 3) * Real.cos (Real.log x))) x := by intros; rfl
  rw [deriv_log_of_pos h_log_ne_zero_1]
  field_simp [h_log_ne_zero_16]
  ring
  <;> simp [Real.exp_ne_zero]
  <;> simp [h_log_ne_zero_16]
  <;> simp [h_log_ne_zero_1]
  <;> simp [Real.exp_ne_zero]
  <;> simp [h_log_ne_zero_16]
  <;> simp [h_log_ne_zero_1]
  <;> simp [Real.exp_ne_zero]
  <;> simp [h_log_ne_zero_16]
  <;> simp [h_log_ne_zero_1]
  <;> simp [Real.exp_ne_zero]
  <;> simp [h_log_ne_zero_16]
  <;> simp [h_log_ne_zero_1]
  <;> simp [Real.exp_ne_zero]

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_cos]
  rw [deriv_log]
  ring_nf
  field_simp
  linarith
  <;> linarith
  <;> assumption
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.id

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  simp_all only [ne_eq, one_div, mul_assoc, mul_comm, mul_left_comm]
  field_simp
  ring
  <;> simp_all only [ne_eq, one_div, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => x ^ 2 + 3) (2 * x) x := fun x hx => by
    apply HasDerivAt.pow
    apply HasDerivAt.const_add
    simp
  have h2 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) (-(Real.sin (Real.log x) * (1 / x))) x := fun x hx => by
    apply HasDerivAt.comp
    apply HasDerivAt.cos
    apply HasDerivAt_log
    apply hx
  simp_all [HasDerivAt.mul, HasDerivAt.add, HasDerivAt.const_mul, HasDerivAt.neg, HasDerivAt.inv]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [← sub_eq_zero]
  field_simp [h_log_ne_zero_15, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
  ring
  <;> simp_all [Real.exp_ne_zero]
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.exp
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.sin
  <;> apply Differentiable.comp
  <;> apply Differentiable.arctan
  <;> apply Differentiable.pow
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.exp
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.const
  <;> apply Differentiable.id
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.sin
  <;> apply Differentiable.comp
  <;> apply Differentiable.arctan
  <;> apply Differentiable.pow

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [add_mul, mul_add, mul_assoc]
  field_simp [Real.exp_ne_zero]
  ring
  <;> simp_all only [deriv_exp, deriv_log, deriv_cos, deriv_sin, deriv_id'', deriv_const',
    deriv_pow'', deriv_add, deriv_sub, deriv_mul, deriv_inv, deriv_pow, deriv_pow']
  <;> field_simp [Real.exp_ne_zero]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  fun_prop_diff
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.cos_ne_zero]
  <;> simp_all [Real.sin_ne_zero]
  <;> simp_all [Real.log_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.cos_ne_zero]
  <;> simp_all [Real.sin_ne_zero]
  <;> simp_all [Real.log_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.cos_ne_zero]
  <;> simp_all [Real.sin_ne_zero]
  <;> simp_all [Real.log_ne_zero]
  <;> simp_all [Real.exp_ne_zero]
  <;> simp_all [Real.cos_ne_zero]
  <;> simp_all [Real.sin_ne_zero]
  <;> simp_all [Real.log_ne_zero]

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_log, deriv_cos, deriv_sin,
    deriv_id'', deriv_pow'', deriv_inv, deriv_div, deriv_comp, deriv_const', deriv_id',
    deriv_comp', deriv_mul', deriv_log']
  field_simp [h_log_ne_zero_15, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> simp only [Real.exp_log, Real.log_exp, Real.log_mul, Real.log_pow, Real.log_inv,
    Real.log_div, Real.log_one, Real.log_zero, mul_one, mul_zero, zero_add,
    zero_sub, sub_zero, add_zero]
  <;> ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [Real.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel_right₀, h_log_ne_zero_16,
    h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  aesop

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp [mul_add, mul_comm, mul_left_comm, deriv_add, deriv_mul, deriv_comp, deriv_exp,
    deriv_log, deriv_id'', deriv_const, Real.deriv_cos, Real.deriv_sin, Real.deriv_log]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19, mul_comm]
  ring

example (x: ℝ)  (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.cos (Real.log x)) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp [h_log_ne_zero_15, h_log_ne_zero_19, mul_add, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_15, h_log_ne_zero_19, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  <;> simp_all
  <;> linarith
  <;> linarith
  <;> linarith
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  have h₁ : deriv (fun x => Real.sin (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * (((Real.exp x * (x ^ 2 + 3)) + (Real.exp x * (2 * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + 3)) * ((-1) * Real.sin (Real.log x) * (1 / x))) / Real.cos (Real.log x) ^ 2 := by
    rw [deriv_sin]
    field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
    ring_nf
    field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
    ring_nf
  rw [h₁]
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  have h₀ : ∀ x, x ≠ 0 → Real.cos (Real.log x) ≠ 0 →
    (Real.cos (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) *
        ((Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * Real.sin (Real.log x)) /
        Real.cos (Real.log x) ^ 2) =
      Real.cos (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) *
        ((Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * Real.sin (Real.log x)) /
        Real.cos (Real.log x) ^ 2 := by intro x h₀ h₁; rfl
  have h₁ : ∀ x, x ≠ 0 → Real.cos (Real.log x) ≠ 0 →
    (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * Real.sin (Real.log x) =
      Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x) * Real.sin (Real.log x) := by
    intro x h₀ h₁
    ring
  have h₂ : ∀ x, x ≠ 0 → Real.cos (Real.log x) ≠ 0 →
    Real.cos (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) *
        ((Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * Real.sin (Real.log x)) /
        Real.cos (Real.log x) ^ 2 =
      Real.cos (Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) *
        ((Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x)) * Real.sin (Real.log x)) /
        Real.cos (Real.log x) ^ 2 := by intro x h₀ h₁; rfl
  simp [h₀, h₁, h₂, deriv_mul, deriv_const_mul, deriv_exp, deriv_log, deriv_pow, deriv_id,
    deriv_inv, deriv_sin, deriv_cos]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / Real.cos ((Real.log (x)))) ≠ 0) (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) ^ 2 := by
  simp only [Real.cos_zero, Real.exp_zero, zero_add, mul_one, mul_zero, add_zero]
  have h1 : ∀ x : ℝ, x ≠ 0 → Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    apply Real.cos_ne_zero_of_mem_Ioo
    exact ⟨by linarith [Real.log_neg_iff (by norm_num : (0 : ℝ) < 1) hx], by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2) hx]⟩
  have h2 : ∀ x : ℝ, Real.cos (Real.log x) ≠ 0 → Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) ≠ 0 := by
    intro x hx
    apply Real.cos_ne_zero_of_mem_Ioo
    exact ⟨by linarith [Real.exp_pos x], by linarith [Real.exp_pos x]⟩
  field_simp [h1, h2, h_log_ne_zero_16, h_div_ne_zero_3, h_tan_ne_zero_1]
  ring_nf
  rw [Real.tan_eq_sin_div_cos]
  field_simp [h1, h2, h_log_ne_zero_16, h_div_ne_zero_3, h_tan_ne_zero_1]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) := by
  have h1 : ∀ x : ℝ, cos (log x) ≠ 0 → x ≠ 0 → DifferentiableAt ℝ (fun x => exp (exp x * (x ^ 2 + 3) / cos (log x))) x := by
    intro x h1 h2
    apply DifferentiableAt.exp
    apply DifferentiableAt.div_const
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.exp
    apply DifferentiableAt.add
    · apply DifferentiableAt.pow
      apply DifferentiableAt.id
    · apply DifferentiableAt.const
  have h2 : ∀ x : ℝ, cos (log x) ≠ 0 → x ≠ 0 → deriv (fun x => exp (exp x * (x ^ 2 + 3) / cos (log x))) x = exp (exp x * (x ^ 2 + 3) / cos (log x)) * (((exp x * (x ^ 2 + 3) + exp x * (2 * x)) * cos (log x) - exp x * (x ^ 2 + 3) * (-1 * sin (log x) * (1 / x))) / cos (log x) ^ 2) := by
    intro x h1 h2
    rw [deriv_exp]
    rw [deriv_div]
    rw [deriv_mul]
    rw [deriv_exp]
    rw [deriv_add]
    · rw [deriv_pow]
      rw [deriv_id]
      rw [deriv_const]
    · rw [deriv_const]
    simp_all
  simp_all

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / Real.cos ((Real.log (x)))) ≠ 0) (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x))) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) / (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) := by
  have h₁ : ∀ x, x ≠ 0 → Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    apply cos_ne_zero_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have h₂ : ∀ x, x ≠ 0 → Real.exp x * (x ^ 2 + 3) / Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    apply div_ne_zero
    · apply mul_ne_zero
      · apply exp_ne_zero
      · nlinarith
    · apply h₁
      assumption
  field_simp [h₁, h₂, Real.log_ne_zero_iff, Real.exp_ne_zero, Real.cos_ne_zero_iff] at *
  line_integrate

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp_all [deriv_exp, deriv_mul, deriv_add, deriv_pow, deriv_const, deriv_id,
    deriv_log, deriv_inv, Real.cos_log, Real.sin_log]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_add, mul_sub, mul_one, mul_div_assoc, mul_pow, mul_comm, mul_left_comm,
    mul_right_comm]
  rw [← sub_eq_zero]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16, Real.exp_ne_zero]
  ring
  <;> simp [h_div_ne_zero_3, h_log_ne_zero_16, Real.exp_ne_zero]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16, Real.exp_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_log, deriv_cos,
    deriv_sin, deriv_id, deriv_comp, deriv_inv, mul_one, mul_zero, add_zero, zero_add,
    mul_neg, mul_assoc, neg_mul, neg_neg]
  field_simp [h_log_ne_zero_15, h_div_ne_zero_2]
  ring

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h_cos_ne_zero: cos (log x) ≠ 0 := by
    intro h_cos_zero
    apply h_div_ne_zero_2
    rw [h_cos_zero]
    simp
  have h_sin_ne_zero: sin (log x) ≠ 0 := by
    intro h_sin_zero
    rw [h_sin_zero] at h_cos_ne_zero
    simp at h_cos_ne_zero
  have h_deriv_mul : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ))) x =
    ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) := by
    rw [deriv_mul]
    · simp [deriv_exp, deriv_pow, deriv_add, deriv_id, deriv_const]
    · apply DifferentiableAt.exp
      apply DifferentiableAt.id
    · apply DifferentiableAt.add
      · apply DifferentiableAt.pow
        apply DifferentiableAt.id
      · apply DifferentiableAt.const
  have h_deriv_div : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) x =
    (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) -
    (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 := by
    rw [deriv_div]
    · simp [h_deriv_mul]
    · apply DifferentiableAt.exp
      apply DifferentiableAt.id
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.pow
        apply DifferentiableAt.id
      · apply DifferentiableAt.const
    · apply h_cos_ne_zero
  rw [h_deriv_div]
  field_simp [h_cos_ne_zero]
  ring

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc]
  field_simp [Real.cos_ne_zero, h_div_ne_zero_2, h_log_ne_zero_15]
  ring
  <;> simp only [Real.exp_log, mul_inv_cancel, h_log_ne_zero_15, Real.cos_log, mul_one,
    mul_div_cancel_left, Real.sin_log, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [Real.cos_ne_zero, h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring
  <;> simp only [Real.exp_log, mul_inv_cancel, h_log_ne_zero_15, Real.cos_log, mul_one,
    mul_div_cancel_left, Real.sin_log, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [Real.cos_ne_zero, h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring
  <;> simp only [Real.exp_log, mul_inv_cancel, h_log_ne_zero_15, Real.cos_log, mul_one,
    mul_div_cancel_left, Real.sin_log, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [Real.cos_ne_zero, h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring
  <;> simp only [Real.exp_log, mul_inv_cancel, h_log_ne_zero_15, Real.cos_log, mul_one,
    mul_div_cancel_left, Real.sin_log, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [Real.cos_ne_zero, h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [mul_assoc, mul_pow, mul_sub, mul_one, mul_add]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.cos_log_pos, Real.cos_log_pos,
    Real.sin_log_pos, Real.sin_log_pos]
  ring
  <;> simp [Real.exp_ne_zero]
  <;> apply Real.cos_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> apply Real.sin_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> simp [Real.exp_ne_zero]
  <;> apply Real.cos_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> apply Real.sin_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> simp [Real.exp_ne_zero]
  <;> apply Real.cos_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> apply Real.sin_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> simp [Real.exp_ne_zero]
  <;> apply Real.cos_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]
  <;> apply Real.sin_ne_zero_of_mem_Ioo <;> simp [Real.log_mem_Ioo]

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all only [one_div, mul_zero, mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  field_simp
  ring_nf
  <;> norm_num
  <;> apply Real.exp_ne_zero
  <;> apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num

example (x: ℝ)  (h_div_ne_zero_3: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_16: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [deriv_mul, deriv_div, deriv_exp, deriv_rpow_const, deriv_log,
    deriv_const_mul, deriv_const, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2 + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, h_log_ne_zero_19, Real.exp_ne_zero]
  ring
  <;> simp_all [Real.cos_log, Real.sin_log, mul_assoc, mul_comm, mul_left_comm,
    mul_add, mul_sub, sub_mul, add_mul]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, h_log_ne_zero_19, Real.exp_ne_zero]
  <;> ring
  <;> simp_all [Real.cos_log, Real.sin_log, mul_assoc, mul_comm, mul_left_comm,
    mul_add, mul_sub, sub_mul, add_mul]

example (x: ℝ)  (h_div_ne_zero_2: Real.cos ((Real.log (x))) ≠ 0) (h_log_ne_zero_15: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * Real.cos (Real.log x) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) / Real.cos (Real.log x) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.cos (Real.log x)) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → cos (log x) ≠ 0 := by
    intro x hx
    exact cos_ne_zero_of_ne_zero_of_ne_pi_div_two (log_ne_zero_of_ne_one hx zero_lt_one)
      (log_ne_pi_div_two_of_pos (hx.lt_of_le zero_le_one))
  have h2 : ∀ x : ℝ, x ≠ 0 → (5 * x + 2) ≠ 0 := by
    intro x hx
    nlinarith
  field_simp [*, log_ne_zero_of_ne_one] at *
  ring_nf
  field_simp [log_ne_zero_of_ne_one]
  linarith

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  rw [deriv_sin]
  simp [mul_add, mul_comm, mul_left_comm]
  ring
  <;> apply isOpen_Ioi

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  simp only [Real.cos_add, Real.cos_sub, Real.sin_sub, Real.sin_add, mul_add, mul_sub, add_mul, sub_mul,
    mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  rw [Real.deriv_cos, neg_one_mul]
  simp only [neg_mul, neg_neg, mul_neg, neg_add, neg_sub]
  ring
  <;> simp only [Real.deriv_sin, mul_one]
  <;> simp only [neg_mul, neg_neg, mul_neg, neg_add, neg_sub]
  <;> ring
  <;> simp only [Real.deriv_exp, mul_one]
  <;> simp only [neg_mul, neg_neg, mul_neg, neg_add, neg_sub]
  <;> ring
  <;> simp only [Real.deriv_pow, mul_one]
  <;> simp only [neg_mul, neg_neg, mul_neg, neg_add, neg_sub]
  <;> ring
  <;> simp only [Real.deriv_id'', mul_one]
  <;> simp only [neg_mul, neg_neg, mul_neg, neg_add, neg_sub]
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  rw [deriv_tan]
  field_simp [h_tan_ne_zero_1]
  ring
  <;>
    simp only [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
  <;>
    ring

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  rw [deriv_exp (f := λ x ↦ (Real.exp x * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))]
  simp only [mul_add, mul_sub, mul_one, mul_zero, add_zero, sub_zero, mul_assoc, mul_comm]
  ring_nf
  <;> apply congr_arg
  <;> apply congr_arg
  <;> ring_nf
  <;> apply congr_arg
  <;> ring_nf
  <;> apply congr_arg
  <;> ring_nf
  <;> apply congr_arg
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  rw [deriv_log (by assumption)]
  field_simp [h_log_ne_zero_1]
  ring
  <;> simp_all only [mul_add, add_assoc, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all only [mul_add, add_assoc, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> field_simp
  <;> linarith

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  · rw [deriv_mul]
    rw [deriv_exp]
    rw [deriv_mul]
    simp only [deriv_pow, deriv_id'', pow_one, mul_one, mul_add, add_assoc, mul_comm, mul_assoc,
      mul_left_comm]
    ring
  · rw [deriv_sin, deriv_mul]
    simp only [deriv_const', deriv_id'', mul_one, mul_zero, add_zero, mul_comm, mul_assoc,
      mul_left_comm]
    ring
  · rw [deriv_exp]
    rw [deriv_mul]
    simp only [deriv_pow, deriv_id'', pow_one, mul_one, mul_add, add_assoc, mul_comm, mul_assoc,
      mul_left_comm]
    ring
  all_goals apply Differentiable.differentiableAt; apply differentiable_exp; apply differentiable_id
  all_goals apply Differentiable.differentiableAt; apply differentiable_sin; apply differentiable_id
  all_goals apply Differentiable.differentiableAt; apply differentiable_exp; apply differentiable_id

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_add, mul_comm, mul_left_comm, mul_assoc, mul_one, add_assoc, add_left_comm]
  ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf
  <;> simp only [Real.exp_zero, mul_one, sub_self, Real.exp_zero, mul_zero, sub_zero]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_sin, deriv_sub,
    deriv_id'', deriv_cos, deriv_log, deriv_comp]
  field_simp [h_log_ne_zero_25]
  ring

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x =
    (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) +
      (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) +
      ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
    intro x hx
    rw [deriv_add]
    · field_simp [hx]
      ring
    · apply DifferentiableAt.add
      · apply DifferentiableAt.mul
        · exact differentiableAt_exp
        · apply DifferentiableAt.pow
          exact differentiableAt_id
      · apply DifferentiableAt.mul
        · apply DifferentiableAt.comp
          · exact differentiableAt_sin
          · apply DifferentiableAt.sub
            · apply DifferentiableAt.const_mul
              exact differentiableAt_id
            · exact differentiableAt_const
        · exact differentiableAt_cos.comp (differentiableAt_log differentiableAt_id)
  simp_all

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  rw [deriv_add]
  simp only [deriv_exp, deriv_add, deriv_mul, deriv_id'', deriv_const', deriv_pow, deriv_sin, deriv_cos, deriv_sub]
  ring
  <;> apply DifferentiableAt.add <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.sin <;> apply DifferentiableAt.cos <;> apply DifferentiableAt.exp <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.const <;> apply DifferentiableAt.id

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₁ : ∀ x : ℝ, HasDerivAt (fun x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ))) (Real.exp x * (x ^ 2 + (3:ℝ))) x := by
    intro x
    have h₁ : HasDerivAt (fun x ↦ Real.exp x * x ^ 2) (Real.exp x * (x ^ 2 + (3:ℝ))) x := by
      have h₁ : HasDerivAt (fun x ↦ Real.exp x * x ^ 2) (Real.exp x * (x ^ 2 + (3:ℝ))) x := by
        have h₁ : HasDerivAt (fun x ↦ Real.exp x * x ^ 2) (Real.exp x * (x ^ 2 + (3:ℝ))) x := by
          apply HasDerivAt.mul
          exact hasDerivAt_exp x
          exact hasDerivAt_pow 2 x
        apply HasDerivAt.mul
        exact hasDerivAt_exp x
        exact hasDerivAt_pow 2 x
      apply HasDerivAt.mul
      exact hasDerivAt_exp x
      exact hasDerivAt_pow 2 x
    apply HasDerivAt.add
    exact h₁
    have h₂ : HasDerivAt (fun x ↦ (3:ℝ)) 0 x := by
      apply hasDerivAt_const
    exact h₂
  have h₂ : ∀ x : ℝ, HasDerivAt (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) x := by
    intro x
    have h₁ : HasDerivAt (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
      have h₁ : HasDerivAt (fun x ↦ Real.sin ((2:ℝ) * x - (1:ℝ))) ((2:ℝ) * Real.cos ((2:ℝ) * x - (1:ℝ))) x := by
        apply HasDerivAt.comp
        exact hasDerivAt_sin ((2:ℝ) * x - (1:ℝ))
        exact hasDerivAt_sub
        exact hasDerivAt_mul_const 2
        exact hasDerivAt_const x 1
      apply HasDerivAt.pow
      exact h₁
    have h₂ : HasDerivAt (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
      apply HasDerivAt.pow
      exact h₁
    apply HasDerivAt.mul
    exact h₂
    exact h₂
  apply HasDerivAt.add
  exact h₁
  apply HasDerivAt.add
  exact h₂
  apply HasDerivAt.add
  exact h₂
  exact h₂

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  simp only [deriv_exp, deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const, deriv_sin, deriv_cos,
    deriv_sub, deriv_neg, deriv_id, deriv_pow, deriv_id, deriv_const]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_exp, deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const',
    deriv_sin, deriv_cos, deriv_sub, deriv_neg, deriv_log, mul_one, mul_zero, add_zero,
    zero_add, mul_comm, mul_left_comm, mul_assoc, mul_div_assoc, mul_div_cancel_left]
  field_simp [h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm, mul_one, mul_zero, add_zero,
    zero_add, mul_comm, mul_left_comm, mul_assoc, mul_div_assoc, mul_div_cancel_left]
  <;> ring
  <;> field_simp [h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  fun_prop
  ring_nf
  field_simp [h_log_ne_zero_25]
  <;> aesop
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all [deriv_add, deriv_mul, deriv_exp, deriv_rpow_const, deriv_log, deriv_sin, deriv_cos,
    deriv_pow, deriv_add, deriv_const, deriv_mul, deriv_comp, deriv_pow, deriv_add,
    deriv_mul, deriv_comp, deriv_pow, deriv_add, deriv_mul, deriv_comp, deriv_pow, deriv_add,
    deriv_mul, deriv_comp]
  ring_nf
  field_simp [h_log_ne_zero_25]
  ring_nf

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [Real.exp_ne_zero]
  ring_nf
  rw [deriv_sin]
  field_simp [Real.exp_ne_zero]
  ring_nf
  <;> simp [Real.exp_ne_zero]
  <;> field_simp [Real.exp_ne_zero]
  <;> ring_nf
  <;> simp [Real.exp_ne_zero]
  <;> field_simp [Real.exp_ne_zero]
  <;> ring_nf
  <;> simp [Real.exp_ne_zero]
  <;> field_simp [Real.exp_ne_zero]
  <;> ring_nf

example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [show (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
    = (λ x ↦ Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))
      by ext; ring)
  simp only [Real.cos_exp_mul_add_int_mul_two_pi,
    Real.sin_exp_mul_add_int_mul_two_pi, mul_zero, sub_zero, mul_one]
  ring_nf
  field_simp
  rw [show (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
    = (λ x ↦ Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))
      by ext; ring]
  simp only [Real.cos_exp_mul_add_int_mul_two_pi,
    Real.sin_exp_mul_add_int_mul_two_pi, mul_zero, sub_zero, mul_one]
  ring_nf
  field_simp

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  rw [← sub_eq_zero]
  simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_tan_ne_zero_1]
  ring_nf
  field_simp [Real.cos_eq_zero_iff, Real.sin_eq_zero_iff]
  <;> simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1]
  <;> ring_nf
  <;> field_simp [Real.cos_eq_zero_iff, Real.sin_eq_zero_iff]
  <;> simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1]
  <;> ring_nf
  <;> field_simp [Real.cos_eq_zero_iff, Real.sin_eq_zero_iff]
  <;> simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1]
  <;> ring_nf
  <;> field_simp [Real.cos_eq_zero_iff, Real.sin_eq_zero_iff]
  <;> simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1]

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  apply HasDerivAt.deriv
  have h1 : HasDerivAt (fun x => Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
    (Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) x := by
    apply HasDerivAt.exp
    apply HasDerivAt.sub
    apply HasDerivAt.mul
    apply HasDerivAt.exp
    apply HasDerivAt.add
    apply HasDerivAt.pow
    apply hasDerivAt_id
    apply hasDerivAt_const
    apply HasDerivAt.neg
    apply HasDerivAt.pow
    apply HasDerivAt.sin
    apply HasDerivAt.sub
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    apply hasDerivAt_const
  exact h1

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  simp_all [deriv_log, h_log_ne_zero_1]
  field_simp [h_log_ne_zero_1]
  ring_nf
  <;> simp_all [h_log_ne_zero_1]
  <;> field_simp [h_log_ne_zero_1]
  <;> linarith

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const]
  rw [deriv_id]
  rw [deriv_const]
  rw [deriv_id]
  ring
  all_goals apply Differentiable.differentiableAt; apply Differentiable.exp; apply differentiable_id
  <;> apply Differentiable.const_mul <;> apply differentiable_id
  <;> apply Differentiable.const_add <;> apply differentiable_id
  <;> apply Differentiable.sin <;> apply Differentiable.const_sub <;> apply differentiable_id
  <;> apply Differentiable.cos <;> apply Differentiable.const_sub <;> apply differentiable_id
  <;> apply Differentiable.pow <;> apply differentiable_id

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x))) := by
  simp only [deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const,
    deriv_sin, deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const,
    deriv_sin]
  ring_nf
  <;> simp only [mul_assoc]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  fun_props
  simp_all only [mul_add, mul_one, mul_sub, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp
  linarith [Real.exp_ne_zero x]

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x => rexp x * (x ^ 2 + 3) - (sin (2 * x - 1)) ^ 2 * cos (log x)) x =
    rexp x * (x ^ 2 + 3) + rexp x * (2 * x) - (2 * sin (2 * x - 1) * (cos (2 * x - 1) * 2) * cos (log x) +
      sin (2 * x - 1) ^ 2 * (-1 * sin (log x) * (1 / x))) := by
    intro x hx
    rw [deriv_sub]
    · rw [deriv_mul]
      rw [deriv_exp]
      rw [deriv_mul]
      rw [deriv_pow]
      simp
      ring
      simp [hx]
      ring
    · apply DifferentiableAt.pow
      apply differentiableAt_id
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.sin
        apply differentiableAt_id
      · apply DifferentiableAt.cos
        apply differentiableAt_log differentiableAt_id
  simpa using h₁ x h_log_ne_zero_25

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, add_assoc, add_comm, add_left_comm]
  ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.exp_ne_zero]
  <;> norm_num

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  rw [show (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
       = (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
        by rfl]
  rw [show (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
       = (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2))
        by rfl]
  aesop
  <;> simp_all only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm]
  <;> apply HasDerivAt.add
  <;> apply HasDerivAt.mul
  <;> apply HasDerivAt.comp
  <;> apply HasDerivAt.sin
  <;> apply HasDerivAt.cos
  <;> apply HasDerivAt.exp
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.const_add
  <;> apply HasDerivAt.const_sub
  <;> apply HasDerivAt.id

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_sub, deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_sin, deriv_const, deriv_id, deriv_tan_comp,
    deriv_log_of_pos (show (0:ℝ) < 5 by norm_num), deriv_log_of_pos (show (0:ℝ) < 5 by norm_num)]
  ring
  <;> simp_all only [ne_eq, one_div, mul_one, mul_div_cancel_left]
  <;> field_simp [Real.log_ne_zero]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_sin, deriv_cos, deriv_id'',
    deriv_const', mul_zero, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm]
  ring
  <;> aesop
  <;> aesop
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_sin,
    deriv_cos, deriv_id'', deriv_const, Real.cos_two_mul, Real.sin_two_mul, mul_add, mul_sub,
    add_assoc, add_sub_assoc, sub_sub_eq_add_sub]
  field_simp [h_log_ne_zero_25]
  ring
  <;> simp only [mul_comm, mul_left_comm, mul_assoc, mul_right_comm]

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp_all [mul_add, add_mul, add_comm, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  rw [Real.exp_ne_zero, sq, mul_inv_cancel h_log_ne_zero_25, mul_one, mul_inv_cancel h_log_ne_zero_25, mul_one]
  field_simp
  linarith

example (x: ℝ) : deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [Real.deriv_sin]
  ring_nf
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  simp only [Real.deriv_sin]
  <;>
  simp only [Real.deriv_exp]
  <;>
  simp only [Real.deriv_pow]
  <;>
  simp only [Real.deriv_mul]
  <;>
  simp only [Real.deriv_id]
  <;>
  simp only [Real.deriv_const]
  <;>
  simp only [Real.deriv_sub]
  <;>
  simp only [Real.deriv_cos]
  <;>
  sim
example (x: ℝ) : deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp_all only [mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  apply deriv_congr_of_mem_nhds
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) zero_lt_one]
  intro x hx
  simp_all only [mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  rw [Real.cos_exp_mul_add_mul_sin_sq]
  ring
  <;> simp [Real.cos_exp_mul_add_mul_sin_sq]
  <;> norm_num
  <;> simp_all only [mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> rw [Real.cos_exp_mul_add_mul_sin_sq]
  <;> ring
  <;> simp [Real.cos_exp_mul_add_mul_sin_sq]
  <;> norm_num
  <;> simp_all only [mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> rw [Real.cos_exp_mul_add_mul_sin_sq]
  <;> ring
  <;> simp [Real.cos_exp_mul_add_mul_sin_sq]
  <;> norm_num

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  have h₀ : ∀ x : ℝ, (cos x) ≠ 0 → (tan x) = (sin x) / (cos x) := by
    intro x hx
    rw [tan_eq_sin_div_cos]
  field_simp [h₀, Real.cos_ne_zero_iff] at *
  ring_nf
  field_simp
  repeat' rw [mul_assoc]
  ring_nf

example (x: ℝ) : deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [deriv_exp, mul_add, mul_one, mul_assoc, mul_left_comm, deriv_mul, deriv_pow, deriv_id'',
    deriv_const', deriv_sin, deriv_sub, deriv_two, deriv_id, deriv_cos, deriv_neg, deriv_add,
    deriv_id'', deriv_const']
  ring_nf
  <;> simp only [Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_sin,
    Complex.ofReal_cos, Complex.ofReal_exp]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  have h₁ :
    deriv (fun x => Real.log (Real.exp x * (x ^ 2 + 3) * (Real.sin (2 * x - 1)) ^ 2)) x =
      ((Real.exp x * (x ^ 2 + 3)) + (Real.exp x * (2 * x))) * (Real.sin (2 * x - 1) ^ 2) +
        (Real.exp x * (x ^ 2 + 3)) * (2 * Real.sin (2 * x - 1) * (Real.cos (2 * x - 1) * 2)) /
        (Real.exp x * (x ^ 2 + 3) * (Real.sin (2 * x - 1)) ^ 2) := by
    field_simp [Real.log_ne_zero_iff, h_log_ne_zero_1]
    ring_nf
    apply Eq.symm
    rw [← sub_eq_zero]
    field_simp [Real.log_ne_zero_iff, h_log_ne_zero_1]
    ring_nf
  rw [h₁]
  field_simp [Real.log_ne_zero_iff, h_log_ne_zero_1]
  <;> ring_nf
  <;> apply Eq.symm
  <;> rw [← sub_eq_zero]
  <;> field_simp [Real.log_ne_zero_iff, h_log_ne_zero_1]
  <;> ring_nf

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_id, deriv_const, deriv_sin, deriv_cos, deriv_sub,
    deriv_add, deriv_neg, deriv_comp, deriv_id, deriv_const]
  <;> ring
  <;> norm_num
  <;> apply Differentiable.exp <;> apply Differentiable.pow <;> apply Differentiable.add
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.sub
  <;> apply Differentiable.add
  <;> apply Differentiable.neg
  <;> apply Differentiable.id
  <;> apply Differentiable.const

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [deriv_mul, deriv_exp, deriv_pow, deriv_const, deriv_add, deriv_mul, deriv_comp, deriv_sin, deriv_id'', deriv_sub, deriv_two, deriv_neg, deriv_one,
    deriv_id, deriv_inv, deriv_comp, deriv_const_mul, deriv_add_const]
  ring

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [mul_add, add_mul, mul_one, mul_zero, zero_add, add_assoc, add_right_neg, add_zero]
  apply HasDerivAt.deriv
  have h₀ : HasDerivAt (fun x => rexp x * (x ^ 2 + (3 : ℝ))) (rexp x * (x ^ 2 + (3 : ℝ)) + rexp x * (2 * x)) x := by
    apply HasDerivAt.mul
    · exact hasDerivAt_exp x
    · exact hasDerivAt_pow 2 x
  have h₁ : HasDerivAt (fun x => x ^ 2 + (3 : ℝ)) (2 * x) x := by
    apply HasDerivAt.pow
    simp
  have h₂ : HasDerivAt (fun x => Real.sin ((2 : ℝ) * x - (1 : ℝ)) ^ 2) (2 * Real.sin ((2 : ℝ) * x - (1 : ℝ)) * Real.cos ((2 : ℝ) * x - (1 : ℝ)) * (2 : ℝ)) x := by
    apply HasDerivAt.pow
    apply HasDerivAt.sin
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      simp
    · apply hasDerivAt_const
  have h₃ : HasDerivAt (fun x => Real.cos (Real.log x)) (-(Real.sin (Real.log x) * (1 / x))) x := by
    apply HasDerivAt.comp
    · exact hasDerivAt_cos (Real.log x)
    · exact hasDerivAt_log h_log_ne_zero_25
  simp only [mul_neg, neg_mul, mul_one, mul_neg_one, neg_neg, neg_add_rev]
  nlinarith [HasDerivAt.deriv h₀, HasDerivAt.deriv h₁, HasDerivAt.deriv h₂, HasDerivAt.deriv h₃]

example (x: ℝ)  (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp [mul_assoc]
  field_simp [h_log_ne_zero_25]
  ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]
  <;> field_simp [h_log_ne_zero_25]
  <;> ring_nf
  <;> simp_all [mul_assoc]

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  simp [deriv_mul, deriv_exp, deriv_pow, deriv_id, deriv_const, deriv_sin, deriv_cos, deriv_sub]
  ring
  <;> apply Differentiable.differentiableAt <;>
  apply Differentiable.mul <;>
  apply Differentiable.add <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const <;>
  apply Differentiable.exp <;>
  apply Differentiable.pow <;>
  apply Differentiable.const <;>
  apply Differentiable.sin <;>
  apply Differentiable.cos <;>
  apply Differentiable.sub <;>
  apply Differentiable.const <;>
  apply Differentiable.mul <;>
  apply Differentiable.const

example (x: ℝ) : deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  ring
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  <;> ring
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  <;> ring
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  <;> ring
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  <;> ring
  <;> simp [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_sin,
    deriv_comp, deriv_id, deriv_const', deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_sin, deriv_comp, deriv_id, deriv_const']
  <;> ring

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [add_mul, mul_add, mul_assoc, mul_one, mul_comm, mul_left_comm]
  rw [deriv_add]
  all_goals
    simp only [add_mul, mul_add, mul_assoc, mul_one, mul_comm, mul_left_comm]
  all_goals
    simp only [Real.deriv_log, Real.deriv_exp, Real.deriv_sin, Real.deriv_cos,
      Real.deriv_pow, Real.deriv_id, mul_one, mul_zero, add_zero, zero_add, mul_assoc,
      mul_comm, mul_left_comm, sub_zero]
  all_goals
    ring_nf
  all_goals
    simp only [mul_one, mul_zero, add_zero, zero_add, mul_assoc, mul_comm, mul_left_comm,
      sub_zero]
  all_goals
    field_simp
  all_goals
    ring_nf
  all_goals
    norm_num
  all_goals
    assumption

example (x: ℝ)  (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  have h_div_ne_zero_29 : Real.log (5:ℝ) ≠ 0 := by norm_num
  have h_log_ne_zero_30 : x ≠ 0 := by assumption
  have h_log_ne_zero_32 : (5:ℝ) ≠ 0 := by norm_num
  field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring_nf
  simp only [mul_assoc, mul_comm, mul_left_comm]
  aesop

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  fun_prop
  <;> simp_all [Real.exp_ne_zero, mul_comm, mul_assoc, mul_left_comm, mul_one, add_assoc, add_comm,
    add_left_comm, mul_add, mul_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_add,
    mul_sub, sub_eq_add_neg, mul_one, add_assoc, add_comm, add_left_comm, mul_add, mul_sub, sub_eq_add_neg,
    mul_one, add_assoc, add_comm, add_left_comm, mul_add, mul_sub, sub_eq_add_neg, mul_one, add_assoc, add_comm,
    add_left_comm, mul_add, mul_sub, sub_eq_add_neg, mul_one, add_assoc, add_comm, add_left_comm, mul_add,
    mul_sub, sub_eq_add_neg, mul_one]
  <;> ring
  <;> field_simp [h_log_ne_zero_25, mul_comm, mul_assoc, mul_left_comm, mul_one, add_assoc, add_comm,
    add_left_comm, mul_add, mul_sub, sub_eq_add_neg, mul_one]
  <;> ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  apply congr_arg
  ring_nf
  <;> field_simp
  <;> ring
  <;> linarith
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  have := h_div_ne_zero_3
  simp_all
  field_simp
  ring_nf
  rw [Real.cos_arcsin] <;> norm_num
  field_simp
  ring_nf
  <;> simp_all only [Real.sin_arcsin]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  simp_all [deriv_cos, deriv_exp, deriv_pow, deriv_id'', deriv_const,
    deriv_mul, deriv_add, deriv_sub, deriv_sin]
  field_simp
  ring
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp only [div_eq_mul_inv, mul_assoc]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_3, Real.tan_eq_sin_div_cos, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  simp only [Real.tan_eq_sin_div_cos, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_3, Real.tan_eq_sin_div_cos, mul_assoc, mul_comm, mul_left_comm]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  apply Eq.symm
  field_simp [h_div_ne_zero_3, Real.exp_ne_zero, mul_comm]
  ring
  <;> apply Eq.symm
  <;> field_simp [h_div_ne_zero_3, Real.exp_ne_zero, mul_comm]
  <;> ring
  <;> apply Eq.symm
  <;> field_simp [h_div_ne_zero_3, Real.exp_ne_zero, mul_comm]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  simp only [deriv_log', mul_comm]
  field_simp [Real.exp_ne_zero, h_log_ne_zero_1, h_div_ne_zero_3, Real.sin_ne_zero_iff]
  ring_nf
  <;> simp [mul_assoc]
  <;> field_simp [Real.exp_ne_zero, h_log_ne_zero_1, h_div_ne_zero_3, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp [mul_assoc]
  <;> field_simp [Real.exp_ne_zero, h_log_ne_zero_1, h_div_ne_zero_3, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp [mul_assoc]
  <;> field_simp [Real.exp_ne_zero, h_log_ne_zero_1, h_div_ne_zero_3, Real.sin_ne_zero_iff]
  <;> ring_nf
  <;> simp [mul_assoc]

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_id'', deriv_sin,
    deriv_cos, deriv_pow, deriv_sub, mul_add, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_2]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_add, mul_comm, mul_left_comm, mul_assoc, mul_one, add_assoc, mul_right_comm]
  norm_num
  field_simp
  ring
  <;> simp only [Real.exp_ne_zero, mul_zero, mul_one, mul_add, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring
  <;> simp only [Real.exp_ne_zero, mul_zero, mul_one, mul_add, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring
  <;> simp only [Real.exp_ne_zero, mul_zero, mul_one, mul_add, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring
  <;> simp only [Real.exp_ne_zero, mul_zero, mul_one, mul_add, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring
  <;> simp only [Real.exp_ne_zero, mul_zero, mul_one, mul_add, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [h_log_ne_zero_25]
  rw [deriv_add]
  · field_simp [h_div_ne_zero_2, h_log_ne_zero_25]
    ring
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.exp
    apply differentiableAt_id
  apply DifferentiableAt.const_add
  apply DifferentiableAt.mul
  apply DifferentiableAt.exp
  apply differentiableAt_id
  apply DifferentiableAt.pow
  apply differentiableAt_id
  apply DifferentiableAt.sin
  apply DifferentiableAt.sub
  apply DifferentiableAt.const_mul
  apply differentiableAt_id
  apply DifferentiableAt.const_sub
  apply differentiableAt_id
  simp [h_div_ne_zero_2, h_log_ne_zero_25]
  apply DifferentiableAt.cos
  apply DifferentiableAt.log
  apply differentiableAt_id
  simp [h_log_ne_zero_25]

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [mul_assoc, mul_div_assoc, mul_div_cancel_left]
  ring_nf
  field_simp
  simp only [mul_assoc, mul_div_assoc, mul_div_cancel_left]
  ring_nf
  field_simp
  <;> simp only [mul_assoc, mul_div_assoc, mul_div_cancel_left]
  <;> ring_nf
  <;> field_simp

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  <;> field_simp [h_div_ne_zero_2]
  <;> simp [mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> apply IsBoundedAtFilter.add <;> apply IsBoundedAtFilter.mul <;> norm_num

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_2, Real.exp_ne_zero, mul_comm, mul_left_comm, mul_assoc,
    add_mul, mul_add, mul_sub, sub_mul]
  ring
  <;> simp only [mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, Real.exp_ne_zero, mul_comm, mul_left_comm, mul_assoc,
    add_mul, mul_add, mul_sub, sub_mul]
  <;> ring
  <;> simp only [mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, Real.exp_ne_zero, mul_comm, mul_left_comm, mul_assoc,
    add_mul, mul_add, mul_sub, sub_mul]
  <;> ring
  <;> simp only [mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, Real.exp_ne_zero, mul_comm, mul_left_comm, mul_assoc,
    add_mul, mul_add, mul_sub, sub_mul]
  <;> ring
  <;> simp only [mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, Real.exp_ne_zero, mul_comm, mul_left_comm, mul_assoc,
    add_mul, mul_add, mul_sub, sub_mul]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  apply deriv_eq_of_eq
  ring_nf
  <;> simp_all only [mul_inv_cancel, mul_div_cancel_left]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [mul_pow, mul_add, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf
  <;> simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> field_simp [h_div_ne_zero_3, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_pow, deriv_id'', deriv_log,
    deriv_sin, deriv_cos, deriv_sub, deriv_neg]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_25]
  ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_25: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all [mul_comm]
  apply deriv_mul_const_field
  ring
  apply deriv_mul_const_field
  ring
  apply deriv_mul_const_field
  ring
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [mul_comm]

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_sin]
  simp [mul_add, mul_comm, mul_left_comm]
  ring
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  apply congrArg
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  have h_cos_ne_zero_23 : cos (exp x * (x ^ 2 + 3) + x ^ 3 * (log x / log 5)) ≠ 0 := by
    intro h
    apply h_tan_ne_zero_1
    rw [← tan_eq_sin_div_cos]
    rw [h]
    simp
  have h_cos_ne_zero_20 : log 5 ≠ 0 := by
    intro h
    apply h_div_ne_zero_20
    rw [h]
    simp
  have h_log_ne_zero_20 : x ≠ 0 := by
    intro h
    apply h_log_ne_zero_21
    rw [h]
    simp
  have h_log_ne_zero_22 : (5:ℝ) ≠ 0 := by
    intro h
    apply h_log_ne_zero_23
    rw [h]
    simp
  field_simp [h_cos_ne_zero_23, h_cos_ne_zero_20, h_log_ne_zero_20, h_log_ne_zero_22]
  rw [deriv_tan]
  field_simp [h_cos_ne_zero_23, h_cos_ne_zero_20, h_log_ne_zero_20, h_log_ne_zero_22]
  ring_nf
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → Real.log x / Real.log 5 ≠ 0 := fun x hx ↦ by
    simp_all only [ne_eq, div_eq_mul_inv, mul_inv, inv_inv]
    apply mul_ne_zero
    · apply Real.log_ne_zero_of_pos_of_ne_one
      · linarith
      · norm_num
    · apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
  have h₂ : ∀ x : ℝ, deriv (λ y ↦ Real.exp (Real.exp y * (y ^ 2 + (3:ℝ)) + (y ^ 3) * (Real.log y / Real.log (5:ℝ))))) x =
    Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) *
    ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) +
    (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
    intro x
    rw [deriv_exp (λ y ↦ Real.exp y * (y ^ 2 + (3:ℝ)) + (y ^ 3) * (Real.log y / Real.log (5:ℝ))) x]
    simp [deriv_exp, deriv_add, deriv_mul, deriv_pow, deriv_log, deriv_id, deriv_const]
    ring
  simp_all

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h_exp_pos : 0 < Real.exp x := Real.exp_pos _
  have h_log_pos : 0 < Real.log (5:ℝ) := Real.log_pos (by norm_num)
  field_simp [h_log_ne_zero_1, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.exp_ne_zero, Real.log_ne_zero_of_pos_of_ne_one,
    mul_comm (Real.log x), mul_comm (Real.log (5:ℝ)), mul_comm (x ^ 2), mul_comm (x ^ 3)]
  ring_nf
  field_simp [h_log_pos, Real.exp_ne_zero, mul_comm (Real.log x), mul_comm (Real.log (5:ℝ)), mul_comm (x ^ 2), mul_comm (x ^ 3)]
  ring_nf
  field_simp [h_log_pos, Real.exp_ne_zero, mul_comm (Real.log x), mul_comm (Real.log (5:ℝ)), mul_comm (x ^ 2), mul_comm (x ^ 3)]
  ring_nf
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp_all [Real.log_ne_zero, mul_add, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22, h_div_ne_zero_19]
  ring
  <;> intro x <;> simp_all [Real.log_ne_zero, mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_log_ne_zero_20, h_log_ne_zero_22, h_div_ne_zero_19]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (λ x : ℝ ↦ Real.exp x * (x ^ 2 + 3) + x ^ 3 * Real.log x) x =
    Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) +
      (3 * x ^ 2 * Real.log x + x ^ 3 * (1 / x)) * Real.exp x +
        (x ^ 3 * Real.log x) * (2 * x) := by
    intro x hx
    simp only [Real.exp_ne_zero, mul_one, mul_zero, zero_mul, add_zero, mul_add, mul_assoc,
      mul_right_comm, mul_comm]
    apply deriv_congr_of_mem_nhds
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    simp only [Real.exp_ne_zero, mul_one, mul_zero, zero_mul, add_zero, mul_add, mul_assoc,
      mul_right_comm, mul_comm]
    ring_nf
  have h₂ : ∀ x : ℝ, x ≠ 0 →
    deriv (λ x : ℝ ↦ x ^ 3 * (Real.log x / Real.log 5) * Real.exp x * (x ^ 2 + 3)) x =
      (3 * x ^ 2 * (Real.log x / Real.log 5) * Real.exp x * (x ^ 2 + 3) +
        x ^ 3 * (1 / x * Real.log 5 / Real.log 5 ^ 2) * Real.exp x * (x ^ 2 + 3)) := by
    intro x hx
    simp only [Real.exp_ne_zero, mul_one, mul_zero, zero_mul, add_zero, mul_add, mul_assoc,
      mul_right_comm, mul_comm]
    apply deriv_congr_of_mem_nhds
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    simp only [Real.exp_ne_zero, mul_one, mul_zero, zero_mul, add_zero, mul_add, mul_assoc,
      mul_right_comm, mul_comm]
    ring_nf
  simp only [Real.exp_ne_zero, mul_one, mul_zero, zero_mul, add_zero, mul_add, mul_assoc,
    mul_right_comm, mul_comm]
  linarith [h₁ 0 one_ne_zero, h₂ 0 one_ne_zero]

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm]
  rw [Real.log_div (by norm_num) (by norm_num)]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  ring_nf
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, Real.log_div,
    Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp]
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  <;> ring_nf
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, Real.log_div,
    Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp]
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  <;> ring_nf
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, Real.log_div,
    Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp]
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  <;> ring_nf
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, Real.log_div,
    Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp]
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  <;> ring_nf
  <;> simp [Real.log_mul, Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp, Real.log_div,
    Real.log_pow, Real.log_inv, Real.log_one, Real.log_exp]
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [*, deriv_add, deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_id'', deriv_const']
  ring_nf
  <;> field_simp
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h1 : Real.log 5 ≠ 0 := by norm_num
  have h2 : x ≠ 0 := by assumption
  have h3 : (5:ℝ) ≠ 0 := by norm_num
  have h4 : (5 * x + 2) ≠ 0 := by assumption
  have h5 : Real.log (5 * x + 2) ≠ 0 := by
    intro h
    apply h4
    rw [← Real.exp_log (by positivity : 0 < 5 * x + 2)]
    rw [h]
    simp
  field_simp [*, Real.log_mul, Real.log_rpow, mul_assoc]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [mul_add, mul_assoc, mul_one, mul_zero, zero_mul, zero_add, mul_neg, mul_comm, mul_left_comm, mul_right_comm]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26, h_div_ne_zero_19]
  ring_nf
  rw [Real.log_mul]
  ring_nf
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  rw [deriv_sin]
  field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  <;> simp_all
  <;> apply DifferentiableAt.differentiableAt
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.sub_const
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.div_const

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  have h₁ : Real.log 5 ≠ 0 := by norm_num
  have h₂ : (5:ℝ) ≠ 0 := by norm_num
  have h₃ : (2:ℝ) ≠ 0 := by norm_num
  have h₄ : (3:ℝ) ≠ 0 := by norm_num
  have h₅ : (4:ℝ) ≠ 0 := by norm_num
  have h₆ : (5:ℝ) ≠ 0 := by norm_num
  have h₇ : (6:ℝ) ≠ 0 := by norm_num
  have h₈ : (7:ℝ) ≠ 0 := by norm_num
  have h₉ : (8:ℝ) ≠ 0 := by norm_num
  have h₁₀ : (9:ℝ) ≠ 0 := by norm_num
  have h₁₁ : (10:ℝ) ≠ 0 := by norm_num
  have h₁₂ : (11:ℝ) ≠ 0 := by norm_num
  have h₁₃ : (12:ℝ) ≠ 0 := by norm_num
  have h₁₄ : (13:ℝ) ≠ 0 := by norm_num
  have h₁₅ : (14:ℝ) ≠ 0 := by norm_num
  have h₁₆ : (15:ℝ) ≠ 0 := by norm_num
  have h₁₇ : (16:ℝ) ≠ 0 := by norm_num
  have h₁₈ : (17:ℝ) ≠ 0 := by norm_num
  have h₁₉ : (18:ℝ) ≠ 0 := by norm_num
  have h₂₀ : (19:ℝ) ≠ 0 := by norm_num
  have h₂₁ : (20:ℝ) ≠ 0 := by norm_num
  field_simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁]
  ring_nf
  norm_num [Real.exp_ne_zero]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one]
  norm_num
  ring_nf
  norm_num
  <;> simp_all only [mul_zero, mul_one, mul_add, mul_sub, sub_zero, zero_sub, sub_neg_eq_add, add_assoc]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  rw [deriv_tan]
  field_simp [Real.cos_ne_zero_iff.mpr h_tan_ne_zero_1]
  ring_nf
  <;> simp_all
  <;> apply mul_ne_zero
  <;> simp_all
  <;> apply div_ne_zero
  <;> simp_all
  <;> apply log_ne_zero_of_pos_of_ne_one
  <;> simp_all
  <;> norm_num
  <;> apply exp_pos
  <;> apply add_pos_of_pos_of_nonneg
  <;> simp_all
  <;> apply mul_nonneg
  <;> simp_all
  <;> apply pow_two_nonneg
  <;> simp_all
  <;> apply pow_three_nonneg
  <;> simp_all
  <;> apply log_nonneg
  <;> simp_all
  <;> apply le_of_lt
  <;> simp_all
  <;> apply exp_pos
  <;> apply add_pos_of_pos_of_nonneg
  <;> simp_all
  <;> apply mul_nonneg
  <;> simp_all
  <;> apply pow_two_nonneg
  <;> simp_all
  <;> apply pow_three_nonneg
  <;> simp_all
  <;> apply log_nonneg
  <;> simp_all
  <;> apply le_of_lt
  <;> simp_all
  <;> apply exp_pos
  <;> apply add_pos_of_pos_of_nonneg
  <;> simp_all
  <;> apply mul_nonneg
  <;> simp_all
  <;> apply pow_two_nonneg
  <;> simp_all
  <;> apply pow_three_nonneg
  <;> simp_all
  <;> apply log_nonneg
  <;> simp_all
  <;> apply le_of_lt
  <;> simp_all
  <;> apply exp_pos
  <;> apply add_pos_of_pos_of_nonneg
  <;> simp_all
  <;> apply mul_nonneg
  <;> simp_all
  <;> apply pow_two_nonneg
  <;> simp_all
  <;> apply pow_three_nonneg
  <;> simp_all
  <;> apply log_nonneg
  <;> simp_all
  <;> apply le_of_lt
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  simp only [deriv_exp, mul_add, mul_one, mul_assoc]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero]
  ring_nf
  <;> simp only [mul_add, mul_one, mul_assoc]
  <;> field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero]
  <;> ring_nf
  <;> simp only [mul_add, mul_one, mul_assoc]
  <;> field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero]
  <;> ring_nf
  <;> simp only [mul_add, mul_one, mul_assoc]
  <;> field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  rw [show
    (fun x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))))
    = (fun x ↦ Real.log (Real.exp x * (x ^ 2 + (3:ℝ)) - x ^ 3 * (Real.log x / Real.log (5:ℝ)))) by ext; ring_nf
  ]
  rw [show
    (fun x ↦ Real.log (Real.exp x * (x ^ 2 + (3:ℝ)) - x ^ 3 * (Real.log x / Real.log (5:ℝ))))
    = (fun x ↦ Real.log (Real.exp x * (x ^ 2 + (3:ℝ)) - x ^ 3 * (Real.log x / Real.log (5:ℝ)))) by ext; rfl
  ]
  apply deriv_log_of_ne_zero
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const',
    deriv_log, mul_one, mul_add, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  ring
  <;> simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const',
    deriv_log, mul_one, mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x))) := by
  simp [deriv_exp, deriv_mul, deriv_add, deriv_rpow_const, deriv_rpow_const_of_nonneg,
    deriv_log, deriv_id'', deriv_const, deriv_sub, deriv_zpow, mul_add, mul_sub, sub_mul,
    add_mul, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, sub_eq_add_neg,
    neg_mul, neg_neg, neg_add, neg_sub, neg_zero]
  ring
  <;> simp_all
  <;> ring
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  rw [add_comm]
  ring_nf
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22, Real.log_ne_zero]
  ring_nf
  <;> simp_all [Real.log_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  apply congr_arg
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  rw [deriv_sub, deriv_add]
  · rw [deriv_mul]
    rw [deriv_exp]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const']
    field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26]
    ring
  · rw [deriv_mul]
    rw [deriv_exp]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const']
    field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26]
    ring
  ·
    rw [deriv_log]
    field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26]
    ring
  all_goals simp_all
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp only [Real.exp_log, mul_comm]
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26]
  ring_nf
  <;> simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26]

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h_log_ne_zero_20 : Real.log 5 ≠ 0 := by
    apply Real.log_ne_zero
    norm_num
    norm_num
  have h_log_ne_zero_21 : x ≠ 0 := by
    intro h
    rw [h] at h_log_ne_zero_20
    simp at h_log_ne_zero_20
  have h_log_ne_zero_23 : (5:ℝ) ≠ 0 := by norm_num
  field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  rw [deriv_sin]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0 := by norm_num
  have h_log_ne_zero_21: x ≠ 0 := by intro h; simp [h] at h_div_ne_zero_20
  have h_log_ne_zero_23: (5:ℝ) ≠ 0 := by norm_num
  rw [deriv_cos]
  simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, mul_add, mul_comm, mul_left_comm, mul_assoc,
    deriv_mul, deriv_const_mul, deriv_exp, deriv_pow, deriv_id'', deriv_add, deriv_const,
    deriv_pow, deriv_id'', deriv_mul, deriv_const_mul, deriv_exp, deriv_pow, deriv_id'']
  ring
  <;> simp_all

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  have h₁ : ∀ x : ℝ, cos (exp x * (x ^ 2 + 3) * x ^ 3 * (log x / log 5)) ≠ 0 := by
    intro x
    simp [cos_pos]
    aesop
  have h₂ : ∀ x : ℝ, log 5 ≠ 0 := by
    intro x
    simp [log_pos]
    aesop
  have h₃ : ∀ x : ℝ, x ≠ 0 := by
    intro x
    simp [log_pos]
    aesop
  have h₄ : ∀ x : ℝ, (5 : ℝ) ≠ 0 := by
    intro x
    simp [log_pos]
    aesop
  field_simp [h₁, h₂, h₃, h₄]
  ring_nf
  field_simp [h₁, h₂, h₃, h₄]
  aesop

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h_log_ne_zero_20 : Real.log 5 ≠ 0 := by
    apply Real.log_ne_zero.mpr
    norm_num
  have h_log_ne_zero_21 : x ≠ 0 := by
    intro h_x_eq_zero
    apply h_log_ne_zero_21
    rw [h_x_eq_zero]
  have h_log_ne_zero_23 : (5:ℝ) ≠ 0 := by
    norm_num
  field_simp [h_log_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  <;> simp_all only [mul_zero, mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  field_simp [*, log_mul, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  ring
  <;> simp_all only [mul_zero, mul_one, mul_neg, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm,
    sub_neg_eq_add]
  <;> norm_num
  <;> apply exp_ne_zero

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [add_mul, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc, add_assoc,
    add_left_comm]
  -- When simplified, we see that the expression matches the desired form.
  ring
  -- Use the `simp` tactic to apply various simplification rules to the expression.
  <;> simp [*, log_exp]
  -- Normalize the expression using ring theory to simplify further.
  <;> ring_nf
  -- Simplify the expression by clearing denominators and canceling terms.
  <;> field_simp
  -- Use the `norm_num` tactic to normalize numerical expressions.
  <;> norm_num
  -- Finally, use the `linarith` tactic to handle linear arithmetic and conclude the proof.
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  simp [*, mul_add, add_mul, mul_comm, mul_left_comm]
  ring
  field_simp [*, mul_assoc]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [add_comm]
  rw [add_comm]
  field_simp [Real.log_ne_zero, h_log_ne_zero_20, h_div_ne_zero_19, h_log_ne_zero_22]
  ring_nf
  <;> simp [add_assoc, add_comm, add_left_comm]
  <;> field_simp [Real.log_ne_zero, h_log_ne_zero_20, h_div_ne_zero_19, h_log_ne_zero_22]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [deriv_mul, deriv_mul, deriv_mul, deriv_mul]
  ring_nf
  <;> simp_all
  <;> apply h_div_ne_zero_19
  <;> apply h_log_ne_zero_20
  <;> apply h_log_ne_zero_22
  <;> norm_num
  <;> linarith
  <;> ring_nf
  <;> simp_all
  <;> apply h_div_ne_zero_19
  <;> apply h_log_ne_zero_20
  <;> apply h_log_ne_zero_22
  <;> norm_num
  <;> linarith
  <;> ring_nf
  <;> simp_all
  <;> apply h_div_ne_zero_19
  <;> apply h_log_ne_zero_20
  <;> apply h_log_ne_zero_22
  <;> norm_num
  <;> linarith
  <;> ring_nf
  <;> simp_all
  <;> apply h_div_ne_zero_19
  <;> apply h_log_ne_zero_20
  <;> apply h_log_ne_zero_22
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  rw [deriv_add]
  simp only [deriv_exp, deriv_pow, deriv_mul, deriv_add, deriv_id'', deriv_const', deriv_log,
    mul_one, mul_zero, zero_mul, zero_add, mul_comm, mul_left_comm, mul_assoc, add_assoc,
    add_right_comm, add_comm]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm,
    mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_19, h_log_ne_zero_26]
  simp only [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_comm,
    mul_left_comm]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, mul_assoc]
  simp only [mul_comm, mul_left_comm]
  ring_nf
  simp only [Real.exp_ne_zero, mul_ne_zero_iff, ne_eq, not_false_eq_true, and_true]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero,
    sub_ne_zero]
  ring
  simp only [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero,
    sub_ne_zero]
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp_all only [mul_div_assoc, mul_one, mul_add, mul_comm, mul_left_comm, mul_assoc]
  apply deriv_tan
  <;> norm_num
  <;> apply mul_ne_zero
  <;> apply h_tan_ne_zero_1
  <;> apply h_div_ne_zero_4
  <;> apply h_div_ne_zero_20
  <;> apply h_log_ne_zero_21
  <;> apply h_log_ne_zero_23

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_exp]
  rw [deriv_mul]
  rw [deriv_exp]
  simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  simp only [one_div, mul_inv, mul_assoc]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_1]
  ring
  norm_num
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_1]
  ring

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  have h₀ : x ≠ 0 := by
    rintro rfl
    simp_all
  have h₁ : (5:ℝ) ≠ 0 := by norm_num
  have h₂ : (3:ℝ) ≠ 0 := by norm_num
  have h₃ : (x ^ 3) ≠ 0 := by
    simp_all
  have h₄ : Real.log ((5:ℝ)) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    norm_num
    norm_num
  have h₅ : (Real.log x / Real.log (5:ℝ)) ≠ 0 := by
    apply div_ne_zero
    exact h₀
    exact h₄
  simp_all [deriv_add, deriv_mul, deriv_const, deriv_exp, deriv_log, deriv_pow, deriv_pow,
    deriv_id, deriv_const, deriv_mul, deriv_div, deriv_pow, deriv_pow, deriv_id, deriv_const,
    deriv_mul, deriv_div, deriv_pow, deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_div,
    deriv_pow, deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_div, deriv_pow, deriv_pow,
    deriv_id, deriv_const, deriv_mul, deriv_div, deriv_pow, deriv_pow, deriv_id, deriv_const]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  field_simp [*, Real.log_ne_zero, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_exp, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_one, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> simp only [Real.log_zero, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  rw [deriv_add]
  · field_simp
    ring_nf
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.add
    · apply DifferentiableAt.exp
      exact differentiableAt_id
    · apply DifferentiableAt.pow
      exact differentiableAt_id
  · apply DifferentiableAt.div
    apply DifferentiableAt.mul
    · apply DifferentiableAt.exp
      exact differentiableAt_id
    · apply DifferentiableAt.add
      · apply DifferentiableAt.pow
        exact differentiableAt_id
      · exact differentiableAt_const _
    apply DifferentiableAt.log
    · apply DifferentiableAt.const_mul
      exact differentiableAt_id
    · norm_num
  · apply DifferentiableAt.sin
    apply DifferentiableAt.sub
    · apply DifferentiableAt.const_mul
      exact differentiableAt_id
    · exact differentiableAt_const _

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  rw [Real.exp_ne_zero]
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp_all only [one_div, mul_one, mul_div_assoc, mul_pow, mul_add, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.exp_ne_zero]
  ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.exp_ne_zero]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.exp_ne_zero]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.exp_ne_zero]
  <;> ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (x ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26, Real.log_ne_zero, Nat.cast_eq_zero,
    mul_comm]
  ring
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  rw [deriv_sin]
  field_simp [h_log_ne_zero_16]
  ring_nf
  <;> simp_all [Real.exp_ne_zero, Real.log_ne_zero, mul_assoc]
  <;> apply mul_assoc

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  simp only [Real.exp_zero, add_zero, mul_one, mul_zero, sub_zero, mul_add, mul_comm]
  norm_num
  ring_nf
  field_simp [h_log_ne_zero_16]
  rw [← Real.cos_pi_div_two]
  apply congr_arg
  ring_nf
  <;> simp
  <;> apply congr_arg
  <;> ring_nf
  <;> simp
  <;> apply congr_arg
  <;> ring_nf
  <;> simp
  <;> apply congr_arg
  <;> ring_nf
  <;> simp

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h₁ : cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ≠ 0 := by
    assumption
  have h₂ : (5:ℝ) * x + (2:ℝ) ≠ 0 := by
    assumption
  have h₃ : HasDerivAt (fun x => Real.exp x * (x ^ 2 + (3:ℝ))) (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.exp x * ((2:ℝ) * x)) x := by
    apply HasDerivAt.mul
    · apply hasDerivAt_exp
    · apply HasDerivAt.add
      · apply HasDerivAt.pow
        apply hasDerivAt_id
      · apply hasDerivAt_const
  have h₄ : HasDerivAt (fun x => Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) (3 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) x := by
    apply HasDerivAt.comp
    · apply HasDerivAt.pow
      apply hasDerivAt_log
      assumption
    · apply HasDerivAt.add
      · apply HasDerivAt.mul_const
        apply hasDerivAt_id
      · apply hasDerivAt_const
  have h₅ : HasDerivAt (fun x => Real.tan (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) _ x := by
    apply HasDerivAt.tan
    · apply h₃
    · apply h₁
  exact h₅.deriv

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h_log_ne_zero_16' : (5 * x + 2 : ℝ) ≠ 0 := by intro H; apply h_log_ne_zero_16 H
  simp only [Real.exp_add, Real.exp_mul, mul_add, mul_one, add_assoc]
  rw [Real.deriv_exp]
  simp only [mul_assoc, mul_comm, mul_left_comm, mul_add, mul_one, add_assoc, add_left_comm, add_comm]
  field_simp [h_log_ne_zero_16']
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h₀ :
    deriv (fun x ↦ Real.log (Real.exp x * (x ^ 2 + 3) + (Real.log (5 * x + 2)) ^ 3)) x =
      ((Real.exp x * (x ^ 2 + 3) + Real.exp x * (2 * x) + 3 * Real.log (5 * x + 2) ^ 2 * (5 / (5 * x + 2)))) /
        (Real.exp x * (x ^ 2 + 3) + Real.log (5 * x + 2) ^ 3) := by
    rw [deriv_log (by assumption)]
    field_simp [h_log_ne_zero_1, h_log_ne_zero_16, exp_ne_zero, pow_ne_zero, mul_comm]
    ring
  rw [h₀]

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [deriv_add, deriv_mul, deriv_log, deriv_zpow', deriv_exp, mul_add, mul_comm, mul_left_comm,
    mul_assoc, pow_two, add_assoc, add_left_comm]
  field_simp [h_log_ne_zero_15, mul_comm, mul_assoc, mul_left_comm]
  ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp [deriv_add, deriv_mul, deriv_zpow, deriv_exp, deriv_log, deriv_const, deriv_pow,
    mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc]
  field_simp [h_log_ne_zero_16]
  ring
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [Real.exp_ne_zero, mul_comm, mul_assoc, mul_left_comm]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25, Real.log_ne_zero_of_pos_of_ne_one]
  ring
  <;> simp [Real.exp_ne_zero, mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15, h_log_ne_zero_25, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp_all [Real.exp_add, Real.exp_log, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm]
  field_simp [Real.cos_log, Real.sin_log]
  ring
  <;> simp_all [Real.exp_add, Real.exp_log, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm]
  <;> field_simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp_all [Real.exp_add, Real.exp_log, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm]
  <;> field_simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp_all [Real.exp_add, Real.exp_log, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm]
  <;> field_simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp_all [Real.exp_add, Real.exp_log, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm]
  <;> field_simp [Real.cos_log, Real.sin_log]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  <;> simp [Real.exp_ne_zero]
  <;> field_simp [h_log_ne_zero_15]
  <;> ring_nf
  <;> simp [deriv_exp, deriv_log, deriv_sin, deriv_cos, deriv_pow]
  <;> ring_nf
  <;> simp [Real.exp_ne_zero]
  <;> field_simp [h_log_ne_zero_15]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp_all only [deriv_exp, deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id'',
    deriv_sin, deriv_cos, deriv_log, deriv_inv, mul_one, mul_zero, mul_neg, mul_add,
    mul_assoc, mul_comm, mul_left_comm]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [*, deriv_add]
  simp only [mul_add, add_assoc, mul_one, mul_comm]
  field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp_all [mul_add, add_assoc, mul_one, mul_comm]
  <;> field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_mul]
  simp [deriv_exp]
  simp [deriv_log]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> assumption
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul_const

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [deriv_sin, deriv_exp, deriv_pow, deriv_add, deriv_mul, deriv_sub, deriv_log,
    deriv_const, deriv_id, deriv_comp, deriv_pow, deriv_mul, deriv_sub, deriv_log,
    deriv_const, deriv_id, deriv_comp, deriv_pow, deriv_mul, deriv_sub, deriv_log,
    deriv_const, deriv_id, deriv_comp, deriv_pow, deriv_mul, deriv_sub, deriv_log,
    deriv_const, deriv_id, deriv_comp]
  field_simp [h_log_ne_zero_16]
  ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [deriv_sub, deriv_mul, deriv_exp, deriv_pow, deriv_id'', deriv_const, deriv_add, deriv_neg,
    deriv_log, mul_one, mul_zero, add_zero, zero_add, zero_mul, sub_zero, zero_sub, neg_mul, neg_neg]
  ring
  <;> field_simp <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  simp [tan_eq_sin_div_cos, mul_comm, sub_eq_add_neg, mul_add, mul_sub, add_comm, add_left_comm,
    add_assoc]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16, Real.exp_ne_zero,
    Real.cos_ne_zero_iff, Real.sin_ne_zero_iff, Real.log_ne_zero_iff,
    mul_comm, mul_left_comm, mul_assoc, mul_comm, sub_eq_add_neg,
    mul_add, mul_sub, add_comm, add_left_comm, add_assoc]
  ring_nf
  simp [tan_eq_sin_div_cos, mul_comm, sub_eq_add_neg, mul_add, mul_sub, add_comm, add_left_comm,
    add_assoc]

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_exp]
  field_simp [h_log_ne_zero_16]
  ring_nf
  rw [add_comm]
  field_simp [h_log_ne_zero_16]
  rw [mul_comm]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h₀ : ∀ x : ℝ, (Real.exp x * (x ^ 2 + 3) - (Real.log (5 * x + 2)) ^ 3) ≠ 0 := by
    intro x
    nlinarith [Real.exp_pos x, Real.log_pos (by nlinarith : (1 : ℝ) < 5 * x + 2)]
  have h₁ : ∀ x : ℝ, (5 * x + 2) ≠ 0 := by
    intro x
    nlinarith
  field_simp [h₀, h₁, Real.exp_ne_zero]
  ring_nf
  norm_num
  rw [← sub_eq_zero]
  field_simp [h₀, h₁, Real.exp_ne_zero]
  ring_nf
  norm_num
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [show (λ x ↦ Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 + Real.exp x * (x ^ 2 + (3:ℝ))) =
    (λ x ↦ Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 + Real.exp x * (x ^ 2 + (3:ℝ))) by rfl]
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_add]
  ring_nf
  <;> simp [deriv_exp, deriv_log, deriv_pow, h_log_ne_zero_15]
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.id
  <;> simp [h_log_ne_zero_15]

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x))) := by
  rw [show deriv (fun x ↦ Real.exp x * (x ^ 2 + (3:ℝ)) - Real.log ((5 * x + 2)) ^ 3 * Real.exp x * (x ^ 2 + (3:ℝ))) x =
    deriv (fun x ↦ Real.exp x * (x ^ 2 + (3:ℝ))) x - deriv (fun x ↦ Real.log ((5 * x + 2)) ^ 3 * Real.exp x * (x ^ 2 + (3:ℝ))) x by
    congr 1
    ext x
    ring_nf
    ]
  simp only [deriv_mul, deriv_exp, deriv_pow, deriv_add, deriv_id'', deriv_const', deriv_log,
    differentiableAt_id', differentiableAt_const, differentiableAt_pow, differentiableAt_add_const,
    differentiableAt_mul_const, deriv_sub, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_id'',
    deriv_const', deriv_mul, differentiableAt_id', differentiableAt_const, differentiableAt_pow,
    differentiableAt_add_const, differentiableAt_mul_const, deriv_sub]
  ring_nf
  field_simp [h_log_ne_zero_16]
  <;> ring_nf
  <;> simp_all
  <;> field_simp [h_log_ne_zero_16]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  rw [deriv_sub, deriv_add, deriv_mul, deriv_const_mul, deriv_exp, deriv_log,
    deriv_pow, deriv_add, deriv_id, deriv_const, deriv_cos, deriv_log]
  simp_all [div_eq_mul_inv]
  ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp_all only [mul_zero, add_zero, zero_mul, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25]
  ring_nf
  --  norm_num
  <;> simp_all only [Real.exp_log, add_left_neg, mul_one, mul_zero, zero_add, mul_neg, mul_one,
    mul_zero, add_zero, zero_mul, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, zero_mul, add_zero, zero_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_exp]
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_const]
  rw [deriv_mul]
  rw [deriv_const]
  rw [deriv_id]
  rw [deriv_log]
  rw [deriv_sin]
  ring_nf
  all_goals try simp [h_log_ne_zero_15]
  <;> field_simp [h_log_ne_zero_15]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp [*, deriv_sub]
  ring_nf
  <;> norm_num
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all [div_eq_mul_inv, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc,
    add_assoc, add_sub_assoc]
  field_simp [h_div_ne_zero_29, h_log_ne_zero_15]
  ring
  <;> apply mul_ne_zero h_log_ne_zero_30 h_log_ne_zero_32 <;> apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [deriv_sub, deriv_mul, deriv_pow, deriv_const, deriv_exp, deriv_id'', deriv_log,
    one_div]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  have h₁ : ∀ x, (fun x => Real.sin (Real.exp x * (x ^ 2 + (3 : ℝ)) * Real.log ((5 : ℝ) * x + (2 : ℝ)) ^ 3)) x = Real.sin (Real.exp x * (x ^ 2 + (3 : ℝ)) * Real.log ((5 : ℝ) * x + (2 : ℝ)) ^ 3) := fun x => rfl
  have h₂ : ∀ x, (fun x => Real.exp x * (x ^ 2 + (3 : ℝ)) * Real.log ((5 : ℝ) * x + (2 : ℝ)) ^ 3) x = Real.exp x * (x ^ 2 + (3 : ℝ)) * Real.log ((5 : ℝ) * x + (2 : ℝ)) ^ 3 := fun x => rfl
  simp only [h₁, h₂]
  rw [deriv_sin (fun x => Real.exp x * (x ^ 2 + (3 : ℝ)) * Real.log ((5 : ℝ) * x + (2 : ℝ)) ^ 3)]
  simp only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_assoc, mul_comm,
    mul_left_comm, mul_right_comm]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  apply congrArg
  funext
  rw [Real.cos_exp]
  ring
  <;> simp_all

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h1 : ∀ x : ℝ, x ∈ Set.univ → Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ)))) ≠ 0 := by
    intro x hx
    apply cos_ne_zero_iff.mpr
    apply ne_of_mem_of_not_mem hx
    simp
  have h2 : ∀ x : ℝ, x ∈ Set.univ → ((5:ℝ) * x + (2:ℝ)) ≠ 0 := by
    intro x hx
    apply ne_of_mem_of_not_mem hx
    simp
  field_simp [h1, h2]
  ring
  <;> simp_all
  <;> apply Differentiable.tan
  <;> apply Differentiable.exp
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.rpow_const
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.log
  <;> apply Differentiable.id
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.rpow_const
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.log
  <;> apply Differentiable.id
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.rpow_const
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.log
  <;> apply Differentiable.id
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.inv

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  have h₁ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.exp (x ^ 2)) x = Real.exp (x ^ 2) * (2 * x) := by
    intro x hx
    rw [deriv_exp (x ^ 2)]
    ring
  have h₂ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.exp (x ^ 2)) x = Real.exp (x ^ 2) * (2 * x) := by
    intro x hx
    rw [deriv_exp (x ^ 2)]
    ring
  have h₃ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.exp (x ^ 2)) x = Real.exp (x ^ 2) * (2 * x) := by
    intro x hx
    rw [deriv_exp (x ^ 2)]
    ring
  have h₄ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.exp (x ^ 2)) x = Real.exp (x ^ 2) * (2 * x) := by
    intro x hx
    rw [deriv_exp (x ^ 2)]
    ring
  have h₅ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.exp (x ^ 2)) x = Real.exp (x ^ 2) * (2 * x) := by
    intro x hx
    rw [deriv_exp (x ^ 2)]
    ring
  linarith [h₁ 1 (by norm_num), h₂ 1 (by norm_num), h₃ 1 (by norm_num), h₄ 1 (by norm_num), h₅ 1 (by norm_num)]

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / (Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  rw [log_exp]
  field_simp [Real.log_ne_zero_iff]
  ring
  <;>
  aesop
  <;>
  aesop
  <;>
  aesop

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp_all [deriv_add, deriv_mul, deriv_exp, deriv_rpow_const, deriv_log_of_pos, mul_comm]
  field_simp [h_log_ne_zero_15, mul_assoc]
  ring_nf
  <;> simp_all [mul_assoc, mul_comm, mul_left_comm]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp [Real.exp_add, Real.exp_log, mul_add, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  ring_nf
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [h_log_ne_zero_15, h_log_ne_zero_25, mul_add, mul_comm, mul_left_comm, mul_assoc,
    add_assoc, add_comm, add_left_comm]
  ring_nf
  simp_all [deriv_add, deriv_mul, deriv_exp, deriv_log, deriv_cos, deriv_sin, deriv_pow,
    deriv_const, mul_one, mul_zero, add_zero, zero_add, mul_add, mul_comm, mul_left_comm,
    mul_assoc, add_assoc, add_comm, add_left_comm]
  field_simp
  linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0 := by
    intro h
    linarith
  have h_log_ne_zero_25: x ≠ 0 := by
    intro h
    linarith
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25, Real.exp_ne_zero]
  ring_nf
  <;>
  simp only [mul_assoc, mul_add, mul_comm]
  <;>
  simp only [add_mul, mul_assoc, mul_comm, mul_left_comm]
  <;>
  simp only [add_assoc, add_left_comm, add_right_comm]
  <;>
  simp only [mul_assoc, mul_add, mul_comm]
  <;>
  simp only [add_mul, mul_assoc, mul_comm, mul_left_comm]
  <;>
  simp only [add_assoc, add_left_comm, add_right_comm]
  <;>
  simp only [mul_assoc, mul_add, mul_comm]
  <;>
  simp only [add_mul, mul_assoc, mul_comm, mul_left_comm]
  <;>
  simp only [add_assoc, add_left_comm, add_right_comm]

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [add_comm, add_assoc, mul_comm, mul_assoc, mul_left_comm]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_mul]
  simp [add_comm, add_assoc, mul_comm, mul_assoc, mul_left_comm]
  field_simp [h_log_ne_zero_15]
  ring
  all_goals
    simp only [Real.deriv_exp, Real.deriv_log, Real.deriv_pow, Real.deriv_id'', deriv_const',
      deriv_add, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_sub, deriv_neg, deriv_inv,
      mul_one, mul_zero, add_zero, zero_add, sub_zero]
  <;> simp only [Real.exp_zero, Real.log_one, zero_mul, zero_add, mul_zero, sub_neg_eq_add]

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp [*, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub]
  field_simp
  ring
  <;> apply_rules [deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_sub, deriv_sin, deriv_cos, deriv_const, deriv_id]
  <;> simp [*, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub]
  <;> field_simp
  <;> ring
  <;> apply_rules [deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_sub, deriv_sin, deriv_cos, deriv_const, deriv_id]
  <;> simp [*, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub]
  <;> field_simp
  <;> ring
  <;> apply_rules [deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_sub, deriv_sin, deriv_cos, deriv_const, deriv_id]
  <;> simp [*, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub]
  <;> field_simp
  <;> ring
  <;> apply_rules [deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_sub, deriv_sin, deriv_cos, deriv_const, deriv_id]

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  rw [deriv_add]
  field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> apply DifferentiableAt.add <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.log <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add_const <;> apply DifferentiableAt.pow <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul <;> apply DifferentiableAt.add_const

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all only [one_div, mul_one, mul_div_cancel_left]
  field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, h_log_ne_zero_16]
  ring
  <;> simp_all only [one_div, mul_one, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, h_log_ne_zero_16]
  <;> ring
  <;> simp_all only [one_div, mul_one, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, h_log_ne_zero_16]
  <;> ring
  <;> simp_all only [one_div, mul_one, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, h_log_ne_zero_16]
  <;> ring
  <;> simp_all only [one_div, mul_one, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, h_log_ne_zero_16]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  simp_all [deriv_sin, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  have h1 : (Real.log ((5 * x + 2 : ℝ)) ^ 3) ≠ 0 := by
    intro h
    apply h_div_ne_zero_3
    simp_all
  have h2 : (5 * x + 2 : ℝ) ≠ 0 := by
    intro h
    apply h_log_ne_zero_16
    simp_all
  field_simp [h1, h2, Real.log_ne_zero_iff, Real.exp_ne_zero]
  ring_nf
  rw [Real.cos_exp_mul_add_mul_div_log_pow]
  field_simp [h1, h2, Real.log_ne_zero_iff, Real.exp_ne_zero]
  ring_nf
  <;> aesop

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h₀ : cos ((Real.exp x * (x ^ 2 + 3)) / Real.log ((5 * x + 2) ^ 3)) ≠ 0 := by
    -- Porting note: added `by norm_num`
    apply cos_ne_zero_of_mem_Ioo <;>
    (try norm_num) <;>
    (try apply mem_Ioo_of_Ioo <;>
    (try apply Ioo_mem_nhds <;>
    (try norm_num) <;>
    (try apply mem_Ioo_of_Ioo))) <;>
    apply mem_Ioo_of_Ioo
  have h₁ : Real.log ((5 * x + 2) ^ 3) ≠ 0 := by
    -- Porting note: added `by norm_num`
    apply Real.log_ne_zero_of_pos_of_ne_one <;>
    (try norm_num) <;>
    (try apply pow_ne_zero <;>
    (try norm_num))
  have h₂ : (5 * x + 2) ≠ 0 := by
    -- Porting note: added `by norm_num`
    norm_num
  have h₃ : (Real.log ((5 * x + 2) ^ 3)) ^ 3 ≠ 0 := by positivity
  have h₄ : Real.exp x ≠ 0 := by apply Real.exp_ne_zero
  field_simp [*, Real.tan_eq_sin_div_cos, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp
  rw [← sub_eq_zero]
  -- Porting note: added `by norm_num`
  norm_num
  rw [← sub_eq_zero]
  -- Porting note: added `by ring_nf`
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  have h₀ : deriv (fun x => Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x =
      Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) *
        (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) -
          (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) /
        (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
    rw [deriv_exp (by simp)]
    field_simp
    ring
  rw [h₀]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_1: ((Real.exp (x)) * (x ^ 2 + (3:ℝ)) / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / (Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  simp_all only [deriv_log, one_div, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16]
  ring
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [add_sub_cancel, add_sub_assoc, mul_one, mul_zero, zero_add, sub_zero,
    mul_inv_rev, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero, Real.exp_ne_zero]
  ring
  <;> simp only [Real.log_exp, mul_one, mul_zero, zero_add, add_zero, sub_self, zero_sub,
    neg_neg, mul_neg, neg_mul, neg_inv, neg_div, neg_neg, mul_neg_one, neg_mul, neg_neg,
    mul_neg_one, neg_mul, neg_neg, mul_neg_one, neg_mul, neg_neg, mul_neg_one, neg_mul, neg_neg,
    mul_neg_one, neg_mul, neg_neg]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.exp x) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp [div_eq_mul_inv, mul_assoc]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  ring
  <;> simp [Real.log_exp]
  <;> simp [Real.exp_log]
  <;> ring
  <;> simp [Real.log_exp]
  <;> simp [Real.exp_log]
  <;> ring
  <;> simp [Real.log_exp]
  <;> simp [Real.exp_log]
  <;> ring
  <;> simp [Real.log_exp]
  <;> simp [Real.exp_log]
  <;> ring
  <;> simp [Real.log_exp]
  <;> simp [Real.exp_log]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_log, deriv_pow, deriv_id, deriv_const,
    deriv_div, deriv_cos, deriv_sin, deriv_neg, mul_one, mul_zero, zero_add, zero_sub,
    mul_neg, mul_one, mul_zero, neg_zero, sub_zero, neg_neg, mul_neg_one, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm]
  field_simp
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.cos (Real.log x)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_mul, deriv_const_mul, deriv_exp, deriv_pow, deriv_id'', deriv_add,
    deriv_log, deriv_cos, deriv_sin, deriv_id, deriv_pow, deriv_mul, deriv_const_mul,
    deriv_exp, deriv_log, deriv_cos, deriv_sin, deriv_id]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [deriv_add, deriv_mul, deriv_div, deriv_log, deriv_exp, deriv_rpow_const, deriv_sin,
    deriv_cos, mul_add, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [mul_pow, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  ring_nf
  rw [← add_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_id, deriv_const,
    mul_one, mul_zero, mul_neg, mul_add, mul_comm, mul_left_comm, mul_assoc,
    add_assoc, add_left_comm, add_comm, add_zero, zero_add, neg_add_rev, neg_mul,
    mul_inv_rev, inv_inv, sub_eq_add_neg]
  field_simp
  ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.exp x) * (x ^ 2 + (3:ℝ)) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.exp x * (x ^ 2 + (3:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (x ^ 3)) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.exp x * (x ^ 2 + (3:ℝ)) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all only [div_eq_mul_inv, mul_inv, mul_one, mul_assoc, mul_comm, mul_left_comm,
    inv_inv, mul_one, mul_assoc, mul_comm, mul_left_comm, inv_inv, mul_one]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring_nf
  simp_all only [mul_assoc, mul_comm, mul_left_comm, inv_inv, mul_one]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.cos (Real.log x) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.log x) (1 / x) x := fun x hx =>
    (hasDerivAt_log hx).hasDerivAt
  have h₂ : ∀ x : ℝ, HasDerivAt Real.cos (-Real.sin x) x := fun x => (hasDerivAt_cos x).hasDerivAt
  have h₃ : ∀ x : ℝ, HasDerivAt (fun x => x ^ 2) (2 * x) x := fun x => (hasDerivAt_pow 2 x).hasDerivAt
  have h₄ : ∀ x : ℝ, HasDerivAt (fun x => Real.sin x) (Real.cos x) x := fun x =>
    (hasDerivAt_sin x).hasDerivAt
  simp only [pow_two]
  field_simp
  ring_nf
  simp only [mul_neg, mul_one, mul_add, neg_mul, neg_neg]
  have h₅ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.sin (2 * x - 1)) (2 * Real.cos (2 * x - 1)) x :=
    fun x hx => (h₄ (2 * x - 1)).comp x ((h₃ x).const_sub _)
  have h₆ : ∀ x : ℝ, HasDerivAt (fun x => Real.cos (Real.log x + Real.sin (2 * x - 1) ^ 2))
    (-Real.sin (Real.log x + Real.sin (2 * x - 1) ^ 2) * (1 / x + 2 * Real.cos (2 * x - 1) * Real.sin (2 * x - 1))) x :=
    fun x => (h₂ (Real.log x + Real.sin (2 * x - 1) ^ 2)).comp x ((h₁ x hx).add ((h₅ x hx).pow 2))
  simp only [add_assoc, add_left_comm, add_right_comm, mul_assoc, mul_comm, mul_left_comm]
  field_simp
  linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun y ↦ Real.cos (y + Real.sin (2 * x - 1) ^ 2)) x = -Real.sin (x + Real.sin (2 * x - 1) ^ 2) * (1 + 2 * Real.sin (2 * x - 1) * Real.cos (2 * x - 1) * 2) := by
    intro x hx
    rw [deriv.comp]
    · simp [Real.deriv_cos, deriv_add, deriv_sin, deriv_const', deriv_mul, deriv_id'', deriv_pow, deriv_comp, deriv_sub, deriv_const, deriv_id]
      ring
    · exact differentiableAt_id'
    · exact differentiableAt_cos
  simp_all only [one_div, sub_eq_add_neg, mul_neg, mul_one, mul_add, mul_sub, mul_assoc]
  field_simp
  linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / Real.cos (Real.cos (Real.log x) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  simp_all [Real.log_zero, Real.log_one, Real.cos_zero, Real.sin_zero, mul_zero, zero_add, zero_sub,
    sub_zero, mul_one, one_mul, add_zero, sub_neg_eq_add, add_comm, add_left_comm,
    mul_comm, mul_left_comm]
  apply Eq.symm
  field_simp
  ring_nf
  <;> simp_all [Real.log_zero, Real.log_one, Real.cos_zero, Real.sin_zero, mul_zero, zero_add, zero_sub,
    sub_zero, mul_one, one_mul, add_zero, sub_neg_eq_add, add_comm, add_left_comm,
    mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [Real.log_zero, Real.log_one, Real.cos_zero, Real.sin_zero, mul_zero, zero_add, zero_sub,
    sub_zero, mul_one, one_mul, add_zero, sub_neg_eq_add, add_comm, add_left_comm,
    mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [Real.log_zero, Real.log_one, Real.cos_zero, Real.sin_zero, mul_zero, zero_add, zero_sub,
    sub_zero, mul_one, one_mul, add_zero, sub_neg_eq_add, add_comm, add_left_comm,
    mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp_all [Real.log_zero, Real.log_one, Real.cos_zero, Real.sin_zero, mul_zero, zero_add, zero_sub,
    sub_zero, mul_one, one_mul, add_zero, sub_neg_eq_add, add_comm, add_left_comm,
    mul_comm, mul_left_comm]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.cos (Real.log x) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.log x) (1 / x) x := fun x hx =>
    (hasDerivAt_log hx).congr_of_eventuallyEq (eventually_of_mem (Ioi_mem_nhds hx) fun y => by simp_all)
  have h₁ : HasDerivAt (fun x : ℝ => Real.cos (Real.log x) + (Real.sin ((2 * x - 1)) ^ 2))
    (-(1 / x) * Real.sin (Real.log x) + 2 * Real.sin ((2 * x - 1)) * Real.cos ((2 * x - 1))) x := by
    refine HasDerivAt.add ?_ ?_
    · exact (h₀ x h_log_ne_zero_6).hasDerivAt.cos
    · have h :=
        (hasDerivAt_sin ((2 * x - 1))).comp x (hasDerivAt_id' x |>.const_mul _)
      have h' :=
        (hasDerivAt_id' x).const_mul (2 : ℝ)
      convert h.pow 2 using 1
      ring
  have h₂ : HasDerivAt (fun x => Real.exp (Real.cos (Real.log x) + (Real.sin ((2 * x - 1)) ^ 2)))
    (Real.exp (Real.cos (Real.log x) + (Real.sin ((2 * x - 1)) ^ 2)) *
      (-(1 / x) * Real.sin (Real.log x) + 2 * Real.sin ((2 * x - 1)) * Real.cos ((2 * x - 1)))) x :=
    HasDerivAt.exp h₁
  convert h₂.deriv using 1
  field_simp [h_log_ne_zero_6]
  ring

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) + (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) / (Real.cos (Real.log x) + Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  rw [deriv_log (by intro h; simp_all [Real.log_ne_zero])]
  field_simp [h_log_ne_zero_1, h_log_ne_zero_6]
  ring_nf
  <;> simp [deriv_add, deriv_mul, deriv_sin, deriv_cos, deriv_id, deriv_const]
  <;> field_simp [h_log_ne_zero_1, h_log_ne_zero_6]
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.cos (Real.log x)) x = -1 * Real.sin (Real.log x) * (1 / x) := by
    intro x hx
    rw [deriv.cos, deriv_log x hx]
    ring
  have h2 : ∀ x : ℝ, deriv (fun x ↦ Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
    intro x
    rw [deriv_sin, deriv_pow]
    ring
  have h3 : ∀ x : ℝ, deriv (fun x ↦ Real.exp x * (x ^ 2 + (3:ℝ))) x = Real.exp x * (x ^ 2 + (3:ℝ)) + (Real.exp x * ((2:ℝ) * x)) := by
    intro x
    rw [deriv_mul, deriv_exp, deriv_add, deriv_pow, deriv_id', deriv_const]
    ring
  simp [h1, h2, h3]
  <;> ring
  <;> intro x hx <;> simp_all

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  rw [show (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) =
      (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) by rfl]
  rw [show (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) =
      (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) by rfl]
  rw [show (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) =
      (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) by rfl]
  rw [show (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) =
      (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) by rfl]
  simp only [Real.deriv_log, mul_one, mul_zero, mul_neg, mul_add, mul_comm]
  field_simp
  ring
  <;> simp only [Real.deriv_log, mul_one, mul_zero, mul_neg, mul_add, mul_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_cos, deriv_sin, deriv_sub, deriv_const, deriv_mul_const_field,
    deriv_log, deriv_id'', deriv_pow, deriv_add, deriv_cos, deriv_sin, deriv_sub, deriv_const,
    deriv_mul_const_field, deriv_log, deriv_id'', deriv_pow]
  field_simp [h_log_ne_zero_5]
  ring
  <;> simp only [Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, mul_add, mul_sub,
    mul_one, mul_neg, neg_neg, neg_mul, neg_add, add_assoc, add_left_comm, add_right_comm]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h_log_ne_zero_4 : x ≠ 0 := by assumption
  field_simp [h_log_ne_zero_4, Real.log_ne_zero]
  ring_nf
  <;> simp [deriv_add, deriv_mul, deriv_const, deriv_cos, deriv_sin, deriv_id, deriv_pow]
  <;> simp [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul]
  <;> simp [mul_add, mul_sub, add_sub_assoc, add_sub_cancel, add_assoc, add_left_comm, add_comm]
  <;> simp [neg_add_rev, neg_sub, neg_neg, mul_neg, sub_neg_eq_add, neg_mul, sub_eq_add_neg]
  <;> ring_nf
  <;> simp [add_assoc, add_left_comm, add_comm]
  <;> simp [mul_assoc, mul_left_comm, mul_comm]
  <;> simp [sub_eq_add_neg]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  apply HasDerivAt.deriv
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) ((-1) * Real.sin (Real.log x) * (1 / x)) x := by
    intro x hx
    have h := HasDerivAt.log (hasDerivAt_id x) hx
    have h' := HasDerivAt.cos (hasDerivAt_id (Real.log x))
    simpa using h'.comp x h
  have h₂ : ∀ x : ℝ, HasDerivAt (fun x => (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
    intro x
    have h := HasDerivAt.sin (hasDerivAt_id (2 * x - 1))
    simp only [mul_sub, mul_one, sub_mul, mul_assoc, mul_comm, mul_left_comm] at h ⊢
    convert h.pow 2 using 1
    ring
  have h₃ : ∀ x : ℝ, HasDerivAt (fun x => (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
    intro x
    have h := HasDerivAt.sin (hasDerivAt_id (2 * x - 1))
    simp only [mul_sub, mul_one, sub_mul, mul_assoc, mul_comm, mul_left_comm] at h ⊢
    convert h.pow 2 using 1
    ring
  convert (h₁ x h_log_ne_zero_5).add (h₂ x).add (h₃ x) using 1
  ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y => Real.log y) (1 / x) x :=
    fun x hx => (hasDerivAt_log hx).comp x (hasDerivAt_id x)
  have h₁ : HasDerivAt (fun y => Real.cos (Real.log y)) (-(1 / x) * Real.sin (Real.log x)) x :=
    (Real.hasDerivAt_cos (Real.log x)).comp x (h₀ x fun _ => id)
  have h₂ : HasDerivAt (fun y => (Real.sin (2 * y - 1)) ^ 2)
    (2 * Real.sin (2 * x - 1) * Real.cos (2 * x - 1) * (2:ℝ)) x :=
    (((hasDerivAt_id' x).const_mul _).sub_const _).sin.pow
  have h₃ : HasDerivAt (fun y => Real.sin (2 * y - 1)) (2 * Real.cos (2 * x - 1)) x :=
    ((hasDerivAt_id' x).const_mul _).sub_const _ |>.sin
  have h₄ : HasDerivAt (fun y => (Real.sin y) ^ 2) (2 * Real.sin x * Real.cos x) x :=
    (hasDerivAt_sin x).pow
  have h₅ : HasDerivAt (fun y => Real.cos (Real.log y) + (Real.sin (2 * y - 1)) ^ 2)
    (-(1 / x) * Real.sin (Real.log x) + (2 * Real.sin (2 * x - 1) * Real.cos (2 * x - 1) * (2:ℝ))) x :=
    h₁.add (h₂.comp x (h₃.pow))
  convert h₅.deriv
  simp only [sq, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, sub_mul, mul_sub]
  ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_cos, deriv_sin, deriv_log, deriv_mul, deriv_sub, deriv_pow, deriv_inv,
    deriv_const, deriv_id, pow_one, mul_one, sub_zero, zero_add, zero_sub, mul_zero, add_zero]
  field_simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> simp only [Real.cos_log, Real.sin_log, Real.cos_sub, Real.sin_sub, Real.cos_add,
    Real.sin_add, Real.cos_mul, Real.sin_mul, mul_assoc]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_cos, deriv_sin, deriv_log, deriv_pow, deriv_const, deriv_mul]
  field_simp [h_log_ne_zero_4, h_div_ne_zero_23, h_log_ne_zero_26]
  ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h₀ : (cos (log x) + (sin (2 * x - 1)) ^ 2 + (log (5 * x + 2)) ^ 3) =
    (fun x => cos (log x) + (sin (2 * x - 1)) ^ 2 + (log (5 * x + 2)) ^ 3) x := rfl
  rw [h₀]
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_cos, deriv_pow, deriv_log, deriv_add]
  simp [h_log_ne_zero_5, h_log_ne_zero_19]
  ring
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.const_sub
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow
  <;> apply DifferentiableAt.const_inv
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_pow

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [deriv_log, mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm,
    deriv_add, deriv_mul, deriv_const, deriv_sin, deriv_cos, deriv_id'', deriv_pow,
    Nat.cast_bit0, Nat.cast_one, Nat.cast_succ]
  field_simp [h_log_ne_zero_4, h_log_ne_zero_19]
  ring_nf
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm, mul_one, mul_zero, mul_neg,
    mul_right_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_19]
  <;> ring_nf
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm, mul_one, mul_zero, mul_neg,
    mul_right_comm]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [one_div, mul_one, mul_neg, mul_assoc]
  field_simp [h_log_ne_zero_6]
  ring_nf
  <;> simp only [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add, mul_neg,
    mul_one, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add, mul_neg,
    mul_one, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf
  <;> simp only [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add, mul_neg,
    mul_one, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₁ : ∀ x, x ≠ 0 → deriv (fun x ↦ Real.cos (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x =
    -1 * Real.sin (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) *
      ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
    intro x hx
    rw [deriv.neg, deriv_cos, sin_sub_sin, mul_comm]
    field_simp
    ring
  simpa using h₁ x h_log_ne_zero_6

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / Real.cos (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  have h₁ : ∀ x, cos (log x - (2 * x - 1) ^ 2) ≠ 0 := fun x => by
    have : cos (log x - (2 * x - 1) ^ 2) ≤ 1 := cos_le_one _
    have : 0 ≤ 1 := zero_le_one
    linarith
  have h₂ : ∀ x, sin ((2 * x - 1) ^ 2) ≤ 1 := fun x => sin_le_one _
  have h₃ : ∀ x, cos ((2 * x - 1) ^ 2) ≤ 1 := fun x => cos_le_one _
  have h₄ : ∀ x, sin (2 * x - 1) ≤ 1 := fun x => sin_le_one _
  have h₅ : ∀ x, cos (2 * x - 1) ≤ 1 := fun x => cos_le_one _
  simp only [deriv_tan_eq_sec_sq, ← sub_eq_add_neg, ← sub_eq_neg_add, ← sub_eq_add_neg, ← sub_eq_neg_add,
    deriv_sub, deriv_log', deriv_sub, deriv_log', deriv_sin, deriv_cos, deriv_id'', deriv_const',
    deriv_mul, deriv_pow, deriv_id'', deriv_const']
  field_simp [h₁, *]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [deriv_exp, deriv_sub, deriv_cos, deriv_log', deriv_sin, deriv_pow, deriv_id'',
    deriv_const, deriv_mul, deriv_neg, deriv_id, neg_one_mul]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) - (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.cos (Real.log x) - Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  have h₁ : ∀ x, cos (log x) - (sin (2 * x - 1)) ^ 2 ≠ 0 := by
    intro x
    nlinarith [sin_le_one (2 * x - 1), cos_le_one (log x)]
  have h₂ : ∀ x, x ≠ 0 := by
    intro x
    nlinarith
  rw [deriv_log_of_ne_zero _ (h₁ x)]
  field_simp [h₁, h₂]
  ring
  <;> simp only [sin_two_mul, cos_two_mul, sin_sub, cos_sub]
  <;> field_simp
  <;> ring
  <;> simp only [sin_two_mul, cos_two_mul, sin_sub, cos_sub]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  <;> simp_all
  <;> field_simp
  <;> linarith
  <;> ring_nf
  <;> apply Differentiable.comp
  <;> apply Differentiable.add
  <;> apply Differentiable.mul
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.id
  <;> apply Differentiable.const
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x))) := by
  simp only [sub_eq_add_neg, neg_mul, neg_neg, mul_neg]
  rw [deriv_add]
  · rw [deriv_add]
    · rw [deriv_mul]
      · rw [deriv_neg]
        rw [deriv_mul]
        · rw [deriv_cos, deriv_log, neg_one_mul]
          ring
        · exact differentiableAt_id
        exact differentiableAt_const _
      · exact differentiableAt_id
      exact differentiableAt_const _
    · rw [deriv_pow]
      rw [deriv_exp]
      simp
      exact differentiableAt_id
    exact differentiableAt_const _
  exact differentiableAt_id
  exact differentiableAt_const _

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [deriv_sub, deriv_add, deriv_cos, deriv_log, deriv_sin, deriv_mul, deriv_id, deriv_const,
    mul_one, mul_zero, sub_zero, zero_add, sub_self, mul_comm]
  field_simp [h_log_ne_zero_5]
  ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  rw [deriv_sub]
  simp only [Real.cos_log, Real.sin_log, mul_comm, mul_assoc, mul_left_comm]
  field_simp
  ring
  all_goals apply Differentiable.differentiableAt; apply Differentiable.cos; apply differentiable_log
  <;> apply Differentiable.sin
  <;> apply differentiable_id
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_add
  <;> apply Differentiable.const_pow
  <;> apply Differentiable.const_div
  <;> apply Differentiable.const_inv
  <;> apply Differentiable.id
  <;> apply Differentiable.log
  <;> apply Differentiable.exp
  <;> apply Differentiable.pow
  <;> apply Differentiable.div
  <;> apply Differentiable.inv
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.mul
  <;> apply Differentiable.neg
  <;> apply Differentiable.compl
  <;> apply Differentiable.sin
  <;> apply Differentiable.cos

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [sub_eq_add_neg, add_comm]
  field_simp [h_log_ne_zero_5]
  ring_nf
  <;> simp only [deriv_sub, deriv_add, deriv_neg, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_id'', deriv_const', deriv_log, deriv_pow, deriv_id, mul_one, mul_zero, zero_add, zero_sub, sub_zero, mul_comm]
  <;> ring_nf
  <;> simp only [deriv_sub, deriv_add, deriv_neg, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_id'', deriv_const', deriv_log, deriv_pow, deriv_id, mul_one, mul_zero, zero_add, zero_sub, sub_zero, mul_comm]
  <;> ring_nf
  <;> simp only [deriv_sub, deriv_add, deriv_neg, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_id'', deriv_const', deriv_log, deriv_pow, deriv_id, mul_one, mul_zero, zero_add, zero_sub, sub_zero, mul_comm]
  <;> ring_nf
  <;> simp only [deriv_sub, deriv_add, deriv_neg, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_id'', deriv_const', deriv_log, deriv_pow, deriv_id, mul_one, mul_zero, zero_add, zero_sub, sub_zero, mul_comm]
  <;> ring_nf
  <;> simp only [deriv_sub, deriv_add, deriv_neg, deriv_mul, deriv_comp, deriv_sin, deriv_cos, deriv_id'', deriv_const', deriv_log, deriv_pow, deriv_id, mul_one, mul_zero, zero_add, zero_sub, sub_zero, mul_comm]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [pow_two]
  rw [deriv_sub]
  · simp only [deriv_cos, deriv_sin, deriv_sub, deriv_mul, deriv_const, deriv_id'', deriv_pow, deriv_id,
    deriv_log, deriv_inv, deriv_comp, deriv_add, deriv_neg]
    ring
  · apply DifferentiableAt.sub <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.sin <;>
      apply DifferentiableAt.sub <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.cos <;>
      apply DifferentiableAt.const_mul <;> apply DifferentiableAt.id
  · apply DifferentiableAt.sub <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.sin <;>
      apply DifferentiableAt.sub <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.cos <;>
      apply DifferentiableAt.const_mul <;> apply DifferentiableAt.id

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_sub, deriv_mul, deriv_const_mul, deriv_cos,
    deriv_log, deriv_id'', deriv_pow, deriv_exp]
  field_simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_sub]
  <;> simp_all [Real.cos_log, Real.sin_log, Real.cos_two_mul, Real.sin_two_mul, mul_assoc, mul_comm, mul_left_comm]
  <;> norm_num
  <;> ring_nf
  <;> apply IsUnit.deriv_eq_zero
  <;> simp_all
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  fun_prop
  simp only [deriv_cos, deriv_sin, deriv_log, deriv_mul, deriv_pow, deriv_id'', deriv_const',
    deriv_comp, deriv_add, deriv_sub]
  field_simp [h_log_ne_zero_5, h_log_ne_zero_19, Real.cos_log, Real.sin_log, Real.cos_two_mul,
    Real.sin_two_mul, Real.cos_sub, Real.sin_sub, mul_comm, mul_assoc, mul_left_comm]
  ring
  <;> simp only [Real.cos_log, Real.sin_log, Real.cos_two_mul, Real.sin_two_mul, Real.cos_sub,
    Real.sin_sub, mul_comm, mul_assoc, mul_left_comm]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y => y.log) (1 / x) x := fun x hx =>
    (hasDerivAt_log hx).comp x ((hasDerivAt_id x).div_const _)
  have h₁ : ∀ x : ℝ, HasDerivAt Real.sin (Real.cos x) x := fun _ => hasDerivAt_sin _
  have h₂ : ∀ x : ℝ, HasDerivAt Real.cos (-Real.sin x) x := fun _ => hasDerivAt_cos _
  have h₃ : ∀ x : ℝ, HasDerivAt (fun y => y ^ 2) (2 * x) x := fun _ => hasDerivAt_pow 2 _
  have h₄ : ∀ x : ℝ, HasDerivAt (fun y => y * 2) 2 x := fun _ => hasDerivAt_id x |>.const_mul _
  have h₅ : ∀ x : ℝ, HasDerivAt (fun y => y - 1) 1 x := fun _ => hasDerivAt_id x |>.sub_const _
  simp only [mul_one, one_mul, mul_zero, zero_mul, mul_neg, neg_mul]
  have h₆ : ∀ x : ℝ, HasDerivAt (fun y => Real.sin y ^ 2) (2 * Real.sin x * Real.cos x) x := fun _ =>
    hasDerivAt_sin _ |>.comp _ <| hasDerivAt_pow 2 _
  have h₇ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos y * (2 * y - 1))
    (-Real.sin x * (2 * x - 1) + Real.cos x * 2) x := fun _ =>
    (hasDerivAt_cos _).mul ((h₄ _).sub (h₅ _))
  have h₈ : ∀ x : ℝ, HasDerivAt (fun y => Real.log y * Real.sin y ^ 2)
    (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)) x := fun _ =>
    (h₀ _ (by assumption)).mul (h₆ _)
  have h₉ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2))
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x))) x := fun _ =>
    (h₈ _).comp _ (h₂ _)
  have h₁₀ : ∀ x : ℝ, HasDerivAt (fun y => Real.sin (2 * y - 1)) (2 * Real.cos (2 * x - 1)) x := fun _ =>
    (h₁ _).comp _ (h₄ _).sub (h₅ _)
  have h₁₁ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  simp only [mul_neg, neg_mul]
  have h₁₂ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  have h₁₃ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  have h₁₄ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  have h₁₅ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  simp only [mul_neg, neg_mul]
  have h₁₆ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  have h₁₇ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^ 2) * (Real.cos x * Real.sin x ^ 2 + Real.log x * (2 * Real.sin x * Real.cos x)))) x :=
    fun _ => (h₉ _).mul (h₁₀ _)
  have h₁₈ : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (Real.log y * Real.sin y ^ 2) * Real.sin (2 * y - 1))
    (Real.cos (Real.log x * Real.sin x ^ 2) * (2 * Real.cos (2 * x - 1)) +
    (-Real.sin (Real.log x * Real.sin x ^
example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.cos (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
    intro x hx
    rw [deriv_cos, neg_mul, neg_neg]
    simp [Real.sin_cos_cancel, mul_add, mul_comm, mul_left_comm, mul_assoc,
      Real.cos_eq_zero_iff]
    ring
  apply h₁
  apply h_log_ne_zero_6

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / Real.cos (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  rw [deriv_tan_comp]
  <;> simp_all [deriv_tan]
  <;> field_simp [h_log_ne_zero_6]
  <;> ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  have h₀ : ∀ x ≠ 0, deriv (fun x => Real.exp (Real.cos (Real.log x) * Real.sin ((2 * x - 1)) ^ 2)) x =
      Real.exp (Real.cos (Real.log x) * Real.sin ((2 * x - 1)) ^ 2) *
        (((-1) * Real.sin (Real.log x) * (1 / x)) * (Real.sin ((2 * x - 1)) ^ 2) +
          (Real.cos (Real.log x) * (2 * Real.sin ((2 * x - 1)) * (Real.cos ((2 * x - 1)) * 2)))) := by
    intro x hx
    rw [deriv_exp (fun x => Real.cos (Real.log x) * Real.sin ((2 * x - 1)) ^ 2)]
    simp only [deriv_mul, deriv_cos, deriv_sin, deriv_log, deriv_pow, deriv_id'', deriv_const']
    field_simp
    ring
  simp_all

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := by
    intro x hx
    exact Real.log_ne_zero_of_pos_of_ne_one (pos_iff_ne_zero.mpr hx)
  have h2 : ∀ x : ℝ, Real.sin x ≠ 0 → x ≠ 0 := by
    intro x hx
    intro h
    rw [h] at hx
    simp at hx
  have h3 : ∀ x : ℝ, Real.cos x ≠ 0 → x ≠ 0 := by
    intro x hx
    intro h
    rw [h] at hx
    simp at hx
  have h4 : ∀ x : ℝ, Real.sin x ≠ 0 → Real.cos x ≠ 0 := by
    intro x hx
    exact (Real.sin_ne_zero_iff.mp hx).2
  have h5 : ∀ x : ℝ, Real.cos x ≠ 0 → Real.sin x ≠ 0 := by
    intro x hx
    exact (Real.cos_ne_zero_iff.mp hx).1
  field_simp [h1, h2, h3, h4, h5]
  ring
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  simp [deriv_add, deriv_mul, deriv_exp, deriv_pow, deriv_id, deriv_const, deriv_log, deriv_sin, deriv_cos]
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.exp x) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  simp_all only [ne_eq, one_div, mul_pow, mul_add, mul_comm, mul_assoc, mul_left_comm]
  field_simp
  ring_nf
  <;> apply Real.cos_log_pos
  <;> apply Real.sin_log_pos
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_of_ne_zero
  <;> apply add_pos <;> apply sq_pos_of_ne_zero
  <;> apply mul_pos <;> apply sq_pos_of_ne_zero
  <;> apply sub_pos
  <;> apply mul_pos
  <;> apply Real.cos_pos_of_mem_Ioo <;> apply Real.sin_pos_of_mem_Ioo
  <;> apply Real.exp_pos
  <;> apply sq_pos_
example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [deriv_add, deriv_mul, deriv_comp, deriv_cos, deriv_sin, deriv_log, deriv_id'', deriv_const,
    mul_comm, mul_left_comm, mul_assoc, mul_sub, mul_one, mul_div_assoc, mul_add]
  field_simp [h_log_ne_zero_5]
  ring
  <;> simp only [mul_assoc]
  <;> simp only [mul_comm, mul_left_comm]
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 →  HasDerivAt (fun x ↦ Real.cos (Real.log x)) (-((1:ℝ) / x) * Real.sin (Real.log x)) x := by
    intro x hx
    have h₁ : HasDerivAt Real.log x (1 / x) := hasDerivAt_log hx
    have h₂ : HasDerivAt Real.cos (Real.cos (Real.log x) * (-Real.sin (Real.log x))) (Real.log x) := by
      simpa only [mul_neg_one] using (hasDerivAt_cos (Real.log x)).comp x (hasDerivAt_log hx)
    simpa only [mul_neg_one, neg_mul] using h₂.comp x h₁
  simp only [mul_sub, mul_one, mul_add, mul_comm, mul_left_comm]
  field_simp [h₀]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  have h₁ : x ≠ 0 := h_log_ne_zero_5
  rw [deriv_add]
  <;> field_simp
  <;> ring
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.comp
  <;> apply differentiableAt_id
  <;> apply differentiableAt_const
  <;> apply differentiableAt_sin
  <;> apply differentiableAt_cos
  <;> apply differentiableAt_log
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) (-(1 / x) * Real.sin (Real.log x)) x := by
    intro x hx
    have h₁ : HasDerivAt Real.log (1 / x) x := hasDerivAt_log hx
    have h₂ : HasDerivAt (fun x => Real.cos (Real.log x)) (-(Real.sin (Real.log x)) * (1 / x)) x :=
      h₁.cos.comp x (hasDerivAt_log hx)
    simpa using h₂
  have h₂ : ∀ x : ℝ, HasDerivAt (fun x => Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * Real.cos ((2:ℝ) * x - (1:ℝ)) * 2) x := fun x => by
    have h₂ : HasDerivAt (fun x => (2:ℝ) * x - (1:ℝ)) 2 x := by
      have h₂ : HasDerivAt (fun x => (2:ℝ) * x) 2 x := hasDerivAt_const x (2:ℝ)
      have h₃ : HasDerivAt (fun x => x - (1:ℝ)) 1 x := hasDerivAt_id x
      have h₄ : HasDerivAt (fun x => (2:ℝ) * x - (1:ℝ)) 2 x := h₂.sub h₃
      simpa using h₄
    have h₃ : HasDerivAt (fun x => Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * Real.cos ((2:ℝ) * x - (1:ℝ)) * 2) x :=
      ((hasDerivAt_pow 2 (fun x => Real.sin ((2:ℝ) * x - (1:ℝ))) x).comp x h₂).mul h₂
    simpa using h₃
  have h₃ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))
    (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) x := fun x hx => by
    have h₃ : HasDerivAt (fun x => Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))
      (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) x := by
      have h₃ : HasDerivAt (fun x => Real.cos (Real.log x)) (-(1 / x) * Real.sin (Real.log x)) x := h₁ x hx
      have h₄ : HasDerivAt (fun x => (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * Real.cos ((2:ℝ) * x - (1:ℝ)) * 2) x := h₂ x
      have h₅ : HasDerivAt (fun x => Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))
        (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) x :=
        h₃.mul h₄
      simpa using h₅
    simpa using h₃
  simpa using h₃

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  rw [deriv_add]
  simp [deriv_cos, deriv_sin, deriv_pow, deriv_id, deriv_const, deriv_log, h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  field_simp [h_log_ne_zero_5, h_div_ne_zero_23, h_log_ne_zero_26]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (x ^ 3)) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all [Real.cos_log, Real.sin_log, mul_assoc]
  field_simp [Real.log_mul, h_log_ne_zero_26, h_log_ne_zero_6, h_div_ne_zero_23]
  ring
  <;> assumption
  <;> simp_all [Real.cos_log, Real.sin_log, mul_assoc]

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp [deriv_add, deriv_mul, deriv_cos, deriv_sin, deriv_log, deriv_pow, deriv_id, h_log_ne_zero_5, h_log_ne_zero_19, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  ring_nf
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  <;> simp [Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [ne_eq, one_div, mul_eq_mul_left_iff, mul_eq_mul_right_iff]
  apply deriv_const_mul_field
  apply deriv_const_mul_field
  apply deriv_const_mul_field
  apply deriv_mul
  apply deriv_mul
  apply deriv_mul
  apply deriv_log
  apply deriv_log
  apply deriv_sin
  apply deriv_cos
  ring
  <;> simp_all
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.cos (Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  rw [deriv_sin]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6]
  ring_nf
  <;> simp_all [Real.sin_zero, Real.cos_zero]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  simp only [Real.cos_log, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_mul,
    mul_one]
  apply HasDerivAt.deriv
  have h₀ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos x) (-(Real.sin x)) x := fun x hx =>
    (Real.hasDerivAt_cos x).neg
  have h₁ : ∀ x : ℝ, HasDerivAt (fun x => Real.log x) (1 / x) x := fun x => (Real.hasDerivAt_log x).2
  have h₂ : ∀ x : ℝ, HasDerivAt (fun x => x ^ 2) (2 * x) x := fun x => (hasDerivAt_pow 2 x).2
  have h₃ : ∀ x : ℝ, HasDerivAt (fun x => Real.sin x) (Real.cos x) x := fun x => hasDerivAt_sin x
  have h₄ : ∀ x : ℝ, HasDerivAt (fun x => Real.cos x) (-(Real.sin x)) x := fun x =>
    (Real.hasDerivAt_cos x).neg
  have h₅ : ∀ x : ℝ, HasDerivAt (fun x => x⁻¹) (-(x ^ 2)⁻¹) x := fun x => by
    simpa using ((hasDerivAt_id x).inv (by simp)).neg
  have h₆ : ∀ x : ℝ, HasDerivAt (fun x => 2 * x) 2 x := fun x => (hasDerivAt_mul_const 2 x).2
  have h₇ : ∀ x : ℝ, HasDerivAt (fun x => 2 * Real.sin x) (2 * Real.cos x) x := fun x =>
    (hasDerivAt_const 2 x).mul (h₃ x)
  have h₈ : ∀ x : ℝ, HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin x * Real.cos x) x := fun x =>
    ((h₃ x).pow 2).2
  have h₉ : ∀ x : ℝ, HasDerivAt (fun x => Real.cos x ^ 2) (-(2 * Real.cos x * Real.sin x)) x :=
    fun x => ((h₄ x).pow 2).2
  have h₁₀ : ∀ x : ℝ, HasDerivAt (fun x => Real.sin (Real.cos x) ^ 2)
    (2 * Real.sin (Real.cos x) * (-(Real.sin x))) x := fun x =>
    ((h₈ (Real.cos x)).comp x (h₄ x)).2
  have h₁₁ : ∀ x : ℝ, HasDerivAt (fun x => Real.cos (Real.sin x) ^ 2)
    (2 * Real.cos (Real.sin x) * (Real.cos x)) x := fun x =>
    ((h₉ (Real.sin x)).comp x (h₃ x)).2
  have h₁₂ : ∀ x : ℝ, HasDerivAt (fun x => Real.log (Real.sin x))
    (1 / Real.sin x * Real.cos x) x := fun x =>
    (h₁ (Real.sin x)).comp x (h₃ x)
  have h₁₃ : ∀ x : ℝ, HasDerivAt (fun x => Real.log (Real.cos x))
    (-(1 / Real.cos x * Real.sin x)) x := fun x =>
    (h₁ (Real.cos x)).comp x (h₄ x)
  have h₁₄ : ∀ x : ℝ, HasDerivAt (fun x => Real.log (Real.sin x ^ 2))
    (2 / Real.sin x * Real.cos x) x := fun x =>
    (h₁ (Real.sin x ^ 2)).comp x ((h₈ x).2)
  have h₁₅ : ∀ x : ℝ, HasDerivAt (fun x => Real.log (Real.cos x ^ 2))
    (-(2 / Real.cos x * Real.sin x)) x := fun x =>
    (h₁ (Real.cos x ^ 2)).comp x ((h₉ x).2)
  simpa [Real.sin_two_mul, Real.cos_two_mul, mul_neg, mul_assoc] using
    h₁₅ x
  <;> simp_all [Real.sin_two_mul, Real.cos_two_mul, mul_neg, mul_assoc]
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / Real.cos (Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by
  have h₀ : ∀ x : ℝ, cos (cos x / sin (2 * x - 1) ^ 2) ≠ 0 := by
    intro x
    exact cos_ne_zero_of_ne_zero_of_ne_pi (sin_ne_zero_of_ne_zero_of_ne_pi (by linarith)) (by linarith)
  have h₁ : ∀ x : ℝ, sin (2 * x - 1) ^ 2 ≠ 0 := by
    intro x
    exact pow_ne_zero 2 (sin_ne_zero_of_ne_zero_of_ne_pi (by linarith))
  have h₂ : ∀ x : ℝ, x ≠ 0 := by
    intro x
    exact (by linarith)
  field_simp [h₀, h₁, h₂, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  ring
  <;> simp_all
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = Real.exp (Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) := by
  rw [deriv_exp]
  simp only [deriv_log', one_div, mul_neg, mul_one, mul_div_assoc, mul_assoc]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6]
  ring
  <;> simp only [Real.exp_log]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6]
  <;> ring
  <;> simp only [Real.exp_log]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6]
  <;> ring
  <;> simp only [Real.exp_log]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) / (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) / (Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) := by
  simp_all only [one_div, mul_comm, mul_assoc, mul_left_comm]
  field_simp [Real.log_ne_zero_iff, Real.sin_ne_zero_iff, Real.cos_ne_zero_iff]
  rw [deriv_log_cos_div_sin_sq, deriv_log_sin_mul]
  field_simp [Real.log_ne_zero_iff, Real.sin_ne_zero_iff, Real.cos_ne_zero_iff]
  ring

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  · field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
    ring
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.cos
    apply DifferentiableAt.log
    exact differentiableAt_id
  · apply DifferentiableAt.add
    · apply DifferentiableAt.mul_const
      apply Differentiable.differentiableAt
      apply differentiable_exp
    · apply Differentiable.differentiableAt
      apply differentiable_id.pow
  <;> simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> try apply DifferentiableAt.pow
  <;> try apply DifferentiableAt.sin
  <;> try apply DifferentiableAt.exp
  <;> try apply DifferentiableAt.log
  <;> try apply DifferentiableAt.add
  <;> try apply DifferentiableAt.mul_const
  <;> try apply DifferentiableAt.add
  <;> try apply DifferentiableAt.mul_const
  <;> try apply DifferentiableAt.const_mul
  <;> try apply DifferentiableAt.const_add
  <;> simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> simp [h_div_ne_zero_2, h_log_ne_zero_5]

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.exp x) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.exp x) * ((2:ℝ) * x)) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → Real.cos (Real.log x) ≠ 0 := by
    intro x hx
    apply Real.cos_ne_zero_of_mem_Ioo
    exact ⟨by linarith [Real.log_neg_iff (by norm_num : (0 : ℝ) < 1) hx],
      by linarith [Real.log_one_lt_iff (by norm_num : (0 : ℝ) < 1) hx]⟩
  have h₁ : ∀ x : ℝ, x ≠ 0 → (Real.sin ((2 : ℝ) * x - (1 : ℝ))) ^ 2 ≠ 0 := by
    intro x hx
    apply pow_ne_zero
    apply Real.sin_ne_zero_of_mem_Ioo
    exact ⟨by linarith [Real.log_neg_iff (by norm_num : (0 : ℝ) < 1) hx],
      by linarith [Real.log_one_lt_iff (by norm_num : (0 : ℝ) < 1) hx]⟩
  have h₂ : ∀ x : ℝ, x ≠ 0 → x ^ 2 + (3 : ℝ) ≠ 0 := by
    intro x hx
    nlinarith
  field_simp [h₀, h₁, h₂, Real.cos_ne_zero_of_mem_Ioo, Real.sin_ne_zero_of_mem_Ioo]
  ring_nf
  <;> simp_all
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.div
  <;> apply Differentiable.mul
  <;> apply Differentiable.add
  <;> apply Differentiable.sub
  <;> apply Differentiable.cos
  <;> apply Differentiable.sin
  <;> apply Differentiable.exp
  <;> apply Differentiable.log
  <;> apply Differentiable.pow
  <;> apply Differentiable.const
  <;> apply Differentiable.id

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + Real.cos (Real.log x)) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  rw [deriv_add]
  <;> simp_all [deriv_div, deriv_log, deriv_cos, deriv_sin, deriv_id]
  <;> field_simp
  <;> ring
  <;> assumption
  <;> norm_num
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.id
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.sub
  <;> apply DifferentiableAt.const_sub

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [deriv_div]
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num
  <;> simp [Real.cos_log, Real.sin_log, mul_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5]
  <;> ring_nf
  <;> norm_num

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  <;> field_simp <;>
  try
    (apply Real.log_ne_zero_of_pos_of_ne_one <;>
    linarith [sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)]
  <;>
  (apply Real.log_ne_zero_of_pos_of_ne_one <;>
    linarith [sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)]
  <;>
  (apply Real.log_ne_zero_of_pos_of_ne_one <;>
    linarith [sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)]
  <;>
  (apply Real.log_ne_zero_of_pos_of_ne_one <;>
    linarith [sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)]
  <;>
  (apply Real.log_ne_zero_of_pos_of_ne_one <;>
    linarith [sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
      sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)]
  <;>
  apply IsUnit.mk0
  <;>
  norm_num

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  ring_nf
  <;> simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  <;> ring_nf
  <;> simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  <;> ring_nf
  <;> simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  <;> ring_nf
  <;> simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  <;> ring_nf
  <;> simp only [one_div, mul_pow, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_5, sin_ne_zero_iff, cos_ne_zero_iff]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [add_comm, add_left_comm, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_5, h_div_ne_zero_2, h_log_ne_zero_26, h_div_ne_zero_23,
    Real.sin_ne_zero_iff, Real.cos_ne_zero_iff]
  ring_nf
  simp only [Real.cos_log, Real.sin_log, mul_div_assoc, mul_assoc]
  field_simp
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (x ^ 3)) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_div]
  <;>
  simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_23, h_log_ne_zero_26, Real.log_ne_zero_of_pos_of_ne_one]
  <;>
  field_simp [h_log_ne_zero_6, h_log_ne_zero_26]
  <;>
  ring_nf
  <;>
  simp_all [Real.log_ne_zero_of_pos_of_ne_one]
  <;>
  field_simp [h_log_ne_zero_6, h_log_ne_zero_26]
  <;>
  linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  field_simp [h_div_ne_zero_2, h_log_ne_zero_5, h_log_ne_zero_19, sub_eq_zero, add_eq_zero_iff_eq_neg, mul_comm]
  ring_nf
  <;>
  simp only [mul_assoc, mul_comm, mul_left_comm]
  <;>
  simp only [deriv_log, deriv_add, deriv_mul, deriv_const, deriv_cos, deriv_sin, deriv_id, deriv_pow, deriv_div,
    deriv_sub, deriv_neg, deriv_exp, deriv_id, deriv_const, deriv_log, deriv_mul, deriv_add, deriv_cos,
    deriv_sin, deriv_id, deriv_pow, deriv_div, deriv_sub, deriv_neg, deriv_exp, deriv_id]
  <;>
  simp only [mul_assoc, mul_comm, mul_left_comm]

example (x: ℝ)  (h_div_ne_zero_2: (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) - Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.cos (Real.log x) / Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_div]
  <;> field_simp <;> simp_all [Real.cos_log]
  <;> norm_num
  <;> ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_sin, deriv_add]
  ring_nf
  simp [deriv_cos, deriv_log, deriv_add, deriv_mul, deriv_const, deriv_id, deriv_pow,
    Real.log_ne_zero, Real.log_pos]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp [deriv_cos, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm, sub_eq_add_neg,
    mul_add, mul_sub, mul_neg, mul_one, mul_div_assoc, mul_div_cancel_left _ h_log_ne_zero_6,
    mul_div_cancel_left _ h_div_ne_zero_14, mul_div_cancel_left _ h_log_ne_zero_17]
  ring
  <;> simp only [add_assoc, add_right_comm, add_left_comm, mul_one, mul_div_assoc,
    mul_div_cancel_left _ h_log_ne_zero_6, mul_div_cancel_left _ h_div_ne_zero_14,
    mul_div_cancel_left _ h_log_ne_zero_17]
  <;> ring
  <;> simp only [add_assoc, add_right_comm, add_left_comm, mul_one, mul_div_assoc,
    mul_div_cancel_left _ h_log_ne_zero_6, mul_div_cancel_left _ h_div_ne_zero_14,
    mul_div_cancel_left _ h_log_ne_zero_17]
  <;> ring
  <;> simp only [add_assoc, add_right_comm, add_left_comm, mul_one, mul_div_assoc,
    mul_div_cancel_left _ h_log_ne_zero_6, mul_div_cancel_left _ h_div_ne_zero_14,
    mul_div_cancel_left _ h_log_ne_zero_17]
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  rw [deriv_tan_comp]
  simp [mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [Real.exp_eq_exp, Real.cos_eq_cos, mul_one, mul_zero, zero_add, mul_neg, mul_one]
  field_simp
  ring_nf
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h₀ : cos (log x) + x ^ 3 * (log x / log 5) ≠ 0 := h_log_ne_zero_1
  have h₁ : x ≠ 0 := h_log_ne_zero_6
  have h₂ : log 5 ≠ 0 := h_div_ne_zero_14
  have h₃ : (5:ℝ) ≠ 0 := h_log_ne_zero_17
  field_simp [*, Real.log_ne_zero, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one] at *
  ring_nf
  field_simp [*, Real.log_ne_zero, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one] at *
  ring_nf
  field_simp [*, Real.log_ne_zero, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one, Real.log_ne_zero_of_pos_of_ne_one,
    Real.log_ne_zero_of_pos_of_ne_one] at *
  ring_nf

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [deriv_add, deriv_cos, deriv_log, deriv_pow, deriv_exp, deriv_id'', deriv_const',
    deriv_mul, mul_one, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, mul_assoc, mul_comm, mul_left_comm]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  simp_all [deriv_add, deriv_const', deriv_mul, deriv_exp, deriv_pow, deriv_log, deriv_sin,
    deriv_cos, deriv_id'', deriv_comp]
  field_simp
  ring
  <;> simp [h_div_ne_zero_14, h_log_ne_zero_4, h_log_ne_zero_17]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) (-Real.sin (Real.log x) * (1 / x)) x :=
    fun x hx =>
      have h₀ : HasDerivAt Real.log (1 / x) x := hasDerivAt_log hx
      have h₁ : HasDerivAt (fun x => Real.cos (Real.log x)) (-Real.sin (Real.log x) * (1 / x)) x :=
        h₀.cos.comp x (hasDerivAt_log hx)
      h₁
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => x ^ 3 * (Real.log x / Real.log (5:ℝ))) ((3 * x ^ 2 * (Real.log x / Real.log (5:ℝ))) + (x ^ 3 * ((1:ℝ) / x) * (1 / Real.log (5:ℝ)))) x :=
    fun x hx =>
      have h₁ : HasDerivAt (fun x => x ^ 3) (3 * x ^ 2) x := hasDerivAt_pow 3 x
      have h₂ : HasDerivAt (fun x => Real.log x / Real.log (5:ℝ)) ((1:ℝ) / x * (1 / Real.log (5:ℝ))) x :=
        have h₂ : HasDerivAt Real.log (1 / x) x := hasDerivAt_log hx
        h₂.div' (hasDerivAt_const x (Real.log (5:ℝ))) (by norm_num)
      h₁.mul h₂
  have h₂ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) (-Real.sin (Real.log x) * (1 / x)) x :=
    fun x hx => h₀ x hx
  simpa using h₀ 0 h_log_ne_zero_5

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.cos (Real.log x)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_add, deriv_cos, deriv_mul, deriv_const, deriv_log, one_mul, zero_add, zero_mul]
  field_simp [h_log_ne_zero_4, h_div_ne_zero_13, h_log_ne_zero_16]
  ring
  <;> simp_all
  <;> ring
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  have h₁ : Real.log 5 ≠ 0 := by linarith
  have h₂ : Real.log 5 ≠ 0 := by linarith
  have h₃ : Real.log 5 ≠ 0 := by linarith
  have h₄ : Real.log 5 ≠ 0 := by linarith
  have h₅ : Real.log 5 ≠ 0 := by linarith
  have h₆ : Real.log 5 ≠ 0 := by linarith
  have h₇ : Real.log 5 ≠ 0 := by linarith
  have h₈ : Real.log 5 ≠ 0 := by linarith
  have h₉ : Real.log 5 ≠ 0 := by linarith
  have h₁₀ : Real.log 5 ≠ 0 := by linarith
  field_simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16]
  ring_nf
  rw [add_comm]
  field_simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16]
  rw [add_comm]
  ring_nf
  <;> simp_all [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16]

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, mul_one, mul_div_assoc]
  apply congrArg
  ring
  <;> field_simp <;> ring
  <;> field_simp <;> ring
  <;> field_simp <;> ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h₁ : x ≠ 0 := by assumption
  have h₂ : (Real.log 5) ≠ 0 := by assumption
  have h₃ : (5:ℝ) ≠ 0 := by norm_num
  have h₄ : (5 * x + 2) ≠ 0 := by assumption
  field_simp [h₁, h₂, h₃, h₄, Real.log_mul, Real.log_rpow, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc, add_assoc, add_left_comm]
  ring_nf
  simp only [Real.cos_log, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  simp only [Real.log_inv, Real.log_rpow, mul_neg, mul_one, mul_add, mul_sub, mul_assoc, mul_comm,
    mul_left_comm, neg_mul, neg_neg]
  field_simp
  ring_nf
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_add]
  <;> simp_all [Real.deriv_cos, Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  <;> field_simp
  <;> linarith
  <;> ring
  <;> linarith
  <;> ring
  <;> linarith
  <;> ring
  <;> linarith
  <;> ring
  <;> linarith
  <;> ring
  <;> linarith
  <;> ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.sin (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))))) x = Real.cos (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
    intro x hx
    rw [deriv_sin (fun x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))]
    simp [Real.deriv_log, hx, Real.log_ne_zero_iff, Nat.cast_eq_zero, Nat.cast_ne_zero,
      ne_eq, Nat.cast_zero, false_or]
    ring
  exact h₁ x h_log_ne_zero_6

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (fun x ↦ Real.log x / Real.log (5:ℝ)) x = (1:ℝ) / (x * Real.log (5:ℝ)) := fun x hx ↦ by
    rw [deriv_div]
    · field_simp [Real.log_ne_zero_iff, hx, Real.log_ne_zero_iff]
    · exact differentiableAt_id'
    · exact differentiableAt_const _
  have h₂ : ∀ x : ℝ, deriv (fun x ↦ x ^ 3) x = (3:ℝ) * x ^ 2 := fun x ↦ by
    rw [deriv_pow]
    simp
  simp_all only [deriv_add, deriv_sub, deriv_sin, deriv_cos, deriv_log, deriv_id'', deriv_const']
  field_simp
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / Real.cos (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_div_ne_zero_14, h_log_ne_zero_17, Real.cos_ne_zero,
    Real.log_ne_zero, sub_eq_zero, pow_ne_zero]
  ring
  <;> simp [Real.cos_pi_div_two]
  <;> field_simp [Real.cos_pi_div_two]
  <;> ring
  <;> simp [Real.cos_pi_div_two]
  <;> field_simp [Real.cos_pi_div_two]
  <;> ring
  <;> simp [Real.cos_pi_div_two]
  <;> field_simp [Real.cos_pi_div_two]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  rw [deriv_exp]
  simp only [Real.exp_log, one_div, mul_div_cancel_left]
  field_simp
  ring_nf
  simp only [Real.exp_log]
  field_simp
  ring_nf
  <;> assumption
  <;> simp_all
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / (Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 → (Real.cos (Real.log x) - x ^ 3 * (Real.log x / Real.log 5)) ≠ 0 →
    deriv (fun x => Real.log (Real.cos (Real.log x) - x ^ 3 * (Real.log x / Real.log 5))) x =
      (-1 * Real.sin (Real.log x) * (1 / x) - ((3 * x ^ 2) * (Real.log x / Real.log 5) + (x ^ 3) * ((1 / x) * Real.log 5 / (Real.log 5 ^ 2)))) / (Real.cos (Real.log x) - x ^ 3 * (Real.log x / Real.log 5)) := by
    intro x h₁ h₂ h₃
    rw [deriv_log_of_cont_diffAt _ h₁ h₂ h₃]
    field_simp [*, Real.log_ne_zero_of_pos_of_ne_one, Real.log_pos, Real.cos_pos_of_mem_Ioo]
    ring_nf
    <;> simp_all only [ne_eq, one_div, mul_eq_mul_left_iff, mul_eq_mul_right_iff, mul_one, mul_zero, mul_neg, mul_assoc]
    <;> norm_num
    <;> linarith [Real.log_pos (by norm_num : (0 : ℝ) < 5)]
  simpa using h x h₀ h₁ h₂

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_sub]
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_const_mul]
  field_simp
  ring_nf
  <;> simp_all [Real.cos_zero, mul_zero, mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.exp

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x))) := by
  simp_all [Real.cos_log, Real.exp_log, Real.exp_ne_zero, mul_comm]
  field_simp [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow, h_log_ne_zero_4, h_div_ne_zero_14,
    h_log_ne_zero_17]
  ring
  <;> simp_all [Real.cos_log, Real.exp_log, Real.exp_ne_zero, mul_comm]
  <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow, h_log_ne_zero_4, h_div_ne_zero_14,
    h_log_ne_zero_17]
  <;> ring
  <;> simp_all [Real.cos_log, Real.exp_log, Real.exp_ne_zero, mul_comm]
  <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow, h_log_ne_zero_4, h_div_ne_zero_14,
    h_log_ne_zero_17]
  <;> ring
  <;> simp_all [Real.cos_log, Real.exp_log, Real.exp_ne_zero, mul_comm]
  <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow, h_log_ne_zero_4, h_div_ne_zero_14,
    h_log_ne_zero_17]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h1 : deriv (fun x => Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.cos (Real.log x)) x =
    deriv (fun x => Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x + deriv (fun x => Real.cos (Real.log x)) x := by
    apply deriv_add
  simp only [h1, deriv_add]
  ring_nf
  <;> simp [deriv_cos, deriv_log, deriv_id, deriv_pow, deriv_const, deriv_mul, deriv_pow, deriv_id,
    deriv_const, deriv_mul, deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_pow, deriv_id,
    deriv_const, deriv_mul, deriv_pow, deriv_id, deriv_const, deriv_mul]
  <;> field_simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_sub, deriv_sub, deriv_add, deriv_add]
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
    Real.log_exp]
  <;> ring_nf
  <;> apply DifferentiableAt.log <;>
    simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
      Real.log_exp]
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.const_add
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
    Real.log_exp]
  <;> ring_nf
  <;> apply DifferentiableAt.log <;>
    simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
      Real.log_exp]
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.const_add
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
    Real.log_exp]
  <;> ring_nf
  <;> apply DifferentiableAt.log <;>
    simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
      Real.log_exp]
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.const_add
  <;> simp [h_log_ne_zero_5, h_div_ne_zero_13, h_log_ne_zero_16, Real.log_ne_zero_iff, Nat.cast_eq_zero,
    Real.log_exp]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  rw [deriv_sub]
  · rw [deriv_cos]
    rw [deriv_pow]
    rw [deriv_mul]
    · rw [deriv_log]
      ring
    · norm_num
    norm_num
  · rw [deriv_mul]
    · rw [deriv_log]
      ring
    · norm_num
  all_goals norm_num

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  rw [deriv_sub, deriv_sub, deriv_sub]
  <;> field_simp
  <;> ring_nf
  <;> simp_all
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.rpow_const
  <;> norm_num
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.rpow_const
  <;> norm_num
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.rpow_const
  <;> norm_num
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.rpow_const
  <;> norm_num

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp only [deriv_sub, deriv_cos, deriv_log, deriv_mul, deriv_zpow, deriv_const, deriv_pow,
    deriv_add, deriv_id'', deriv_comp, deriv_exp, deriv_neg, deriv_id, deriv_zpow, deriv_const,
    deriv_pow, deriv_add, deriv_mul, deriv_id'', deriv_comp, deriv_exp, deriv_neg, deriv_id,
    deriv_zpow, deriv_const, deriv_pow, deriv_add, deriv_mul, deriv_id'', deriv_comp, deriv_exp,
    deriv_neg, deriv_id]
  field_simp [h_log_ne_zero_4, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  ring
  <;> simp_all
  <;> field_simp [h_log_ne_zero_4, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring
  <;> simp_all
  <;> field_simp [h_log_ne_zero_4, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring
  <;> simp_all
  <;> field_simp [h_log_ne_zero_4, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₀ : x ≠ 0 := by assumption
  have h₁ : Real.log 5 ≠ 0 := by norm_num
  have h₂ : (5 : ℝ) ≠ 0 := by norm_num
  field_simp [Real.log_ne_zero_iff, h₀, h₁, h₂, Real.log_ne_zero_iff, Real.log_ne_zero_iff]
  ring_nf
  simp only [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  field_simp
  linarith

example (x: ℝ)  (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₁ : x ≠ 0 := by assumption
  have h₂ : (5:ℝ) ≠ 0 := by norm_num
  have h₃ : Real.log ((5:ℝ)) ≠ 0 := by norm_num
  have h₄ : deriv (λ x ↦ Real.cos (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x =
    (-1:ℝ) * Real.sin (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
    simp [deriv_cos, deriv_mul, deriv_log, deriv_rpow_const, deriv_exp, deriv_id, deriv_pow,
      deriv_sin, deriv_const, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_inv, deriv_neg, deriv_id', deriv_comp, deriv_mul,
      deriv_div, deriv_pow, deriv_
example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp_all [Real.log_mul, Real.log_rpow, mul_assoc, mul_comm, mul_left_comm,
    Real.log_inv, Real.log_one, Real.log_zero, sub_eq_add_neg,
    Real.log_pow, add_assoc, add_comm, add_left_comm]
  field_simp [Real.cos_ne_zero, Real.log_ne_zero, Real.log_ne_zero,
    mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm, add_right_comm, mul_right_comm, mul_assoc,
    mul_comm, mul_left_comm, mul_right_comm, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm, mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  ring
  <;> apply Real.cos_ne_zero
  <;> apply Real.log_ne_zero
  <;> apply mul_assoc
  <;> apply mul_comm
  <;> apply mul_left_comm
  <;> apply mul_right_comm
  <;> apply add_assoc
  <;> apply add_comm
  <;> apply add_left_comm
  <;> apply add_right_comm
  <;> apply sub_eq_add_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg
  <;> apply pow_two
  <;> apply pow_three
  <;> apply pow_add
  <;> apply pow_one
  <;> apply pow_zero
  <;> apply pow_mul
  <;> apply pow_sub
  <;> apply pow_inv
  <;> apply pow_neg

example (x: ℝ)  (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_exp (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))]
  simp [Real.cos_log, Real.sin_log, mul_assoc, mul_comm, mul_left_comm, mul_add,
    mul_sub, mul_one, mul_div_assoc, mul_div_cancel_left]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := fun x hx ↦ by
    rintro rfl
    simp at hx
  have h2 : ∀ x : ℝ, x ≠ 0 → Real.cos x ≠ 0 := fun x hx ↦ by
    rintro rfl
    simp at hx
  field_simp [h_log_ne_zero_1, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17, h1, h2]
  ring
  <;>
  simp only [Real.log_one, mul_one, mul_zero, add_zero, mul_assoc]
  <;>
  simp only [mul_comm, mul_left_comm]
  <;>
  simp only [Real.log_inv, mul_inv, mul_neg, mul_one, neg_mul, neg_neg]
  <;>
  ring
  <;>
  simp only [Real.log_one, mul_one, mul_zero, add_zero, mul_assoc]
  <;>
  simp only [mul_comm, mul_left_comm]
  <;>
  simp only [Real.log_inv, mul_inv, mul_neg, mul_one, neg_mul, neg_neg]
  <;>
  ring

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  <;> simp [deriv_cos, deriv_exp, deriv_log, deriv_pow, deriv_id, deriv_const, mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> norm_num
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17, Real.log_ne_zero, ne_eq]
  ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17, Real.log_ne_zero, ne_eq]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17, Real.log_ne_zero, ne_eq]
  <;> ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17, Real.log_ne_zero, ne_eq]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_mul, deriv_const, deriv_id, deriv_pow, deriv_log,
    deriv_comp, mul_one, mul_zero, zero_add, add_zero, mul_neg, mul_assoc]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  ring
  <;> simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp [Real.cos_log, Real.sin_log]
  <;> ring
  <;> simp [Real.cos_log, Real.sin_log]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.cos (Real.log x)) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [Real.cos_log, mul_div_assoc, mul_assoc]
  rw [deriv_mul]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  rw [deriv_mul]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  rw [deriv_mul]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  ring
  <;> norm_num
  <;> simp_all
  <;> apply DifferentiableAt.mul <;> apply DifferentiableAt.const_mul <;> apply DifferentiableAt.log <;> apply DifferentiableAt.id <;> simp_all
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.id
  <;> simp_all
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.id
  <;> simp_all
  <;> apply DifferentiableAt.cos
  <;> apply DifferentiableAt.sin
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.rpow_const
  <;> apply DifferentiableAt.const_div
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.id
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [Real.cos_log, Real.sin_log, Real.cos_two_mul, Real.sin_two_mul, mul_one, mul_neg, mul_assoc]
  aesop
  <;> norm_num
  <;> apply Real.cos_log
  <;> apply Real.sin_log
  <;> apply Real.cos_two_mul
  <;> apply Real.sin_two_mul
  <;> simp only [mul_one, mul_neg, mul_assoc]
  <;> aesop
  <;> norm_num

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_mul]
  simp [h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_6]
  ring
  <;> simp_all only [Real.deriv_log, Real.deriv_cos, Real.deriv_sin, mul_neg, mul_one, mul_zero,
    mul_add, mul_sub, mul_assoc, sub_zero, mul_comm]
  <;> ring_nf
  <;> simp_all only [mul_assoc, mul_comm, mul_left_comm]
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg
  <;> apply mul_nonneg
  <;> apply mul_self_nonneg
  <;> apply mul_nonneg

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp [deriv_add, deriv_mul, deriv_comp, deriv_log, deriv_zpow₀, deriv_pow, deriv_inv,
    deriv_const, deriv_add, deriv_id, deriv_zpow₀, deriv_pow, deriv_inv, deriv_const,
    deriv_add, deriv_id, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm, mul_add, mul_sub]
  ring
  <;> field_simp
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.cos (Real.log x) * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20, Real.log_ne_zero_of_pos_of_ne_one]
  ring_nf
  simp only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20, Real.log_ne_zero_of_pos_of_ne_one]
  ring_nf
  <;> simp only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, mul_assoc, mul_left_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp [deriv_sin, deriv_cos, deriv_log, deriv_mul, deriv_div, deriv_pow, deriv_zpow]
  field_simp
  ring
  <;> assumption
  <;> simp
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₁ : x ≠ 0 := by
    intro h
    apply h_log_ne_zero_7
    simp [h]
  have h₂ : (x ^ 3 : ℝ) ≠ 0 := by
    intro h
    apply h_div_ne_zero_4
    simp [h]
  field_simp [h₁, h₂, h_log_ne_zero_7, h_div_ne_zero_4, h_log_ne_zero_17, h_div_ne_zero_14]
  ring_nf
  rw [Real.cos_div_three]
  norm_num
  field_simp [h₁, h₂, h_log_ne_zero_7, h_div_ne_zero_4, h_log_ne_zero_17, h_div_ne_zero_14]
  norm_num
  linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp only [deriv_tan_comp, deriv_cos_comp, deriv_log_div, deriv_const_div, deriv_pow_comp]
  field_simp
  ring_nf
  <;> assumption
  <;> apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
  <;> apply ne_of_gt <;> apply pow_pos <;> apply Real.exp_pos

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  apply HasDerivAt.deriv
  have h : ∀ x ≠ 0, HasDerivAt (fun y => Real.exp (Real.cos (Real.log y) / y ^ 3 * (Real.log y / Real.log 5)))
      (Real.exp (Real.cos (Real.log x) / x ^ 3 * (Real.log x / Real.log 5)) *
        (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) *
          (Real.log x / Real.log 5) +
          (Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log 5) / Real.log 5 ^ 2)))
    x := by
    intro x hx
    have h1 : HasDerivAt (fun y => Real.log y / Real.log 5) (1 / x / Real.log 5) x := by
      refine HasDerivAt.div ?_ ?_ ?_ <;> aesop
    have h2 : HasDerivAt (fun y => Real.cos (Real.log y) / y ^ 3)
        (1 / x * (-Real.sin (Real.log x)) / x ^ 3 - 3 * Real.cos (Real.log x) / x ^ 2) x := by
      refine HasDerivAt.div ?_ ?_ ?_ <;> aesop
    have h3 : HasDerivAt (fun y => Real.log y) (1 / x) x := by
      simpa using hasDerivAt_id x
    have h4 : HasDerivAt Real.exp (Real.exp (Real.log x / x ^ 3 * (Real.log x / Real.log 5)))
        (Real.log x / x ^ 3 * (Real.log x / Real.log 5)) := by
      simpa using hasDerivAt_exp _
    have h5 : HasDerivAt (fun y => Real.exp (Real.cos (Real.log y) / y ^ 3 * (Real.log y / Real.log 5)))
        (Real.exp (Real.cos (Real.log x) / x ^ 3 * (Real.log x / Real.log 5)) *
          (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) *
            (Real.log x / Real.log 5) +
            (Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log 5) / Real.log 5 ^ 2)))
      x := by
      refine HasDerivAt.comp x ?_ ?_ <;> aesop
    exact h5
  aesop

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  rw [deriv_log_cos_div_x3_logx_div_log5]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [div_eq_mul_inv]
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_div_ne_zero_3, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  <;>
  simp only [Real.exp_log, Real.cos_log, Real.sin_log, mul_one, mul_div_cancel_left]
  <;>
  simp [div_eq_mul_inv]
  <;>
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_div_ne_zero_3, mul_assoc, mul_comm, mul_left_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.exp_log, Real.cos_log, Real.sin_log, mul_one, mul_div_cancel_left]
  <;>
  simp [div_eq_mul_inv]
  <;>
  field_simp [h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_div_ne_zero_3, mul_assoc, mul_comm, mul_left_comm]
  <;>
  ring_nf

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_log_ne_zero_7: x ≠ 0) (h_div_ne_zero_14: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_17: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  rw [deriv_cos, deriv_mul, deriv_mul, deriv_mul, deriv_mul, deriv_mul, deriv_mul, deriv_mul, deriv_mul]
  field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17,
    mul_assoc, mul_comm, mul_left_comm]
  ring
  <;> simp [deriv_log, h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring
  <;> simp [deriv_log, h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring
  <;> simp [deriv_log, h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring
  <;> simp [deriv_log, h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring
  <;> simp [deriv_log, h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> field_simp [h_div_ne_zero_4, h_log_ne_zero_7, h_div_ne_zero_14, h_log_ne_zero_17]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [deriv_add, deriv_mul, deriv_const, deriv_log, deriv_pow, deriv_id, deriv_comp, deriv_inv, deriv_cos,
    mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  ring
  <;> simp_all only [inv_pow, inv_inv]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.cos (Real.log x)) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h₁ : x ≠ 0 := by
    intro h
    rw [h] at h_div_ne_zero_13
    simp at h_div_ne_zero_13
  have h₂ : x ^ 3 ≠ 0 := by
    intro h
    rw [h] at h_div_ne_zero_3
    simp at h_div_ne_zero_3
  have h₃ : Real.log 5 ≠ 0 := by
    intro h
    rw [h] at h_div_ne_zero_13
    simp at h_div_ne_zero_13
  field_simp [h₁, h₂, h₃, Real.log_ne_zero_iff, Nat.cast_eq_zero, Nat.cast_ne_zero]
  ring_nf
  simp only [Real.cos_log, Real.sin_log, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  field_simp
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  simp [deriv_div, deriv_mul, deriv_comp, deriv_pow, deriv_log, deriv_const, deriv_id,
    h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16,
    Real.log_ne_zero]
  ring_nf
  rw [← sub_eq_zero]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16,
    Real.log_ne_zero]
  ring_nf
  <;> simp [Real.cos_log, Real.sin_log, Real.cos_sq, Real.sin_sq, add_comm, sub_eq_add_neg]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16,
    Real.log_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp_all only [one_div, mul_div_cancel_left]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  ring_nf
  norm_cast
  <;> simp_all only [one_div, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all only [one_div, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all only [one_div, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  <;> ring_nf
  <;> norm_cast

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_div_ne_zero_13: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_16: (5:ℝ) ≠ 0) (h_log_ne_zero_20: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (x ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.cos (Real.log x) / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [add_assoc, add_left_comm, add_right_comm, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_6, h_div_ne_zero_13, h_log_ne_zero_16, h_log_ne_zero_20]
  ring_nf
  rw [Real.log_pow]
  rw [Real.log_mul]
  ring_nf
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.cos (Real.log x) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h₀ : x ≠ 0 := by assumption
  have h₁ : (5 * x + 2) ≠ 0 := by assumption
  have h₂ : HasDerivAt (fun x ↦ Real.log x) (1 / x) x := hasDerivAt_log h₀
  have h₃ : HasDerivAt (fun x ↦ Real.cos (Real.log x + (Real.log ((5 * x + 2)) ^ 3))) (-(Real.sin (Real.log x + (Real.log ((5 * x + 2)) ^ 3))) * (1 / x + 3 * Real.log ((5 * x + 2)) ^ 2 * (5 / (5 * x + 2)))) x := by
    apply HasDerivAt.comp
    · apply HasDerivAt.cos
      apply HasDerivAt.add
      · exact h₂.comp x (hasDerivAt_log h₀)
      · have h₄ : HasDerivAt (fun x ↦ (Real.log ((5 * x + 2)) ^ 3)) (3 * Real.log ((5 * x + 2)) ^ 2 * (5 / (5 * x + 2))) x := by
          apply HasDerivAt.comp
          · apply HasDerivAt.rpow
            exact hasDerivAt_const x 3
            exact hasDerivAt_log h₁
          · exact hasDerivAt_id' x
        exact h₄
    · exact hasDerivAt_id' x
  simp at h₃
  field_simp [h₀, h₁] at h₃ ⊢
  linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  rw [deriv_comp (fun x ↦ Real.cos (Real.log x + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) fun x ↦ Real.log x + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3]
  simp [deriv_cos, deriv_add, deriv_log, deriv_pow, h_log_ne_zero_6, h_log_ne_zero_10]
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / Real.cos (Real.cos (Real.log x) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  rw [deriv_tan_comp]
  <;> simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> ring_nf
  <;> norm_num
  <;> apply Real.cos_ne_zero_of_ne_zero_of_ne_pi <;> simp [h_tan_ne_zero_1]
  <;> simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> ring_nf
  <;> norm_num
  <;> apply Real.cos_ne_zero_of_ne_zero_of_ne_pi <;> simp [h_tan_ne_zero_1]
  <;> simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> ring_nf
  <;> norm_num
  <;> apply Real.cos_ne_zero_of_ne_zero_of_ne_pi <;> simp [h_tan_ne_zero_1]
  <;> simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_comm, add_left_comm]
  <;> ring_nf
  <;> norm_num
  <;> apply Real.cos_ne_zero_of_ne_zero_of_ne_pi <;> simp [h_tan_ne_zero_1]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.cos (Real.log x) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h₁ : deriv (fun x => Real.log x) x = 1 / x := by
    apply deriv_log
  have h₂ : deriv (fun x => (5 * x + 2) ^ 3) x = 3 * (5 * x + 2) ^ 2 * 5 := by
    apply deriv_zpow
  have h₃ : deriv (fun x => Real.cos (Real.log x) + Real.log ((5 * x + 2) ^ 3)) x = -Real.sin (Real.log x) * (1 / x) + 3 * Real.log ((5 * x + 2) ^ 3) * (5 / (5 * x + 2)) := by
    rw [deriv_add]
    · rw [deriv_cos, h₁]
      ring
    · rw [deriv_log, h₂]
      ring
  rw [deriv_exp, h₃]
  ring

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / (Real.cos (Real.log x) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h₀ : ∀ x : ℝ, x ≠ 0 → x.log ≠ 0 := fun x hx ↦ ne_of_ne_of_eq hx (Real.log_one.symm)
  have h₁ : ∀ x : ℝ, x ≠ 0 → (5 * x + 2) ≠ 0 := fun x hx ↦ ne_of_ne_of_eq hx (by norm_num)
  have h₂ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₃ : ∀ x : ℝ, x ≠ 0 → (5 * x + 2) ≠ 0 := fun x hx ↦ ne_of_ne_of_eq hx (by norm_num)
  have h₄ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₅ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₆ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₇ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₈ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₉ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₀ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₁ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₂ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₃ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₄ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₅ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₆ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₇ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₈ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₁₉ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  have h₂₀ : ∀ x : ℝ, x ≠ 0 → (cos (log x) + (log (5 * x + 2)) ^ 3) ≠ 0 := fun x hx ↦
    ne_of_ne_of_eq (h₀ x hx) (by norm_num)
  simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, hx, hlog_ne_zero_1, hlog_ne_zero_6, hlog_ne_zero_10]
  field_simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, hx, hlog_ne_zero_1, hlog_ne_zero_6, hlog_ne_zero_10]
  ring_nf
  norm_num
  field_simp [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h
example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  have h1 : deriv (fun x => Real.cos (Real.log x)) x = -Real.sin (Real.log x) * (1 / x) := by
    rw [deriv_cos, deriv_log, neg_one_mul]
    ring
  have h2 : deriv (fun x => (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
    rw [deriv_rpow_const, deriv_log]
    ring
    linarith
  have h3 : deriv (fun x => Real.exp x * (x ^ 2 + (3:ℝ))) x = Real.exp x * (x ^ 2 + (3:ℝ)) + Real.exp x * ((2:ℝ) * x) := by
    rw [deriv_mul, deriv_exp, deriv_pow, deriv_const]
    ring
    linarith
  linarith [h1, h2, h3]

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [one_div, mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_4, h_log_ne_zero_10]
  ring
  <;> aesop
  <;> aesop
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [deriv_add, deriv_cos, deriv_log, deriv_pow, deriv_id'', deriv_const, pow_one,
    mul_one, mul_zero, add_zero, zero_add, mul_neg, mul_assoc, mul_comm]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [deriv_add]
  <;> simp [deriv_cos, deriv_log, deriv_pow, deriv_id, h_log_ne_zero_4, h_log_ne_zero_9]
  <;> field_simp
  <;> ring
  <;> simp [Real.cos_log]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.cos (Real.log x)) (-(1 / x) * Real.sin (Real.log x)) x := by
    intro x hx
    have h := hasDerivAt_log hx
    have h2 := hasDerivAt_cos (Real.log x)
    have h3 := hasDerivAt_comp (fun x => Real.cos x) h
    simp only [Function.comp_apply, Real.cos_log] at h3
    convert h3 using 1
    field_simp
  have h2 : ∀ x : ℝ, ((5:ℝ) * x + (2:ℝ)) ≠ 0 → HasDerivAt (fun x => (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) x := by
    intro x hx
    have h := hasDerivAt_log hx
    have h2 := hasDerivAt_pow 3 (Real.log ((5:ℝ) * x + (2:ℝ)))
    have h3 := hasDerivAt_comp (fun x => x ^ 3) h
    simp only [Function.comp_apply, Real.log_pow] at h3
    convert h3 using 1
    field_simp
  have h3 : ∀ x : ℝ, HasDerivAt (fun x => (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
    intro x
    have h := hasDerivAt_sin ((2:ℝ) * x - (1:ℝ))
    have h2 := hasDerivAt_pow 2 (Real.sin ((2:ℝ) * x - (1:ℝ)))
    have h3 := hasDerivAt_comp (fun x => x ^ 2) h
    simp only [Function.comp_apply, Real.sin_sq] at h3
    convert h3 using 1
    ring
  simp only [add_assoc, add_right_comm, add_left_comm, add_comm]
  aesop
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [deriv_add]
  <;> simp_all [deriv_log, deriv_cos, deriv_sin, deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_id, mul_comm]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [deriv_add, deriv_cos, deriv_log, deriv_pow, deriv_const, deriv_mul, deriv_id, deriv_div,
    deriv_inv, deriv_zpow, deriv_comp, deriv_neg, deriv_sub]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  <;> simp [Real.deriv_cos, deriv_zpow', deriv_log, mul_assoc, mul_comm, mul_left_comm,
    Real.deriv_log, Real.deriv_id'', mul_one, mul_zero, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring
  <;> norm_num
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.zpow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.zpow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.zpow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.zpow
  <;> apply DifferentiableAt.log

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.cos (Real.log x) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp [deriv_sin, deriv_cos, deriv_sub, deriv_log, deriv_pow]
  ring_nf
  field_simp [h_log_ne_zero_6, h_log_ne_zero_10]
  linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_cos]
  simp only [deriv_sub, deriv_cos, neg_mul, mul_neg, mul_one, neg_neg, mul_assoc]
  field_simp [h_log_ne_zero_6, h_log_ne_zero_10]
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / Real.cos (Real.cos (Real.log x) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  simp only [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  <;> ring_nf
  <;> simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.cos (Real.log x) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [deriv_exp, deriv_sub, deriv_log, deriv_pow, deriv_const, deriv_add, deriv_mul,
    deriv_id'', deriv_cos, deriv_pow, deriv_zpow, deriv_comp, deriv_zpow, deriv_id'', deriv_zpow]
  field_simp [h_log_ne_zero_6, h_log_ne_zero_10]
  ring_nf
  <;> simp_all
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.cos (Real.log x) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  simp only [deriv_log', comp_apply, one_div, mul_one]
  field_simp [sub_ne_zero, h_log_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10, mul_comm]
  ring
  <;> simp [Real.log, Real.cos, Real.sin, Real.tan, Real.exp, mul_assoc, mul_comm, mul_left_comm]
  <;> norm_num

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add, deriv_add, deriv_add, deriv_neg, deriv_cos, deriv_log,
    deriv_pow, deriv_exp, deriv_add, deriv_add, deriv_id'', deriv_const'] <;>
  simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;>
  field_simp
  <;>
  ring_nf

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x))) := by
  field_simp [h_log_ne_zero_4, h_log_ne_zero_10, Real.cos_log, Real.exp_log,
    mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  <;> simp [Real.cos_log, Real.exp_log, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [Real.cos_log, Real.log_cos, mul_add, mul_comm, mul_left_comm, mul_assoc,
    add_assoc, add_left_comm, sub_eq_add_neg, add_right_comm, neg_add_rev, neg_neg, neg_mul,
    neg_sub, neg_neg, neg_zero, mul_zero, add_zero, mul_one, zero_mul, mul_neg, neg_mul,
    neg_sub, neg_neg, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> simp only [mul_assoc]
  <;> ring_nf
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp [deriv_sub, deriv_cos, deriv_log, deriv_pow, deriv_const, deriv_id, mul_comm]
  field_simp
  ring
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [deriv_add, deriv_sub, deriv_const, deriv_cos, deriv_log, deriv_sin, deriv_id'',
    deriv_pow, deriv_mul_const, deriv_mul_comp, deriv_comp, deriv_X, deriv_one, deriv_zero,
    deriv_neg, deriv_mul, deriv_add_const, deriv_add_const', deriv_add_const'',
    deriv_mul_inv_comp, deriv_mul_inv_comp', deriv_mul_inv_comp'', deriv_mul_inv_comp''',
    deriv_mul_inv_comp'''', deriv_mul_inv_comp''''', deriv_mul_inv_comp'''''',
    deriv_mul_inv_comp''''''', deriv_mul_inv_comp'''''''', deriv_mul_inv_comp'''''''''
  ]
  field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  ring

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp_all only [deriv_sub, deriv_cos, deriv_log, deriv_zpow, deriv_id'', deriv_const',
    sub_zero, zero_mul, zero_sub, mul_zero, zero_add, mul_one, sub_neg_eq_add, neg_zero]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [mul_comm, mul_one, mul_div_cancel_left]
  field_simp
  ring_nf
  rw [← sub_eq_zero]
  field_simp
  linarith

example (x: ℝ)  (h_log_ne_zero_4: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  rw [Real.log_div]
  ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> ring_nf
  <;> simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_4, h_log_ne_zero_10, h_div_ne_zero_23, h_log_ne_zero_26,
    Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  have h1 : ∀ x, x ≠ 0 → deriv (fun y => Real.sin (Real.cos (Real.log y) * Real.log y ^ 3)) x =
      Real.cos (Real.cos (Real.log x) * Real.log x ^ 3) *
        (((-1:ℝ) * Real.sin (Real.log x) * (1 / x)) * Real.log x ^ 3 +
          Real.cos (Real.log x) * (3 * Real.log x ^ 2 * (1 / x))) := by
    intro x hx
    rw [deriv_sin]
    field_simp [Real.cos_log, hx, Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
    ring
  have h2 : ∀ x, x ≠ 0 → deriv (fun y => Real.sin (Real.cos (Real.log y) * Real.log y ^ 3)) x =
      Real.cos (Real.cos (Real.log x) * Real.log x ^ 3) *
        (((-1:ℝ) * Real.sin (Real.log x) * (1 / x)) * Real.log x ^ 3 +
          Real.cos (Real.log x) * (3 * Real.log x ^ 2 * (1 / x))) := by
    intro x hx
    rw [deriv_sin]
    field_simp [Real.cos_log, hx, Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
    ring
  have h3 : ∀ x, x ≠ 0 → deriv (fun y => Real.sin (Real.cos (Real.log y) * Real.log y ^ 3)) x =
      Real.cos (Real.cos (Real.log x) * Real.log x ^ 3) *
        (((-1:ℝ) * Real.sin (Real.log x) * (1 / x)) * Real.log x ^ 3 +
          Real.cos (Real.log x) * (3 * Real.log x ^ 2 * (1 / x))) := by
    intro x hx
    rw [deriv_sin]
    field_simp [Real.cos_log, hx, Real.log_ne_zero, mul_assoc, mul_comm, mul_left_comm]
    ring
  simpa using h1 x h_log_ne_zero_6

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  rw [Real.cos_le_iff_le_sin, mul_comm]
  refine' le_of_not_lt fun h => _
  linarith [h, Real.sin_le_one (Real.log x), Real.sin_le_one (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)]

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / Real.cos (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  simp only [deriv_tan, cos_sq, mul_pow, mul_assoc]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10]
  ring
  <;> simp only [Real.log_pow, Real.log_mul, Real.log_one, mul_one, mul_zero, add_zero,
    mul_add, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10]
  <;> ring_nf
  <;> simp only [Real.log_pow, Real.log_mul, Real.log_one, mul_one, mul_zero, add_zero,
    mul_add, mul_comm, mul_left_comm]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_6, h_log_ne_zero_10]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  rw [deriv_exp]
  simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  field_simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  ring_nf
  <;> simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> field_simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> ring_nf
  <;> simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> field_simp [*, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_right_comm]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  simp only [Real.log_mul, Real.log_pow, mul_add, mul_one, mul_assoc]
  have h₁ : ∀ x : ℝ, cos (log x) ≠ 0 := by
    intro x
    apply cos_ne_zero_of_mem_Ioo
    exact ⟨by linarith [exp_pos x], by linarith [exp_pos x]⟩
  have h₂ : ∀ x : ℝ, log ((5 * x + 2) ^ 3) ≠ 0 := by
    intro x
    apply log_ne_zero_of_pos_of_ne_one
    · nlinarith [sq_nonneg (5 * x + 2)]
    · nlinarith [sq_nonneg (5 * x + 2)]
  field_simp [h₁, h₂, Real.log_mul, Real.log_pow, mul_add, mul_one, mul_assoc]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_add]
  <;> rw [deriv_add]
  <;> rw [deriv_mul]
  <;> rw [deriv_comp]
  <;> simp [deriv_exp, deriv_pow, deriv_log, deriv_id, deriv_const, mul_one, mul_zero, add_zero, zero_add, mul_add, mul_comm, mul_left_comm, mul_assoc]
  <;> ring
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.exp x) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [add_mul, mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_assoc]
  field_simp [h_log_ne_zero_6, h_log_ne_zero_10, Real.exp_ne_zero]
  ring_nf
  <;> simp only [Real.exp_log, mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_assoc]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, Real.exp_ne_zero]
  <;> ring_nf
  <;> simp only [Real.exp_log, mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_assoc]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, Real.exp_ne_zero]
  <;> ring_nf
  <;> simp only [Real.exp_log, mul_assoc, mul_comm, mul_left_comm, mul_right_comm, mul_assoc]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_10, Real.exp_ne_zero]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [add_assoc, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  rw [← add_assoc]
  ring
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  <;> ring_nf
  <;> simp_all [Real.cos_log, Real.sin_log, Real.log_mul, Real.log_pow, Real.log_inv]

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  rw [deriv_mul]
  simp only [Real.deriv_cos, Real.deriv_log, mul_one, mul_zero, add_zero, zero_add, mul_neg, mul_assoc]
  field_simp [h_log_ne_zero_5, h_log_ne_zero_9]
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add] <;>
  (try
    rw [deriv_mul] <;>
    first
      | rw [deriv_const_mul] |
        rw [deriv_const_mul]) <;>
  (try
    rw [deriv_pow] <;>
    first
      | rw [deriv_id] |
        rw [deriv_id]) <;>
  (try
    rw [deriv_add] <;>
    first
      | rw [deriv_const_add] |
        rw [deriv_const_add]) <;>
  (try
    rw [deriv_sub] <;>
    first
      | rw [deriv_const_sub] |
        rw [deriv_const_sub]) <;>
  (try
    rw [deriv_neg] <;>
    first
      | rw [deriv_id] |
        rw [deriv_id]) <;>
  (try
    rw [deriv_log] <;>
    first
      | rw [deriv_id] |
        rw [deriv_id]) <;>
  (try
    rw [deriv_exp] <;>
    first
      | rw [deriv_id] |
        rw [deriv_id]) <;>
  ring
  <;> simp_all
  <;> ring_nf
  <;> field_simp
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h1 : deriv (fun x => Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x =
    (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) +
        (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) *
        (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) +
      (Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) *
        ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
    rw [deriv_mul (fun x => Real.cos (Real.log x)) (fun x => (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)]
    simp [deriv_cos, deriv_log, deriv_pow, deriv_mul, deriv_add, deriv_const, deriv_mul, deriv_sin, deriv_sub,
      deriv_const]
    ring
  rw [h1]

example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_add]
  <;> simp [deriv_mul, deriv_const, deriv_log, deriv_comp, deriv_id, deriv_pow, h_log_ne_zero_5, h_log_ne_zero_9, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> field_simp [h_log_ne_zero_5, h_log_ne_zero_9, h_div_ne_zero_23, h_log_ne_zero_26]
  <;> ring_nf
  <;> norm_num
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.comp
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.comp
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.const
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.comp
  <;> apply DifferentiableAt.pow

example (x: ℝ)  (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (x ^ 3)) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_mul] <;> field_simp [h_log_ne_zero_26, h_log_ne_zero_6, h_log_ne_zero_10, Real.log_ne_zero]
  ring_nf <;>
  simp only [mul_pow, mul_assoc] <;>
  ring_nf <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm] <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf
  <;>
  simp only [Real.cos_log, Real.sin_log, mul_add, mul_sub, mul_one, mul_div_assoc, mul_comm]
  <;>
  ring_nf

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  have h_log_ne_zero_1 : Real.log x ≠ 0 := by
    apply ne_of_gt
    apply lt_of_le_of_lt (Real.log_nonpos (by norm_num) (by linarith))
    norm_num
  have h_log_ne_zero_2 : Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 ≠ 0 := by
    apply ne_of_gt
    apply lt_of_le_of_lt (Real.log_nonpos (by norm_num) (by linarith))
    norm_num
  field_simp [h_log_ne_zero_1, h_log_ne_zero_2]
  ring
  <;> simp [Real.deriv_log, Real.deriv_sin, Real.deriv_cos, h_log_ne_zero_1, h_log_ne_zero_2, h_div_ne_zero_3, h_log_ne_zero_6, h_log_ne_zero_10]
  <;> field_simp [h_log_ne_zero_1, h_log_ne_zero_2]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  apply HasDerivAt.deriv
  have h1 : HasDerivAt (fun x => Real.cos (Real.log x)) (-((Real.sin (Real.log x)) * (1 / x))) x := by
    have h1 : HasDerivAt Real.log (1 / x) x := by
      apply hasDerivAt_log
      linarith
    have h2 : HasDerivAt (fun x => Real.cos (Real.log x)) (-Real.sin (Real.log x) * (1 / x)) x := by
      apply HasDerivAt.cos
      exact h1
    exact h2
  have h2 : HasDerivAt (fun x => Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) (3 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) x := by
    have h2 : HasDerivAt (fun x => Real.log ((5:ℝ) * x + (2:ℝ))) (5 / ((5:ℝ) * x + (2:ℝ))) x := by
      apply hasDerivAt_log
      linarith
    have h3 : HasDerivAt (fun x => Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) (3 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) x := by
      apply HasDerivAt.pow
      exact h2
    exact h3
  have h3 : HasDerivAt (fun x => Real.cos (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) (-1 * Real.sin (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    apply HasDerivAt.cos
    apply HasDerivAt.div h1 h2
    linarith
  have h4 : HasDerivAt (fun x => Real.cos (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) (-1 * Real.sin (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    apply HasDerivAt.cos
    apply HasDerivAt.div h1 h2
    linarith
  have h5 : HasDerivAt (fun x => Real.cos (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) (-1 * Real.sin (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    apply HasDerivAt.cos
    apply HasDerivAt.div h1 h2
    linarith
  have h6 : HasDerivAt (fun x => Real.cos (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) (-1 * Real.sin (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    apply HasDerivAt.cos
    apply HasDerivAt.div h1 h2
    linarith
  have h7 : HasDerivAt (fun x => Real.cos (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) (-1 * Real.sin (Real.log x / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) x := by
    apply HasDerivAt.cos
    apply HasDerivAt.div h1 h2
    linarith
  exact h7

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / Real.cos (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h : (fun x ↦ Real.tan (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) = (fun x ↦ Real.tan (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) := by
    ext x
    congr 2
    congr 2
    rw [Real.log_rpow]
    linarith [Real.log_one]
  rw [h]
  rw [deriv_tan_comp]
  field_simp
  ring
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  apply congrArg
  ring
  <;> apply congr_arg
  <;> field_simp <;> ring_nf <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: (Real.cos ((Real.log (x))) / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log (Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / (Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h : ∀ x ≠ 0, x⁻¹ * Real.log x ≠ 0 := by
    intro x hx
    exact mul_ne_zero (inv_ne_zero hx) (log_ne_zero_of_pos_of_ne_one (by positivity) hx)
  simp only [deriv_log_cos, deriv_log_div, deriv_log_comp, deriv_const_div, deriv_pow, deriv_add,
    deriv_mul, deriv_const, deriv_id, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_id]
  field_simp [h x h_log_ne_zero_6, h_log_ne_zero_1, h_div_ne_zero_3]
  ring
  <;> simp_all
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  have h₀ : ∀ x ≠ 0, deriv (fun x => Real.log x) x = 1 / x := fun x hx => deriv_log x hx
  have h₁ : deriv (fun x => x ^ 2) x = 2 * x := by rw [deriv_pow]; simp
  have h₂ : deriv (fun x => Real.exp x) x = Real.exp x := by simp [deriv_exp]
  have h₃ : deriv (fun x => x ^ 3) x = 3 * x ^ 2 := by rw [deriv_pow]; simp
  have h₄ : deriv (fun x => Real.log (x ^ 2)) x = 2 / x := by
    rw [deriv_log]
    · field_simp
      ring
    · simp
  have h₅ : deriv (fun x => Real.log (x ^ 3)) x = 3 / x := by
    rw [deriv_log]
    · field_simp
      ring
    · simp
  have h₆ : deriv (fun x => Real.log (x ^ 4)) x = 4 / x := by
    rw [deriv_log]
    · field_simp
      ring
    · simp
  have h₇ : deriv (fun x => Real.log (x ^ 5)) x = 5 / x := by
    rw [deriv_log]
    · field_simp
      ring
    · simp
  have h₈ : deriv (fun x => x ^ 4) x = 4 * x ^ 3 := by rw [deriv_pow]; simp
  have h₉ : deriv (fun x => x ^ 5) x = 5 * x ^ 4 := by rw [deriv_pow]; simp
  simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_id, deriv_pow, deriv_exp,
    deriv_log, deriv_inv, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h_log_ne_zero_5, h_log_ne_zero_9]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.exp x) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  rw [deriv_div]
  <;> simp_all [mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
  <;> field_simp
  <;> ring
  <;> norm_num
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  apply Eq.symm
  apply Eq.symm
  apply Eq.symm
  rw [add_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_5, h_log_ne_zero_9, Real.log_mul, Real.log_rpow,
    mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg]
  ring
  <;> apply isOpen_Ioi
  <;> apply Continuous.continuousOn
  <;> apply Continuous.comp <;> apply continuous_log <;>
    apply Continuous.add
  <;> apply Continuous.mul
  <;> apply Continuous.const
  <;> apply Continuous.id

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.cos (Real.log x)) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm, mul_one, mul_right_comm,
    mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num), Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num),
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)]
  ring_nf
  <;> simp only [Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num), Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num),
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, sub_sub_sub_cancel_right,
    mul_div_cancel_left]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_5, h_log_ne_zero_9]
  ring
  <;> simp [*, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  rw [deriv_mul]
  field_simp
  ring_nf
  <;> apply h_log_ne_zero_5
  <;> apply h_log_ne_zero_9
  <;> apply h_div_ne_zero_2
  <;> norm_num
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_9: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  have h₁ : x ≠ 0 := by
    intro H
    apply h_log_ne_zero_5
    simp [H]
  have h₂ : (5 * x + 2) ≠ 0 := by
    intro H
    apply h_log_ne_zero_9
    simp [H]
  have h₃ : Real.log 5 ≠ 0 := by
    intro H
    apply h_div_ne_zero_23
    simp [H]
  have h₄ : Real.log (5 * x + 2) ≠ 0 := by
    intro H
    apply h_div_ne_zero_2
    simp [H]
  simp [deriv_add, deriv_mul, deriv_const, deriv_log, deriv_pow, h₁, h₂, h₃, h₄,
    mul_assoc, mul_comm, mul_left_comm]
  field_simp [h₁, h₂, h₃, h₄, sub_ne_zero]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_6: x ≠ 0) (h_log_ne_zero_10: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_23: Real.log ((5:ℝ)) ≠ 0)  (h_log_ne_zero_26: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - Real.cos (Real.log x) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (x ^ 3)) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.cos (Real.log x) / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [one_div, mul_one, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  ring_nf
  <;> simp only [one_div, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  <;> ring_nf
  <;> simp only [one_div, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  <;> ring_nf
  <;> simp only [one_div, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  <;> ring_nf
  <;> simp only [one_div, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  <;> ring_nf
  <;> simp only [one_div, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_6, h_log_ne_zero_26, h_div_ne_zero_23, h_div_ne_zero_3, h_log_ne_zero_10]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_sin]
  field_simp [h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  <;> simp only [Real.cos_sin_cancel]
  <;> simp only [mul_one, mul_zero, sub_zero, zero_add, add_zero]
  <;> ring_nf
  <;> simp only [Real.cos_sin_cancel]
  <;> simp only [mul_one, mul_zero, sub_zero, zero_add, add_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₁ : x ≠ 0 := by assumption
  have h₂ : Real.log 5 ≠ 0 := by assumption
  have h₃ : (5:ℝ) ≠ 0 := by norm_num
  have h₄ : (2:ℝ) ≠ 0 := by norm_num
  have h₅ : (1:ℝ) ≠ 0 := by norm_num
  field_simp [h₁, h₂, h₃, h₄, h₅, Real.log_ne_zero_iff]
  simp only [mul_add, mul_sub, mul_one, mul_comm, mul_left_comm, mul_right_comm]
  ring_nf
  simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub, mul_add, mul_sub, mul_one, mul_comm, mul_left_comm, mul_right_comm]
  field_simp [h₁, h₂, h₃, h₄, h₅, Real.log_ne_zero_iff]
  linarith [h₁, h₂, h₃, h₄, h₅]

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  have h₁ : deriv (fun x => Real.tan (y + z * x)) x = z * (1 / Real.cos (y + z * x) ^ 2) := by
    apply deriv_tan
  have h₂ : deriv (fun x => Real.tan (y + z * x)) x = z * (1 / Real.cos (y + z * x) ^ 2) := by
    apply deriv_tan
  have h₃ : deriv (fun x => Real.tan (y + z * x)) x = z * (1 / Real.cos (y + z * x) ^ 2) := by
    apply deriv_tan
  have h₄ : deriv (fun x => Real.tan (y + z * x)) x = z * (1 / Real.cos (y + z * x) ^ 2) := by
    apply deriv_tan
  have h₅ : deriv (fun x => Real.tan (y + z * x)) x = z * (1 / Real.cos (y + z * x) ^ 2) := by
    apply deriv_tan
  simp_all

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  rw [deriv_exp (f := fun x => (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2))]
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_rpow_const]
  rw [deriv_log]
  ring
  all_goals assumption

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 + (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h1 : (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) =ᶠ[𝓝 x] (fun x ↦ Real.log (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
    filter_upwards [eventually_ne_nhds (0 : ℝ)] with x hx
    rw [← Real.log_rpow hx]
    congr
    ring
  have h2 : deriv (fun x ↦ Real.log (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x =
    ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
    simp [Real.log_rpow]
    field_simp
    ring
  rw [deriv_congr_of_eventuallyEq h1 h2]

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [pow_two]
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  ring_nf
  norm_num
  <;> simp only [Real.exp_log, Real.exp_sub, mul_div_assoc, mul_div_cancel_left]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → x ^ 2 ≠ 0 := fun x hx ↦ pow_ne_zero 2 hx
  have h₂ : ∀ x : ℝ, x ≠ 0 → x ^ 3 ≠ 0 := fun x hx ↦ pow_ne_zero 3 hx
  have h₃ : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := fun x hx ↦ Real.log_ne_zero_of_pos_of_ne_one (hx.symm ▸ zero_lt_one) hx
  have h₄ : ∀ x : ℝ, x ≠ 0 → Real.log 5 ≠ 0 := fun x hx ↦ Real.log_ne_zero_of_pos_of_ne_one zero_lt_five (by norm_num)
  have h₅ : ∀ x : ℝ, x ≠ 0 → Real.exp x ≠ 0 := fun x hx ↦ Real.exp_ne_zero x
  field_simp [h₁, h₂, h₃, h₄, h₅]
  ring
  <;> simp only [Real.sin_two_mul, Real.cos_two_mul, Real.sin_sub, Real.cos_sub, mul_assoc, mul_comm, mul_left_comm]
  <;> ring
  <;> simp only [Real.sin_sq, Real.cos_sq, Real.sin_add, Real.cos_add, mul_assoc, mul_comm, mul_left_comm]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add] <;> simp [deriv_add, deriv_sin, deriv_pow, deriv_mul, deriv_id, deriv_const,
    deriv_log, Real.log_mul, Real.log_rpow] <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  ring_nf
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> simp only [add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> simp only [add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := fun x hx ↦ by simp [Real.log_eq_zero, hx]
  have h₂ : ∀ x : ℝ, (5:ℝ) * x + (2:ℝ) ≠ 0 → Real.log ((5:ℝ) * x + (2:ℝ)) ≠ 0 := fun x hx ↦ by simp [Real.log_eq_zero, hx]
  have h₃ : ∀ x : ℝ, x ≠ 0 → Real.log (5:ℝ) ≠ 0 := fun x hx ↦ by simp [Real.log_eq_zero, hx]
  have h₄ : ∀ x : ℝ, (5:ℝ) * x + (2:ℝ) ≠ 0 → Real.sqrt ((5:ℝ) * x + (2:ℝ)) ≠ 0 := fun x hx ↦ by simp [Real.sqrt_eq_zero, hx]
  field_simp [*, sub_eq_zero, sin_eq_zero_iff] at *
  ring_nf
  field_simp [*, sub_eq_zero, sin_eq_zero_iff] at *
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [pow_three, mul_neg, mul_one, mul_zero, mul_add, mul_assoc, mul_comm, mul_left_comm,
    add_assoc, add_left_comm, add_comm, add_zero, mul_right_comm]
  field_simp [h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26, Real.log_ne_zero,
    Real.log_ne_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at *
  ring_nf
  apply Eq.symm
  rw [Real.log_div]
  field_simp
  rw [Real.log_mul]
  field_simp
  rw [Real.log_rpow]
  field_simp
  ring_nf
  <;> apply Eq.symm
  <;> apply Eq.symm
  <;> apply Eq.symm

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  simp [deriv_sin, deriv_cos, deriv_pow, deriv_sub, deriv_mul, deriv_log, deriv_pow, deriv_id,
    mul_sub_left_distrib, mul_sub_right_distrib, mul_add, sub_add_eq_sub_sub,
    mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm, sub_sub, sub_right_comm]
  ring
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring
  <;> simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  <;> ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  have := h_tan_ne_zero_1
  have := h_div_ne_zero_20
  have := h_log_ne_zero_21
  have := h_log_ne_zero_23
  field_simp [Real.tan_eq_sin_div_cos, Real.log_ne_zero_iff]
  ring_nf
  rw [Real.deriv_tan]
  field_simp [Real.tan_eq_sin_div_cos, Real.log_ne_zero_iff]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) := by
  simp [deriv_exp]
  field_simp [h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  <;> simp only [mul_sub, mul_one, mul_add, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm, neg_mul, neg_neg, neg_add]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul,
    Real.sin_sub, Real.cos_sub, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_neg, Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]
  <;> simp only [Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.sin_neg,
    Real.cos_neg, neg_neg, neg_add]
  <;> simp only [Real.sin_zero, Real.cos_zero, mul_one, mul_neg, neg_neg, mul_zero, add_zero,
    zero_add, sub_zero]
  <;> simp only [Real.sin_eq_sin_iff, Real.cos_eq_cos_iff]

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 - (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h₁ : (λ x => Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) =ᶠ[𝓝 x]
    fun x => Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := eventually_of_forall fun x => rfl
  rw [deriv_congr_of_eventuallyEq h₁]
  simp only [deriv_log', deriv_sub, deriv_pow'', deriv_sin, deriv_mul, deriv_const', deriv_id'', deriv_log_of_pos
    (show (0:ℝ) < (5:ℝ) by norm_num), mul_one, sub_zero, zero_sub, mul_neg, mul_one, neg_neg]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [show (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) = (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) by rfl]
  apply congrArg
  ext x
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  ring_nf
  <;> simp_all [Real.sin_two_mul, Real.cos_two_mul, Real.exp_add, Real.exp_sub, Real.exp_mul, Real.exp_pow]
  <;> simp_all [Real.log_mul, Real.log_div, Real.log_pow]
  <;> simp_all [Real.log_exp]
  <;> simp_all [Real.exp_log]
  <;> simp_all [Real.exp_log]
  <;> simp_all [Real.exp_log]
  <;> simp_all [Real.exp_log]

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x))) := by
  rw [show (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) =
      (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * Real.log x * (Real.exp x) * (x ^ 2 + (3:ℝ)) / Real.log (5:ℝ))) by
    ext x
    field_simp [h_log_ne_zero_21, h_log_ne_zero_23]
    ring_nf]
  simp only [deriv_sub, deriv_pow, deriv_mul, deriv_const, deriv_add, deriv_id'', deriv_exp, deriv_log,
    deriv_sin, deriv_cos, deriv_sub, deriv_pow, deriv_mul, deriv_const, deriv_add, deriv_id'',
    deriv_exp, deriv_log, deriv_sin, deriv_cos]
  field_simp [h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, deriv_add]
  ring
  <;> simp_all [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, deriv_add]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, deriv_add]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp [deriv_sub, deriv_mul, deriv_pow, deriv_comp, deriv_sin, deriv_id, deriv_log, h_div_ne_zero_19,
    h_log_ne_zero_20, h_log_ne_zero_22, sq, mul_add, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  ring
  <;> field_simp
  <;> simp [h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  <;> ring
  <;> field_simp
  <;> simp [h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  <;> ring
  <;> field_simp
  <;> simp [h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  <;> ring
  <;> field_simp
  <;> simp [h_log_ne_zero_20, h_log_ne_zero_22, mul_assoc]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h₁ : deriv (fun x => (Real.sin (2 * x - 1)) ^ 2 - x ^ 3 * (Real.log x / Real.log 5) + Real.log (5 * x + 2) ^ 3) x =
      deriv (fun x => (Real.sin (2 * x - 1)) ^ 2 - x ^ 3 * (Real.log x / Real.log 5) + Real.log (5 * x + 2) ^ 3) x := rfl
  rw [h₁]
  apply congrArg
  ring_nf
  <;> simp [*, Nat.cast_nonneg]
  <;> field_simp
  <;> linarith
  <;> ring_nf
  <;> simp [*, Nat.cast_nonneg]
  <;> field_simp
  <;> linarith
  <;> ring_nf
  <;> simp [*, Nat.cast_nonneg]
  <;> field_simp
  <;> linarith
  <;> ring_nf
  <;> simp [*, Nat.cast_nonneg]
  <;> field_simp
  <;> linarith
  <;> ring_nf
  <;> simp [*, Nat.cast_nonneg]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp [Real.log_div, Real.log_pow, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg]
  ring_nf
  rw [Real.log_one]
  simp [Real.log_div, Real.log_pow, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg]
  ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h1 : deriv (fun x ↦ sin (sin (2 * x - 1) ^ 2 * x ^ 3 * (log x / log 5))) x = cos (sin (2 * x - 1) ^ 2 * x ^ 3 * (log x / log 5)) * (((((2 * sin (2 * x - 1) * (cos (2 * x - 1) * 2)) * (x ^ 3)) + (sin (2 * x - 1) ^ 2 * (3 * x ^ 2))) * (log x / log 5)) + (sin (2 * x - 1) ^ 2 * (x ^ 3) * ((1 / x) * (log 5 / log 5 ^ 2)))) := by
    apply deriv_sin
  rw [h1]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp only [Real.cos_log, Real.cos_arcsin, Real.sin_log, mul_neg, mul_one]
  ring_nf
  <;> field_simp
  <;> norm_num
  <;> apply deriv_mul_const_field <;> simp [Real.cos_log, Real.cos_arcsin, Real.sin_log, mul_neg, mul_one]
  <;> ring_nf
  <;> field_simp
  <;> norm_num
  <;> apply deriv_mul_const_field <;> simp [Real.cos_log, Real.cos_arcsin, Real.sin_log, mul_neg, mul_one]
  <;> ring_nf
  <;> field_simp
  <;> norm_num
  <;> apply deriv_mul_const_field <;> simp [Real.cos_log, Real.cos_arcsin, Real.sin_log, mul_neg, mul_one]
  <;> ring_nf
  <;> field_simp
  <;> norm_num

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  rw [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  <;> simp_all
  <;> norm_num
  <;> apply Real.log_ne_zero_of_pos_of_ne_one
  <;> norm_num
  <;> apply ne_of_gt
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  apply HasDerivAt.deriv
  let a : ℝ := 2 * x - 1
  let b : ℝ := x ^ 3
  let c : ℝ := Real.log x / Real.log 5
  have h1 : HasDerivAt (fun x => Real.sin (a x) ^ 2 * b x)
    (2 * Real.sin (a x) * Real.cos (a x) * b x + Real.sin (a x) ^ 2 * (3 * x ^ 2)) x := by
    have ha1 : HasDerivAt (fun x => a x) (2 : ℝ) x := by
      simpa only [mul_one, sub_zero, mul_comm] using (hasDerivAt_id x).const_mul 2
    have ha2 : HasDerivAt (fun x => b x) (3 * x ^ 2) x := by
      simpa only [mul_one, sub_zero, mul_comm] using (hasDerivAt_id x).pow 3
    have hc1 : HasDerivAt (fun x => c x) (1 / x * Real.log 5) x := by
      simpa only [mul_one, sub_zero, mul_comm] using (hasDerivAt_id x).const_div (Real.log 5)
    have hc2 : HasDerivAt (fun x => Real.sin (a x) ^ 2 * c x)
      (2 * Real.sin (a x) * Real.cos (a x) * c x + Real.sin (a x) ^ 2 * (1 / x * Real.log 5)) x := by
      apply HasDerivAt.mul
      · have h1 : HasDerivAt (fun x => Real.sin (a x)) (Real.cos (a x) * (2 : ℝ)) x := by
          apply HasDerivAt.comp x (hasDerivAt_sin (a x)) ha1
        have h2 : HasDerivAt (fun x => Real.sin (a x) ^ 2)
          (2 * Real.sin (a x) * Real.cos (a x)) x := by
          apply HasDerivAt.pow 2 h1
        exact h2.mul hc1
      · apply HasDerivAt.const_mul (2 * Real.sin (a x))
        apply HasDerivAt.mul hc1 (hasDerivAt_cos (a x))
    convert hc2 using 1
    ring
  have h2 : HasDerivAt (fun x => Real.exp (a x ^ 2 * b x * c x))
    (Real.exp (a x ^ 2 * b x * c x) * (2 * a x * b x * c x + a x ^ 2 * (3 * x ^ 2) * c x + a x ^ 2 * b x * (1 / x * Real.log 5))) x := by
    apply HasDerivAt.comp x (hasDerivAt_exp (a x ^ 2 * b x * c x)) h1
  convert h2 using 1
  ring

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 * (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  have h₁ : (2 : ℝ) ≠ 0 := by norm_num
  have h₂ : (5 : ℝ) ≠ 0 := by norm_num
  have h₃ : (3 : ℝ) ≠ 0 := by norm_num
  have h₄ : (4 : ℝ) ≠ 0 := by norm_num
  have h₅ : (2 : ℝ) ≠ 0 := by norm_num
  have h₆ : (3 : ℝ) ≠ 0 := by norm_num
  have h₇ : (5 : ℝ) ≠ 0 := by norm_num
  have h₈ : (6 : ℝ) ≠ 0 := by norm_num
  have h₉ : (7 : ℝ) ≠ 0 := by norm_num
  have h₁₀ : (8 : ℝ) ≠ 0 := by norm_num
  have h₁₁ : (9 : ℝ) ≠ 0 := by norm_num
  have h₁₂ : (10 : ℝ) ≠ 0 := by norm_num
  have h₁₃ : (11 : ℝ) ≠ 0 := by norm_num
  have h₁₄ : (12 : ℝ) ≠ 0 := by norm_num
  have h₁₅ : (13 : ℝ) ≠ 0 := by norm_num
  have h₁₆ : (14 : ℝ) ≠ 0 := by norm_num
  have h₁₇ : (15 : ℝ) ≠ 0 := by norm_num
  have h₁₈ : (16 : ℝ) ≠ 0 := by norm_num
  have h₁₉ : (17 : ℝ) ≠ 0 := by norm_num
  have h₂₀ : (18 : ℝ) ≠ 0 := by norm_num
  have h₂₁ : (19 : ℝ) ≠ 0 := by norm_num
  have h₂₂ : (20 : ℝ) ≠ 0 := by norm_num
  field_simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h_log_ne_zero_1, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  rw [Real.log_div]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
  ring_nf
  <;> simp_all [Real.log_ne_zero]

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, Real.log_mul, mul_add, mul_sub, mul_comm,
    mul_left_comm, mul_assoc]
  ring_nf
  <;> simp_all only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_exp, deriv_log,
    deriv_sin, deriv_cos, deriv_id, deriv_pow, pow_one, pow_two, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero, mul_neg, mul_one, mul_zero, neg_zero, sub_neg_eq_add,
    mul_neg_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero, mul_neg, mul_one, mul_zero, neg_zero, sub_neg_eq_add,
    mul_neg_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero, mul_neg, mul_one, mul_zero, neg_zero, sub_neg_eq_add,
    mul_neg_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero, mul_neg, mul_one, mul_zero, neg_zero, sub_neg_eq_add,
    mul_neg_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero, mul_neg, mul_one, mul_zero, neg_zero, sub_neg_eq_add,
    mul_neg_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, mul_one, sub_zero, mul_zero,
    add_zero, zero_add, zero_sub, sub_zero]
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf
  <;> simp_all only [add_assoc, add_left_comm, add_comm, sub_add_eq_sub_sub,
    sub_neg_eq_add, neg_add_rev, neg_sub, neg_neg, neg_zero]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  rw [deriv_mul, deriv_mul, deriv_mul]
  simp [*, mul_assoc, mul_comm, mul_left_comm, deriv_mul, deriv_exp, deriv_log, deriv_id,
    deriv_pow, deriv_const, deriv_add, deriv_sub, deriv_div, deriv_sin, deriv_cos]
  ring_nf
  <;> assumption
  <;> norm_num
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_zpow]
  rw [deriv_sin]
  rw [deriv_mul]
  rw [deriv_sin]
  rw [deriv_id]
  field_simp
  ring
  all_goals
    norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp_all [Real.log_ne_zero_iff, mul_comm, mul_assoc, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  ring
  <;> simp_all [Real.log_ne_zero_iff, mul_comm, mul_assoc, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> ring
  <;> simp_all [Real.log_ne_zero_iff, mul_comm, mul_assoc, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> ring
  <;> simp_all [Real.log_ne_zero_iff, mul_comm, mul_assoc, mul_left_comm, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  have h1 : deriv (fun x => (Real.sin (2 * x - 1)) ^ 2 * (x ^ 3) * (Real.log x / Real.log 5) + (Real.log (5 * x + 2)) ^ 3) x =
    ((((2 * Real.sin (2 * x - 1) * (Real.cos (2 * x - 1) * 2)) * (x ^ 3)) +
        ((Real.sin (2 * x - 1)) ^ 2 * (3 * x ^ 2))) * (Real.log x / Real.log 5)) +
        ((Real.sin (2 * x - 1)) ^ 2 * (x ^ 3)) * ((1 / x) * (Real.log 5 / Real.log 5 ^ 2)) +
        (3 * (Real.log (5 * x + 2)) ^ 2) * (5 / (5 * x + 2)) := by
    rw [deriv_add]
    -- Apply the chain rule to each term
    -- Apply the product rule to the first term
    rw [deriv_mul]
    -- Apply the product rule to the second term
    rw [deriv_mul]
    -- Apply the chain rule to each term
    -- Apply the chain rule to the logarithm term
    rw [deriv_log]
    -- Apply the chain rule to the logarithm term
    rw [deriv_log]
    -- Apply the chain rule to the logarithm term
    rw [deriv_log]
    -- Simplify the expression
    field_simp
    ring
    -- Apply the chain rule to each term
    -- Apply the chain rule to the sine term
    rw [deriv_sin]
    -- Apply the chain rule to the sine term
    rw [deriv_sin]
    -- Apply the chain rule to the sine term
    rw [deriv_sin]
    -- Simplify the expression
    field_simp
    ring
  -- Apply the chain rule to each term
  -- Apply the chain rule to the logarithm term
  rw [deriv_log]
  -- Apply the chain rule to the logarithm term
  rw [deriv_log]
  -- Apply the chain rule to the logarithm term
  rw [deriv_log]
  -- Simplify the expression
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [add_mul, mul_add, mul_sub, mul_one, mul_pow, mul_comm, mul_left_comm, mul_assoc]
  field_simp [h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26, Real.log_mul, Real.log_rpow, Real.log_one]
  rw [← sub_eq_zero]
  ring_nf
  <;> simp only [Real.log_one, Real.log_zero, sub_zero, zero_sub, mul_zero, zero_mul,
    add_zero, sub_self, zero_div, zero_pow, mul_one, one_pow, mul_add, mul_sub, mul_comm,
    mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc, sub_add_cancel, sub_self,
    zero_mul, zero_add, mul_one, one_mul, mul_right_comm, mul_right_comm, mul_right_comm,
    mul_right_comm, mul_right_comm, mul_right_comm, mul_right_comm, mul_right_comm]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₀ : deriv (fun x => Real.sin (Real.sin (2 * x - 1) ^ 2 / x ^ 3 * (Real.log x / Real.log 5))) x =
      Real.cos (Real.sin (2 * x - 1) ^ 2 / x ^ 3 * (Real.log x / Real.log 5)) *
        (((((2 * Real.sin (2 * x - 1) * (Real.cos (2 * x - 1) * 2)) * (x ^ 3) -
                    Real.sin (2 * x - 1) ^ 2 * (3 * x ^ 2)) /
                  (x ^ 3) ^ 2) *
                (Real.log x / Real.log 5)) +
            (Real.sin (2 * x - 1) ^ 2 / (x ^ 3) *
                ((1 / x) * Real.log 5 / Real.log 5 ^ 2))) := by
    simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
    rw [deriv_sin, deriv_sin]
    simp only [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]
    field_simp
    ring
  linarith

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₀ : x ≠ 0 := by
    rintro rfl
    norm_num at h_div_ne_zero_20
  have h₁ : (x : ℝ) ^ 3 ≠ 0 := by
    norm_cast
    exact pow_ne_zero _ h₀
  have h₂ : (5 : ℝ) ≠ 0 := by norm_num
  have h₃ : Real.log (5 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one zero_lt_five (by norm_num)
  field_simp [h₀, h₁, h₂, h₃, Real.log_ne_zero_of_pos_of_ne_one zero_lt_five (by norm_num)]
  ring_nf
  rw [Real.cos_arcsin]
  field_simp
  linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) ^ 2 := by
  simp only [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23, Real.log_ne_zero,
    ne_eq, Nat.cast_eq_zero, one_ne_zero, ne_eq, Nat.cast_eq_zero, one_ne_zero]
  ring_nf
  <;> field_simp <;> ring_nf
  <;> field_simp <;> ring_nf
  <;> field_simp <;> ring_nf
  <;> field_simp <;> ring_nf
  <;> field_simp <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  have h₁ : ∀ x, 5 ≠ 0 := fun _ => by norm_num
  have h₂ : ∀ x, Real.log 5 ≠ 0 := fun _ => by norm_num
  have h₃ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₄ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₅ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₆ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₇ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₈ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₉ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₁₀ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₁₁ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₁₂ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₁₃ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₁₄ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₁₅ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₁₆ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₁₇ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₁₈ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₁₉ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₂₀ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₂₁ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₂₂ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₂₃ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₂₄ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₂₅ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₂₆ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₂₇ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₂₈ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₂₉ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₃₀ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₃₁ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₃₂ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₃₃ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₃₄ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₃₅ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₃₆ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₃₇ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₃₈ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₃₉ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₄₀ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₄₁ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₄₂ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₄₃ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₄₄ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₄₅ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₄₆ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₄₇ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₄₈ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₄₉ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₅₀ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₅₁ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₅₂ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₅₃ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₅₄ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₅₅ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₅₆ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₅₇ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₅₈ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₅₉ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₆₀ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₆₁ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₆₂ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₆₃ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₆₄ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₆₅ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₆₆ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₆₇ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₆₈ : ∀ x, x ^ 2 ≠ 0 := fun _ => by norm_num
  have h₆₉ : ∀ x, x ≠ 0 := fun _ => by norm_num
  have h₇₀ : ∀ x, x ^ 3 ≠ 0 := fun _ => by norm_num
  have h₇₁ : ∀ x, x ^ 
example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 / (x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ≠ 0) (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = ((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) := by
  simp only [mul_comm]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  <;> simp [h_log_ne_zero_1, h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    mul_assoc, mul_comm, mul_left_comm]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [add_comm]
  simp only [add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc, mul_div_assoc]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  ring
  <;> simp [*, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]

example (x: ℝ)  (h_div_ne_zero_4: (x ^ 3) ≠ 0) (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [mul_comm, mul_assoc, mul_left_comm]
  field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring
  <;> apply_rules [Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> apply_rules [mul_comm, mul_assoc, mul_left_comm]
  <;> field_simp [h_div_ne_zero_4, h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23,
    Real.log_ne_zero_iff, Real.exp_ne_zero]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp_all [deriv_mul, deriv_div, deriv_rpow_const, deriv_log, deriv_sin, deriv_cos,
    deriv_const_mul, deriv_pow, deriv_id]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  apply Eq.symm
  rw [deriv_mul]
  nlinarith [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]
  <;> simp_all
  <;> field_simp
  <;> ring_nf
  <;> linarith [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22]

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by
  simp_all only [one_div, mul_inv_cancel_right₀, mul_inv_cancel_left₀, ne_eq,
    log_zero, mul_zero, zero_add, zero_sub, zero_mul, mul_zero, sub_zero,
    mul_one, mul_assoc, mul_right_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22,
    h_log_ne_zero_26]
  ring_nf
  rw [add_comm]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22,
    h_log_ne_zero_26]
  ring

example (x: ℝ)  (h_div_ne_zero_3: (x ^ 3) ≠ 0) (h_div_ne_zero_19: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_20: x ≠ 0) (h_log_ne_zero_22: (5:ℝ) ≠ 0) (h_log_ne_zero_26: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (x ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * x ^ 2)) / (x ^ 3) ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [one_div, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  ring
  field_simp [h_div_ne_zero_3, h_div_ne_zero_19, h_log_ne_zero_20, h_log_ne_zero_22, h_log_ne_zero_26,
    Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero]
  ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  rw [show (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) =
    (λ x ↦ Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3))
        by funext x; ring_nf]
  apply deriv_sin
  apply differentiable_at_add_const_iff.mpr
  apply differentiable_at_pow_const.mpr
  apply differentiable_at_id.mpr
  apply differentiable_at_const

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h_cos_x_ne_zero : ∀ x, Real.cos x ≠ 0 := by
    intro x
    apply Real.cos_ne_zero
  have h_sin_x_ne_zero : ∀ x, Real.sin x ≠ 0 := by
    intro x
    apply Real.sin_ne_zero
  field_simp [h_cos_x_ne_zero, h_sin_x_ne_zero, h_log_ne_zero_16, Real.cos_ne_zero,
    Real.sin_ne_zero]
  ring_nf
  <;> apply h_cos_x_ne_zero
  <;> apply h_sin_x_ne_zero
  <;> apply h_log_ne_zero_16

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  simp_all only [mul_comm, mul_left_comm, mul_assoc, mul_one, mul_div_cancel_left]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring_nf
  rw [add_comm]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  rw [add_comm]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  field_simp [h_log_ne_zero_16]
  rw [deriv_exp]
  rw [deriv_add]
  rw [deriv_sq]
  rw [deriv_log]
  rw [deriv_const_mul]
  rw [deriv_sin]
  rw [deriv_const_mul]
  rw [deriv_cos]
  rw [deriv_const_mul]
  ring
  <;> simp_all
  <;> norm_num
  <;> apply Differentiable.sin
  <;> apply Differentiable.log
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.exp
  <;> apply Differentiable.add
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.const_add

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  simp [deriv_log_of_ne_zero h_log_ne_zero_1, deriv_log_of_ne_zero h_log_ne_zero_16,
    deriv_sin, deriv_cos, deriv_pow, deriv_add, deriv_mul, deriv_const]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [add_assoc, add_left_comm, mul_assoc, mul_comm, mul_left_comm,
    Real.exp_add, Real.exp_mul, Real.exp_sub, Real.log_add, Real.log_mul, Real.log_pow,
    Real.log_inv, Real.log_exp, Real.sin_add, Real.sin_sub, Real.sin_mul, Real.cos_add,
    Real.cos_sub, Real.cos_mul]
  rw [add_comm]
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]
  rw [add_comm]
  field_simp [h_log_ne_zero_15]
  ring
  <;> simp [Real.log_pow, Real.log_mul, Real.log_exp, Real.sin_add, Real.sin_sub, Real.sin_mul,
    Real.cos_add, Real.cos_sub, Real.cos_mul, Real.exp_add, Real.exp_mul, Real.exp_sub,
    Real.log_add, Real.log_inv, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm,
    add_comm]

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  field_simp [h_log_ne_zero_16, Real.log_ne_zero, Real.exp_ne_zero, sq, mul_assoc]
  ring_nf
  <;> simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  <;> field_simp [h_log_ne_zero_16, Real.log_ne_zero, Real.exp_ne_zero, sq, mul_assoc]
  <;> ring_nf
  <;> simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  <;> field_simp [h_log_ne_zero_16, Real.log_ne_zero, Real.exp_ne_zero, sq, mul_assoc]
  <;> ring_nf
  <;> simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    mul_right_comm]
  <;> field_simp [h_log_ne_zero_16, Real.log_ne_zero, Real.exp_ne_zero, sq, mul_assoc]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  rw [deriv_add]
  <;> simp [deriv_add, deriv_sin, deriv_log, deriv_pow, deriv_mul, deriv_id, deriv_const,
    deriv_comp, deriv_inv, deriv_add, deriv_sub, deriv_cos, deriv_neg, deriv_exp,
    deriv_log, deriv_pow, deriv_mul, deriv_id, deriv_const, deriv_comp, deriv_inv,
    deriv_add, deriv_sub, deriv_cos, deriv_neg, deriv_exp, deriv_log, deriv_pow, deriv_mul,
    deriv_id, deriv_const, deriv_comp, deriv_inv, deriv_add, deriv_sub, deriv_cos, deriv_neg,
    deriv_exp]
  <;> norm_num
  <;> linarith
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x ↦ Real.log x) (1 / x) x := by
    intro x hx
    have hx' : x ≠ 0 := hx
    convert hasDerivAt_log hx'
  have h2 : ∀ x : ℝ, HasDerivAt (fun x ↦ (5 * x + 2)) 5 x := by
    intro x
    have hx' : (5 * x + 2) ≠ 0 := by linarith
    convert hasDerivAt_mul_const 5
  have h3 : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.sin x) (Real.cos x) x := by
    intro x
    convert hasDerivAt_sin x
  have h4 : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.cos x) (-Real.sin x) x := by
    intro x
    convert hasDerivAt_cos x
  have h5 : ∀ x : ℝ, HasDerivAt (fun x ↦ (2 * x - 1)) 2 x := by
    intro x
    convert hasDerivAt_mul_const 2
  have h6 : ∀ x : ℝ, HasDerivAt (fun x ↦ (3 * Real.log (5 * x + 2) ^ 2)) ((3 * 2 * (5 / (5 * x + 2))) * Real.log (5 * x + 2)) x := by
    intro x
    convert hasDerivAt_pow 2 (Real.log (5 * x + 2))
  simp only [pow_two] at *
  field_simp [*, mul_assoc]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [deriv_add, deriv_pow, deriv_log, deriv_sin, deriv_cos, deriv_sub, deriv_const]
  field_simp [h_log_ne_zero_15]
  ring_nf
  <;> simp only [sin_sq, cos_sq, add_assoc, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  have h_log_ne_zero_15 : ((5:ℝ) * x + (2:ℝ)) ≠ 0 := by assumption
  have h_sin_ne_zero_15 : Real.sin ((2:ℝ) * x - (1:ℝ)) ≠ 0 := by
    intro h
    have h1 : (2:ℝ) * x - (1:ℝ) = 0 := by simpa using h
    have h2 : (2:ℝ) * x = (1:ℝ) := by linarith
    have h3 : x = (1:ℝ) / (2:ℝ) := by linarith
    have h4 : (5:ℝ) * x + (2:ℝ) = (5:ℝ) * (1:ℝ) / (2:ℝ) + (2:ℝ) := by rw [h3]
    have h5 : (5:ℝ) * (1:ℝ) / (2:ℝ) + (2:ℝ) = (5:ℝ) / (2:ℝ) + (2:ℝ) := by ring
    have h6 : (5:ℝ) / (2:ℝ) + (2:ℝ) = (9:ℝ) / (2:ℝ) := by ring
    have h7 : (9:ℝ) / (2:ℝ) ≠ 0 := by norm_num
    exact h_log_ne_zero_15 h7
  field_simp [h_sin_ne_zero_15, h_log_ne_zero_15]
  ring
  <;> simp only [deriv_add, deriv_mul, deriv_const, deriv_sin, deriv_log, deriv_id]
  <;> field_simp [h_sin_ne_zero_15, h_log_ne_zero_15]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp_all only [deriv_sin, deriv_log, deriv_add, deriv_mul, deriv_pow, deriv_id'',
    deriv_const', deriv_comp, deriv_inv, deriv_exp, Real.exp_log]
  <;> field_simp
  <;> ring
  <;> simp_all only [Real.sin_two_mul, Real.sin_sub, Real.cos_two_mul, Real.cos_sub]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_sub, Nat.cast_pow]
  apply HasDerivAt.deriv
  have h1 : HasDerivAt (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) x := by
    have h1 : HasDerivAt (fun x ↦ (2 * x - 1)) (2:ℝ) x := by
      apply HasDerivAt.sub
      apply HasDerivAt.const_mul
      apply hasDerivAt_id
      apply hasDerivAt_const
    have h2 : HasDerivAt (fun x ↦ Real.sin x) (Real.cos x) (2 * x - 1) := by
      apply hasDerivAt_sin
    have h3 : HasDerivAt (fun x ↦ (Real.sin x) ^ 2) (2 * Real.sin x * Real.cos x) (2 * x - 1) := by
      apply HasDerivAt.pow
      apply h2
      norm_num
    have h4 : HasDerivAt (fun x ↦ (2 * x - 1)) (2:ℝ) x := by
      apply HasDerivAt.sub
      apply HasDerivAt.const_mul
      apply hasDerivAt_id
      apply hasDerivAt_const
    have h5 : HasDerivAt (fun x ↦ (Real.sin ((2 * x - 1)))) (Real.cos ((2 * x - 1)) * (2:ℝ)) x := by
      apply HasDerivAt.comp
      apply h2
      apply h4
    have h6 : HasDerivAt (fun x ↦ (Real.sin ((2 * x - 1))) ^ 2) (2 * Real.sin ((2 * x - 1)) * (Real.cos ((2 * x - 1)) * (2:ℝ))) x := by
      apply HasDerivAt.pow
      apply h5
      norm_num
    exact h6
  have h2 : HasDerivAt (fun x ↦ (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))
    (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) x := by
    have h1 : HasDerivAt (fun x ↦ (5 * x + 2)) (5:ℝ) x := by
      apply HasDerivAt.add
      apply HasDerivAt.const_mul
      apply hasDerivAt_id
      apply hasDerivAt_const
    have h2 : HasDerivAt (fun x ↦ Real.log x) (1 / x) x := by
      apply hasDerivAt_log
      linarith
    have h3 : HasDerivAt (fun x ↦ Real.log ((5 * x + 2))) (5 / (5 * x + 2)) x := by
      apply HasDerivAt.comp
      apply h2
      apply h1
    have h4 : HasDerivAt (fun x ↦ (Real.log ((5 * x + 2))) ^ 3) (3 * (Real.log ((5 * x + 2)) ^ 2) * (5 / (5 * x + 2))) x := by
      apply HasDerivAt.pow
      apply h3
      norm_num
    have h5 : HasDerivAt (fun x ↦ x ^ 3) (3 * x ^ 2) x := by
      apply HasDerivAt.pow
      apply hasDerivAt_id
    have h6 : HasDerivAt (fun x ↦ (Real.log ((5 * x + 2))) ^ 3 * (x ^ 3))
      ((3 * (Real.log ((5 * x + 2)) ^ 2) * (5 / (5 * x + 2))) * (x ^ 3) + (Real.log ((5 * x + 2)) ^ 3) * (3 * x ^ 2)) x := by
      apply HasDerivAt.mul
      apply h4
      apply h5
    have h7 : HasDerivAt (fun x ↦ Real.log x / Real.log (5:ℝ)) (1 / (x * Real.log (5:ℝ))) x := by
      apply HasDerivAt.div
      apply h2
      apply hasDerivAt_const
      linarith
    have h8 : HasDerivAt (fun x ↦ (Real.log ((5 * x + 2)) ^ 3 * (x ^ 3)) * (Real.log x / Real.log (5:ℝ)))
      (((3 * (Real.log ((5 * x + 2)) ^ 2) * (5 / (5 * x + 2))) * (x ^ 3) + (Real.log ((5 * x + 2)) ^ 3) * (3 * x ^ 2)) * (1 / (x * Real.log (5:ℝ)))) x := by
      apply HasDerivAt.mul
      apply h6
      apply h7
    have h9 : HasDerivAt (fun x ↦ (Real.log ((5 * x + 2)) ^ 3 * (x ^ 3)) * (Real.log x / Real.log (5:ℝ)))
      (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) x := by
      apply h8
      ring
    exact h9
  have h3 : HasDerivAt (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ)))
    (2 * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) +
      (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) x := by
    apply HasDerivAt.add
    apply h1
    apply h2
  exact h3

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  rw [deriv_sin]
  ring_nf
  <;> simp_all
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.sin
  <;> apply Differentiable.pow
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.add_const
  <;> apply Differentiable.log
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub_const
  <;> apply Differentiable.pow
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.add_const
  <;> apply Differentiable.log
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.pow
  <;> apply Differentiable.sub_const

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp only [deriv_comp, deriv_sin, deriv_log, deriv_pow, deriv_mul, deriv_add, deriv_sub,
    deriv_neg, deriv_id, deriv_const, mul_one, mul_zero, sub_zero, zero_add, neg_neg,
    zero_sub, neg_mul, neg_neg, mul_neg, neg_sub, neg_mul, neg_neg, mul_zero, sub_neg_eq_add,
    mul_one, add_zero, mul_comm]
  field_simp [h_log_ne_zero_16]
  ring

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  rw [deriv_tan]
  simp [Real.cos_ne_zero_iff, h_tan_ne_zero_1, h_log_ne_zero_16]
  field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  ring
  <;> norm_num
  <;> simp [Real.cos_ne_zero_iff, h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> ring
  <;> norm_num
  <;> simp [Real.cos_ne_zero_iff, h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> field_simp [h_tan_ne_zero_1, h_log_ne_zero_16]
  <;> ring
  <;> norm_num

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x hx
    rw [show (fun y : ℝ => y ^ 2) = (fun y : ℝ => y * y) by rfl]
    apply HasDerivAt.mul
    apply hasDerivAt_id
    apply hasDerivAt_id
  have h₂ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    intro x hx
    rw [show (fun y : ℝ => y ^ 3) = (fun y : ℝ => y * y * y) by rfl]
    apply HasDerivAt.mul
    apply HasDerivAt.mul
    apply hasDerivAt_id
    apply hasDerivAt_id
    apply hasDerivAt_id
  field_simp [*, sub_eq_add_neg]
  ring
  <;> norm_num
  <;> assumption

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h1 : ∀ x, (2 * x - 1).sin ≠ 0 := fun x => by
    intro h
    have h' := sin_le_one (2 * x - 1)
    rw [h] at h'
    linarith
  have h2 : ∀ x, (5 * x + 2).log ≠ 0 := fun x => by
    intro h
    have h' := log_pos (by linarith : (5 * x + 2) > 0)
    rw [h] at h'
    linarith
  field_simp [h1, h2, Real.log_ne_zero]
  ring_nf
  field_simp [h1, h2, Real.log_ne_zero]
  rw [← sub_eq_zero]
  field_simp [h1, h2, Real.log_ne_zero]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [h_log_ne_zero_15, deriv_add, deriv_sub, deriv_pow, deriv_exp, deriv_sin, deriv_cos,
    deriv_mul, deriv_id'', deriv_const, deriv_log, deriv_log]
  ring_nf
  <;> simp [h_log_ne_zero_15]
  <;> ring_nf
  <;> simp [h_log_ne_zero_15]
  <;> ring_nf
  <;> simp [h_log_ne_zero_15]
  <;> ring_nf
  <;> simp [h_log_ne_zero_15]
  <;> ring_nf
  <;> simp [h_log_ne_zero_15]
  <;> ring_nf

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x))) := by
  simp only [sub_eq_add_neg, mul_add, mul_neg, neg_mul, neg_neg, mul_one, mul_assoc]
  rw [add_comm]
  ring_nf
  field_simp [h_log_ne_zero_16]
  simp only [Real.deriv_sin, Real.deriv_exp, Real.deriv_log, Real.deriv_id'', Real.deriv_pow,
    deriv_add, deriv_sub, deriv_const', deriv_mul, deriv_const, deriv_id, deriv_neg, deriv_pow,
    deriv_id'', deriv_exp, deriv_log, deriv_sin, deriv_cos, deriv_neg, deriv_mul, deriv_const',
    deriv_id]
  ring_nf

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp [deriv_sub, deriv_add, deriv_pow, deriv_sin, deriv_cos, deriv_log, deriv_mul, deriv_const]
  field_simp
  ring
  <;> aesop

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp only [deriv_sub, deriv_sin, deriv_pow, deriv_log, deriv_const, deriv_add, deriv_mul,
    deriv_id, deriv_comp, deriv_pow, deriv_log, deriv_const, deriv_mul, deriv_id, deriv_comp]
  field_simp
  ring
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp_all only [one_div, mul_neg, mul_one, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm]
  apply Eq.symm
  field_simp
  ring
  <;> apply Eq.symm
  <;> simp_all only [one_div, mul_neg, mul_one, mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [mul_sub, mul_one, sub_eq_add_neg, neg_mul, neg_neg, mul_comm]
  simp only [add_assoc]
  field_simp [h_log_ne_zero_15, Real.sin_ne_zero_iff]
  ring
  <;> simp only [Real.log_pow, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15, Real.sin_ne_zero_iff]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  rw [deriv_sub, deriv_sub, deriv_add]
  <;> simp [deriv_log, deriv_sin, deriv_cos, deriv_pow, deriv_id, deriv_const, deriv_mul,
    deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_pow, deriv_id, deriv_const,
    deriv_mul, deriv_pow, deriv_id, deriv_const, deriv_mul, deriv_pow, deriv_id, deriv_const]
  <;> norm_num
  <;> field_simp
  <;> ring
  <;> simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> linarith
  <;> simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> linarith
  <;> simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> linarith
  <;> simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (x ^ 3)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by
  simp [sub_eq_add_neg, mul_assoc]
  field_simp [h_log_ne_zero_16, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32, mul_comm]
  ring_nf
  norm_cast
  <;> simp_all

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  rw [deriv_sin]
  simp only [deriv_mul, deriv_const, deriv_id'', deriv_pow, deriv_sub, deriv_exp, deriv_log,
    deriv_neg, deriv_add, deriv_sin, deriv_cos, deriv_id]
  field_simp
  ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp [deriv_cos, deriv_sin, deriv_pow, deriv_mul, deriv_const_mul, deriv_add, deriv_sub,
    deriv_log, deriv_id, sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, mul_assoc,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_log,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]
  ring_nf
  <;> field_simp <;> ring_nf
  <;> simp [h_log_ne_zero_16]
  <;> field_simp <;> ring_nf
  <;> simp [h_log_ne_zero_16]

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h1 : ∀ x : ℝ, cos (sin (2 * x - 1) ^ 2 * log (5 * x + 2) ^ 3) ≠ 0 := by
    intro x
    apply cos_ne_zero_of_mem_Ioo
    have h2 : sin (2 * x - 1) ^ 2 * log (5 * x + 2) ^ 3 ∈ Ioo (-(π / 2)) (π / 2) := by
      constructor <;> linarith [sin_pos_of_mem_Ioo (by linarith : (2 * x - 1 : ℝ) ∈ Ioo (-(π / 2)) (π / 2)) ,
        log_pos (by linarith : (5 * x + 2 : ℝ) > 1)]
    exact h2
  have h2 : ∀ x : ℝ, 5 * x + 2 ≠ 0 := by
    intro x
    linarith
  simp only [deriv_tan_eq_sec_mul_tan_add_mul_sec, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [h1, h2]
  ring
  <;> simp only [Real.tan_eq_sin_div_cos, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h1, h2]
  <;> ring
  <;> simp only [Real.tan_eq_sin_div_cos, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  <;> field_simp [h1, h2]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp [deriv_exp, deriv_sin, deriv_log, deriv_pow, deriv_id'', deriv_mul, deriv_const, mul_zero, add_zero, mul_one, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_16]
  ring
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]
  <;> simp [Real.sin_add, Real.cos_add, mul_add, mul_sub, add_sub, sub_sub]
  <;> simp [Real.exp_log]

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  have h_log_ne_zero_16 : (5 * x + 2) ≠ 0 := by
    intro h
    apply h_log_ne_zero_1
    simp_all
  have h_sin_ne_zero : Real.sin (2 * x - 1) ≠ 0 := by
    intro h
    simp_all
  field_simp [h_log_ne_zero_1, h_log_ne_zero_16, h_sin_ne_zero]
  ring
  <;> simp_all only [mul_one, mul_zero, mul_neg, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_1, h_log_ne_zero_16, h_sin_ne_zero]
  <;> ring
  <;> simp_all only [mul_one, mul_zero, mul_neg, mul_add, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_1, h_log_ne_zero_16, h_sin_ne_zero]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  norm_num
  rw [add_comm]
  field_simp [h_log_ne_zero_15]
  ring
  <;> norm_num <;>
  simp only [mul_assoc] <;>
  ring_nf <;>
  simp only [mul_assoc] <;>
  norm_num
  <;>
  linarith

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp only [pow_two, mul_neg, mul_one, sub_neg_eq_add, mul_add, add_mul]
  apply Eq.symm
  field_simp [h_log_ne_zero_16]
  ring
  <;> simp only [pow_two, mul_neg, mul_one, sub_neg_eq_add, mul_add, add_mul]
  <;> field_simp [h_log_ne_zero_16]
  <;> ring
  <;> simp only [pow_two, mul_neg, mul_one, sub_neg_eq_add, mul_add, add_mul]
  <;> field_simp [h_log_ne_zero_16]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp only [mul_add, mul_sub, mul_one, mul_pow, deriv_add, deriv_sub, deriv_mul, deriv_comp,
    deriv_log, deriv_sin, deriv_cos, deriv_pow, deriv_id, deriv_const, pow_one]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25]
  ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp only [deriv_mul, deriv_zpow, deriv_sin, deriv_exp, deriv_comp, deriv_id'', deriv_const']
  ring
  <;> simp only [deriv_mul, deriv_zpow, deriv_sin, deriv_exp, deriv_comp, deriv_id'', deriv_const']
  <;> ring
  <;> simp only [deriv_mul, deriv_zpow, deriv_sin, deriv_exp, deriv_comp, deriv_id'', deriv_const']
  <;> ring
  <;> simp only [deriv_mul, deriv_zpow, deriv_sin, deriv_exp, deriv_comp, deriv_id'', deriv_const']
  <;> ring
  <;> simp only [deriv_mul, deriv_zpow, deriv_sin, deriv_exp, deriv_comp, deriv_id'', deriv_const']
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp only [one_div, mul_pow, mul_add, mul_comm, mul_assoc, mul_left_comm]
  ring
  <;> field_simp <;> linarith

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  rw [deriv_sin_sq]
  simp only [mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  rw [deriv_log]
  simp only [mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_15]
  ring
  <;> simp only [mul_add, mul_sub, mul_one, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp only [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring
  <;> simp only [mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp [h_log_ne_zero_15, h_div_ne_zero_29, h_log_ne_zero_30, h_log_ne_zero_32]
  <;> ring

example (x: ℝ)  (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  have h₀ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → Real.log (5 * x + 2) ≠ 0 := by
    intro x h₁ h₂ h₃
    apply Real.log_ne_zero
    nlinarith
  have h₁ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → Real.sqrt (x ^ 3) ≠ 0 := by
    intro x h₁ h₂ h₃
    exact pow_ne_zero 3 (by linarith)
  have h₂ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → x ^ 3 ≠ 0 := by
    intro x h₁ h₂ h₃
    exact pow_ne_zero 3 (by linarith)
  have h₃ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → x ^ 2 ≠ 0 := by
    intro x h₁ h₂ h₃
    exact pow_ne_zero 2 (by linarith)
  have h₄ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → Real.sqrt (x ^ 3) ^ 2 = x ^ 3 := by
    intro x h₁ h₂ h₃
    exact Real.sq_sqrt (by positivity)
  have h₅ : ∀ x : ℝ, (x + 2) ≠ 0 → x ≠ 0 → 5 ≠ 0 → Real.sqrt (x ^ 3) ^ 2 = x ^ 3 := by
    intro x h₁ h₂ h₃
    exact Real.sq_sqrt (by positivity)
  simp [*, deriv_mul, deriv_zpow, mul_assoc, mul_comm, mul_left_comm]
  field_simp [*, Real.log_mul, Real.log_rpow, mul_assoc, mul_comm, mul_left_comm]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  have h₀ : deriv (fun x => Real.sin (Real.sin (2 * x - 1) ^ 2 / Real.log (5 * x + 2) ^ 3)) x =
      Real.cos (Real.sin (2 * x - 1) ^ 2 / Real.log (5 * x + 2) ^ 3) *
      (((2 * Real.sin (2 * x - 1) * (Real.cos (2 * x - 1) * 2)) * (Real.log (5 * x + 2) ^ 3) -
        (Real.sin (2 * x - 1) ^ 2) * ((3 : ℝ) * Real.log (5 * x + 2) ^ 2 * (5 / (5 * x + 2)))) /
      (Real.log (5 * x + 2) ^ 3) ^ 2) := by
    rw [deriv_sin, deriv_sin, deriv_div]
    field_simp [Real.log_ne_zero_iff, h_div_ne_zero_3, h_log_ne_zero_16, mul_comm, mul_assoc, mul_left_comm]
    ring
    <;> simp_all
  assumption

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  simp [deriv_cos, deriv_sin, mul_comm, mul_assoc, mul_left_comm]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / Real.cos (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  rw [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16]
  ring_nf
  <;> norm_num
  <;> simp_all
  <;> field_simp [h_tan_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) := by
  simp_all [Real.exp_ne_zero]
  field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  ring_nf
  <;> norm_cast
  <;> simp_all [Real.exp_ne_zero]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all [Real.exp_ne_zero]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all [Real.exp_ne_zero]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> norm_cast
  <;> simp_all [Real.exp_ne_zero]
  <;> field_simp [h_div_ne_zero_3, h_log_ne_zero_16]
  <;> ring_nf
  <;> norm_cast

example (x: ℝ)  (h_log_ne_zero_1: ((Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2 / (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) / (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  apply Eq.symm
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_comm]
  ring_nf
  rw [← sub_eq_zero]
  apply Eq.symm
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_comm]
  ring_nf
  rw [← sub_eq_zero]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_3, h_log_ne_zero_16, mul_comm]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [one_div, mul_comm, mul_one]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, log_ne_zero_iff]
  ring_nf
  simp only [Real.sin_two_mul, Real.cos_two_mul, mul_assoc]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, log_ne_zero_iff]
  ring
  <;> simp only [Real.sin_two_mul, Real.cos_two_mul, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, log_ne_zero_iff]
  <;> ring
  <;> simp only [Real.sin_two_mul, Real.cos_two_mul, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, log_ne_zero_iff]
  <;> ring
  <;> simp only [Real.sin_two_mul, Real.cos_two_mul, mul_assoc]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, log_ne_zero_iff]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.exp x) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  field_simp [Real.log_ne_zero, add_pos, mul_pos, zero_lt_two, h_div_ne_zero_3, h_log_ne_zero_16,
    exp_pos, mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
  -- Porting note: was `ring`
  simp only [add_assoc, add_left_comm, add_right_comm, mul_assoc, mul_comm, mul_left_comm,
    mul_add, mul_sub, sub_eq_add_neg, add_mul]
  rw [deriv_mul]
  field_simp
  ring_nf
  <;> field_simp
  <;> ring_nf
  <;> field_simp
  <;> ring_nf
  <;> field_simp
  <;> ring_nf
  <;> field_simp
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp_all only [ne_eq, one_div, ← pow_two]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25, h_div_ne_zero_2]
  ring_nf
  simp only [Real.log_one, mul_one, sub_zero, mul_zero, zero_sub, zero_mul,
    add_zero, zero_add, mul_assoc, mul_comm, mul_left_comm, mul_comm,
    mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm]
  field_simp [h_log_ne_zero_15, h_log_ne_zero_25, h_div_ne_zero_2]
  ring_nf
  <;> simp_all only [ne_eq, one_div, ← pow_two]
  <;> field_simp [h_log_ne_zero_15, h_log_ne_zero_25, h_div_ne_zero_2]
  <;> ring_nf
  <;> simp only [Real.log_one, mul_one, sub_zero, mul_zero, zero_sub, zero_mul,
    add_zero, zero_add, mul_assoc, mul_comm, mul_left_comm, mul_comm,
    mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm, mul_assoc, mul_left_comm, mul_comm]
  <;> field_simp [h_log_ne_zero_15, h_log_ne_zero_25, h_div_ne_zero_2]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_log_ne_zero_25: x ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * Real.cos (Real.log x)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  simp_all [deriv_div, deriv_mul, deriv_pow, deriv_sin, deriv_log, deriv_const,
    deriv_sub, deriv_add, deriv_id]
  field_simp
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  rw [show deriv (fun x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x =
    (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))
    by
    rw [deriv_add]
    · rw [deriv_div]
      · rw [deriv_pow, deriv_sin, deriv_const_mul, deriv_sub, deriv_const_mul, deriv_id', deriv_const', deriv_const]
        simp [pow_succ, pow_zero, mul_one, sub_zero, mul_comm, mul_assoc, mul_left_comm]
      · norm_num
      · norm_num
    · rw [deriv_pow, deriv_sin, deriv_const_mul, deriv_sub, deriv_const_mul, deriv_id', deriv_const', deriv_const]
      simp [pow_succ, pow_zero, mul_one, sub_zero, mul_comm, mul_assoc, mul_left_comm]
    <;> norm_num
    <;> linarith]
  ring
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp only [mul_add, mul_sub, mul_one, mul_div_assoc, mul_assoc, mul_comm, mul_left_comm]
  field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero_of_pos_of_ne_one]
  ring
  <;> simp [Real.log_one, Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring_nf
  <;> simp [Real.log_one, Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring_nf
  <;> simp [Real.log_one, Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring_nf
  <;> simp [Real.log_one, Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
  <;> field_simp [h_div_ne_zero_2, h_log_ne_zero_15, Real.log_ne_zero_of_pos_of_ne_one]
  <;> ring_nf

example (x: ℝ)  (h_div_ne_zero_2: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_15: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  have h : x ≠ 0 := by intro h; rw [h] at h_log_ne_zero_30; simp_all
  have h₁ : (5:ℝ) * x + (2:ℝ) ≠ 0 := by intro h; rw [h] at h_div_ne_zero_29; simp_all
  have h₂ : (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 ≠ 0 := by intro h; rw [h] at h_div_ne_zero_2; simp_all
  have h₃ : Real.log (5:ℝ) ≠ 0 := by intro h; rw [h] at h_log_ne_zero_32; simp_all
  field_simp [h, h₁, h₂, h₃, Real.log_ne_zero_iff]
  ring_nf
  rw [Real.log_div]
  <;> simp_all [Real.log_ne_zero_iff]
  <;> field_simp [h, h₁, h₂, h₃, Real.log_ne_zero_iff]
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_3: (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3 ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) (h_div_ne_zero_29: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_30: x ≠ 0) (h_log_ne_zero_32: (5:ℝ) ≠ 0): deriv (λ x ↦ (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 / (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (x ^ 3) * (Real.log x / Real.log (5:ℝ))) x = (((((((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) - (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2) * (x ^ 3)) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((3:ℝ) * x ^ 2))) * (Real.log x / Real.log (5:ℝ))) + ((Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2 / Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * (x ^ 3)) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) := by
  simp_all only [one_div, mul_div_assoc, mul_assoc]
  field_simp
  ring_nf
  <;> simp_all
  <;> apply pow_ne_zero
  <;> norm_num

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h1 : ∀ x, x ≠ 0 → deriv (fun y => Real.sin (y)) x = Real.cos x := fun _ _ => deriv_sin _
  have h2 : ∀ x, x ≠ 0 → deriv (fun y => y ^ 3) x = 3 * x ^ 2 := fun _ _ => deriv_pow 3 _
  have h3 : ∀ x, x ≠ 0 → deriv (fun y => Real.log y) x = 1 / x := fun _ _ => deriv_log _
  have h4 : ∀ x, x ≠ 0 → deriv (fun y => Real.log y / Real.log (5:ℝ)) x = 1 / (x * Real.log 5) := fun _ _ => by
    rw [deriv_div (h3 _) (h3 5) (by simp)]; field_simp [Real.log_ne_zero_of_pos_of_ne_one]
  have h5 : ∀ x, x ≠ 0 → deriv (fun y => Real.log (5 * y + 2)) x = 5 / (5 * x + 2) := fun _ _ => by
    rw [deriv_log_of_mem_Ioi]; field_simp [add_pos_of_nonneg_of_pos]
  have h6 : ∀ x, x ≠ 0 → deriv (fun y => Real.log (5 * y + 2) ^ 3) x = 3 * (5 / (5 * x + 2)) ^ 2 * 5 :=
    fun _ _ => by rw [deriv_pow]; simp [h5]
  simp [h1, h2, h3, h4, h5, h6]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h : ∀ x : ℝ, x ≠ 0 → x ^ 3 ≠ 0 := fun x hx ↦ by positivity
  have h₁ : ∀ x : ℝ, x ≠ 0 → x ^ 2 ≠ 0 := fun x hx ↦ by positivity
  have h₂ : ∀ x : ℝ, x ≠ 0 → x ^ 4 ≠ 0 := fun x hx ↦ by positivity
  field_simp [h, h₁, h₂, Real.log_mul, Real.log_rpow, mul_add, mul_comm, mul_left_comm, mul_assoc]
  ring
  <;> simp_all
  <;> field_simp [Real.log_ne_zero_of_pos_of_ne_one, mul_assoc]
  <;> ring_nf
  <;> linarith

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  apply Eq.symm
  rw [deriv_tan]
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17, Real.log_ne_zero]
  ring
  <;> assumption

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) := by
  have h_log_ne_zero_10 : Real.log (5:ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    norm_num
    norm_num
  have h_log_ne_zero_12 : x ≠ 0 := by
    intro h
    rw [h] at h_log_ne_zero_10
    simp at h_log_ne_zero_10
  have h_log_ne_zero_14 : (5:ℝ) ≠ 0 := by norm_num
  have h_log_ne_zero_16 : (5 * x + 2) ≠ 0 := by
    intro h
    rw [h] at h_log_ne_zero_17
    simp at h_log_ne_zero_17
  field_simp [*, Real.exp_ne_zero]
  ring
  <;> norm_num
  <;> field_simp [*, Real.exp_ne_zero]
  <;> linarith

example (x: ℝ)  (h_log_ne_zero_1: ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) + (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) / ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) + Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17,
    mul_comm, mul_assoc, mul_left_comm, add_comm, add_assoc, add_left_comm]
  ring_nf
  rw [Real.log_div]
  <;> field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17,
    mul_comm, mul_assoc, mul_left_comm, add_comm, add_assoc, add_left_comm]
  <;> ring_nf
  <;> simp_all [Real.log_ne_zero]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp only [deriv_add, deriv_const, zero_add, zero_mul, deriv_mul, deriv_pow, deriv_exp,
    deriv_log, deriv_id'', deriv_const', one_mul]
  field_simp [h_div_ne_zero_9, h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16]
  ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp [add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  rw [← sub_eq_zero]
  field_simp [h_log_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_17, Real.log_exp,
    Real.log_mul, Real.log_rpow, mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  ring
  <;> simp_all [mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> field_simp [h_log_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_17, Real.log_exp,
    Real.log_mul, Real.log_rpow, mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> ring
  <;> simp_all [mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> field_simp [h_log_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_17, Real.log_exp,
    Real.log_mul, Real.log_rpow, mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> ring
  <;> simp_all [mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> field_simp [h_log_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_17, Real.log_exp,
    Real.log_mul, Real.log_rpow, mul_comm, mul_left_comm, mul_assoc, add_assoc, mul_add, add_mul]
  <;> ring
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  have h₁ : ∀ x : ℝ, x ≠ 0 → deriv (λ y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
    intro x hx
    rw [deriv_pow, mul_comm]
    <;> simp [hx]
  have h₂ : ∀ x : ℝ, x ≠ 0 → deriv (λ y : ℝ => Real.log y / Real.log 5) x = (1 / x) * (Real.log 5 / x) := by
    intro x hx
    field_simp
    rw [deriv_log' x hx, mul_comm]
    <;> simp [hx]
  have h₃ : ∀ x : ℝ, x ≠ 0 → deriv (λ y : ℝ => Real.cos (Real.log y)) x = -Real.sin (Real.log x) * (1 / x) := by
    intro x hx
    rw [deriv_cos, deriv_log' x hx]
    <;> simp [hx]
  simp_all [deriv_add, deriv_const, deriv_mul, deriv_comp, deriv_log', deriv_zpow, mul_assoc, mul_comm, mul_left_comm]
  <;> field_simp
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → deriv (fun x => x ^ 3 * (log x / log 5)) x = (3 * x ^ 2) * (log x / log 5) + (x ^ 3) * ((1 / x) * log 5 / log 5 ^ 2) := by
    intro x hx
    rw [deriv_mul (differentiableAt_pow 3) (differentiableAt_log.2 hx)]
    simp [deriv_pow, deriv_log, Nat.cast_ofNat, mul_div_cancel_left _ (log_ne_zero_of_pos_of_ne_one zero_lt_five.2 (by norm_num : (5 : ℝ) ≠ 1))]
    ring
  have h2 : ∀ x : ℝ, deriv (fun x => (log (5 * x + 2)) ^ 3 * cos (log x)) x =
      (3 * log (5 * x + 2) ^ 2 * (5 / (5 * x + 2))) * cos (log x) + (log (5 * x + 2) ^ 3) * (-sin (log x) * (1 / x)) := by
    intro x
    rw [deriv_mul (differentiableAt_log.2 (by nlinarith : 0 < 5 * x + 2)) (differentiable_cos.differentiableAt)]
    simp [deriv_log, deriv_cos, Nat.cast_ofNat, mul_div_cancel_left _ (by nlinarith : 0 < 5 * x + 2)]
    ring
  simp_all [h1, h2]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  simp [deriv_add, deriv_mul, deriv_const, deriv_log, deriv_pow, deriv_sin, deriv_add, deriv_mul, deriv_const,
    deriv_log, deriv_pow, deriv_sin, deriv_sub, deriv_neg, deriv_id, deriv_const, deriv_log, deriv_pow, deriv_sin,
    deriv_add, deriv_mul, deriv_const, deriv_log, deriv_pow, deriv_sin, deriv_sub, deriv_neg, deriv_id, deriv_const,
    deriv_log, deriv_pow, deriv_sin, deriv_add, deriv_mul, deriv_const, deriv_log, deriv_pow, deriv_sin,
    deriv_sub, deriv_neg, deriv_id, deriv_const]
  field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16, h_div_ne_zero_9]
  ring_nf
  <;> norm_num
  <;> field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16, h_div_ne_zero_9]
  <;> linarith
  <;> norm_num
  <;> field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16, h_div_ne_zero_9]
  <;> linarith
  <;> norm_num
  <;> field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16, h_div_ne_zero_9]
  <;> linarith
  <;> norm_num

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) + (((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)))) := by
  simp_all [deriv_add, deriv_mul, deriv_pow, deriv_zpow, deriv_const', deriv_id', deriv_log,
    deriv_sin, deriv_cos, deriv_inv, deriv_comp, deriv_add_const, deriv_const_mul]
  field_simp
  ring
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h₀ : Real.log 5 ≠ 0 := by
    apply ne_of_gt
    norm_num
  have h₁ : x ≠ 0 := by
    apply ne_of_gt
    norm_num
  have h₂ : (5 * x + 2) ≠ 0 := by
    apply ne_of_gt
    norm_num
  field_simp [*, Real.log_mul, Real.log_rpow, mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  rw [← sub_eq_zero]
  field_simp
  ring_nf

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  simp_all only [deriv_cos, mul_one, mul_neg, mul_zero, zero_add, mul_neg_one, mul_one]
  field_simp [h_log_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  have h1 : cos ((x ^ 3) * (log x / log (5:ℝ)) - (log ((5:ℝ) * x + (2:ℝ))) ^ 3) ≠ 0 := h_tan_ne_zero_1
  have h2 : log (5:ℝ) ≠ 0 := h_div_ne_zero_10
  have h3 : x ≠ 0 := h_log_ne_zero_11
  have h4 : (5:ℝ) ≠ 0 := h_log_ne_zero_13
  have h5 : (5:ℝ) * x + (2:ℝ) ≠ 0 := h_log_ne_zero_17
  field_simp [h1, h2, h3, h4, h5, Real.log_ne_zero, Real.log_ne_zero, Real.log_ne_zero,
    Real.log_ne_zero, Real.log_ne_zero]
  ring
  <;> simp_all only [mul_assoc]
  <;> apply DifferentiableAt.hasDerivAt
  <;> apply DifferentiableAt.div_const
  <;> apply DifferentiableAt.mul_const
  <;> apply DifferentiableAt.add_const
  <;> apply DifferentiableAt.sub_const
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.tan

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) := by
  have h1 : ∀ x : ℝ, x ≠ 0 → Real.log x ≠ 0 := fun x hx =>
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by linarith)
  have h2 : ∀ x : ℝ, (5 : ℝ) * x + 2 ≠ 0 → Real.log ((5 : ℝ) * x + 2) ≠ 0 := fun x hx =>
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by linarith)
  have h3 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h4 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h5 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h6 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h7 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h8 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h9 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h10 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h11 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h12 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h13 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h14 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h15 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h16 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h17 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h18 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h19 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h20 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h21 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h22 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h23 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h24 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h25 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h26 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h27 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h28 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h29 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h30 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h31 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h32 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h33 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h34 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h35 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h36 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h37 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h38 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h39 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h40 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h41 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h42 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h43 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h44 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h45 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h46 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h47 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h48 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h49 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h50 : ∀ x : ℝ, (3 : ℝ) ≠ 0 := fun x => by norm_num
  have h51 : ∀ x : ℝ, (1 : ℝ) ≠ 0 := fun x => by norm_num
  have h52 : ∀ x : ℝ, (4 : ℝ) ≠ 0 := fun x => by norm_num
  have h53 : ∀ x : ℝ, (5 : ℝ) ≠ 0 := fun x => by norm_num
  have h54 : ∀ x : ℝ, (2 : ℝ) ≠ 0 := fun x => by norm_num
  have h55 : ∀ x : ℝ, (3 : ℝ) ≠
example (x: ℝ)  (h_log_ne_zero_1: ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) - (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) / ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) - Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17]
  ring_nf
  rw [deriv_log_div_log]
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17]
  ring_nf
  <;> simp_all
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  rw [deriv_sub]
  rw [deriv_sub]
  rw [deriv_add]
  ring
  <;> apply DifferentiableAt.pow
  <;> apply DifferentiableAt.mul
  <;> apply DifferentiableAt.div
  <;> apply DifferentiableAt.add
  <;> apply DifferentiableAt.const_mul
  <;> apply DifferentiableAt.log
  <;> apply DifferentiableAt.exp
  <;> apply DifferentiableAt.const_add
  <;> apply DifferentiableAt.id
  <;> simp_all

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.exp x) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x))) := by
  simp_all only [Ne, Nat.cast_eq_zero, Nat.cast_succ, one_div, add_eq_zero_iff, mul_eq_mul_left_iff,
    mul_eq_mul_right_iff, mul_one, mul_zero, mul_neg, neg_eq_zero, zero_add, zero_sub, sub_zero,
    mul_neg_one, mul_one, sub_eq_zero, mul_right_comm, mul_left_comm]
  ring_nf
  field_simp [h_div_ne_zero_8, h_log_ne_zero_9, h_log_ne_zero_11, h_log_ne_zero_17]
  linarith

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + Real.cos (Real.log x)) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) := by
  simp_all [Real.log_div, Real.log_pow, mul_div_assoc, mul_assoc]
  field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16]
  ring
  <;> simp_all [Real.log_div, Real.log_pow, mul_div_assoc, mul_assoc]
  <;> field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16]
  <;> ring
  <;> simp_all [Real.log_div, Real.log_pow, mul_div_assoc, mul_assoc]
  <;> field_simp [h_log_ne_zero_10, h_log_ne_zero_12, h_log_ne_zero_16]
  <;> ring

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0) : deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * Real.cos (Real.log x)) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * Real.cos (Real.log x)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)))) := by
  simp [deriv_sub, deriv_mul, deriv_log, deriv_rpow_const, deriv_const_mul, deriv_comp,
    deriv_inv, deriv_add, deriv_id'', deriv_pow'', deriv_cos, deriv_sin]
  field_simp
  ring_nf

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) + (2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ)) := by
  fun_prop
  <;> simp_all [deriv_mul, deriv_log, deriv_pow, deriv_const, deriv_add, deriv_sin, deriv_sub,
    deriv_neg, deriv_exp, deriv_inv, deriv_id, deriv_pow, deriv_const, deriv_mul,
    deriv_log, deriv_pow, deriv_const, deriv_add, deriv_sin, deriv_sub, deriv_neg,
    deriv_exp, deriv_inv, deriv_id, deriv_pow, deriv_const, deriv_mul, deriv_log,
    deriv_pow, deriv_const, deriv_add, deriv_sin, deriv_sub, deriv_neg, deriv_exp,
    deriv_inv, deriv_id]
  <;> norm_num
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_8: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_9: x ≠ 0) (h_log_ne_zero_11: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) - (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2) x = (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)) - ((((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + ((Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) := by
  simp only [deriv_sub, deriv_mul, deriv_rpow_const, deriv_log, deriv_pow, deriv_add, deriv_mul,
    deriv_const, deriv_id, deriv_comp, deriv_sin, deriv_cos, deriv_inv, deriv_add, deriv_sub]
  field_simp
  ring

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  have h₀ : ∀ x ≠ 0, Real.log x / Real.log 5 ≠ 0 := fun x hx => div_ne_zero (log_ne_zero_of_pos_of_ne_one (by linarith) hx) (log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
  have h₁ : ∀ x, (5 * x + 2) ≠ 0 → Real.log (5 * x + 2) ≠ 0 := fun x hx => log_ne_zero_of_pos_of_ne_one (by linarith) hx
  have h₂ : ∀ x ≠ 0, Real.log x ≠ 0 := fun x hx => log_ne_zero_of_pos_of_ne_one (by linarith) hx
  have h₃ : ∀ x ≠ 0, (5 * x + 2) ≠ 0 → Real.log (5 * x + 2) ≠ 0 := fun x hx hx' => log_ne_zero_of_pos_of_ne_one (by linarith) hx'
  field_simp [*, log_ne_zero_of_pos_of_ne_one] at *
  ring_nf
  field_simp [*, log_ne_zero_of_pos_of_ne_one] at *
  first | assumption | ring_nf | simp_all
  <;> aesop

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = (-1:ℝ) * Real.sin ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  simp [Real.cos_eq_zero_iff]
  ring_nf
  <;> simp_all

example (x: ℝ)  (h_tan_ne_zero_1: Real.cos ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.tan ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / Real.cos ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) ^ 2 := by
  field_simp [h_tan_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17]
  rw [deriv_tan]
  field_simp [Real.cos_ne_zero_iff]
  ring_nf
  <;> simp_all [Real.cos_ne_zero_iff]
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = Real.exp ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) := by
  apply HasDerivAt.deriv
  have h₁ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => x ^ 3) (3 * x ^ 2) x := fun x hx =>
    (hasDerivAt_pow 3 x).congr_of_eventuallyEq (eventually_of_forall fun _ => rfl) (by simp [hx])
  have h₂ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.log x) (1 / x) x := fun x hx =>
    (hasDerivAt_log hx).congr_of_eventuallyEq (eventually_of_forall fun _ => rfl) (by simp [hx])
  have h₃ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.log (5 * x + 2)) (5 / (5 * x + 2)) x := fun x hx =>
    (hasDerivAt_log (by linarith)).congr_of_eventuallyEq (eventually_of_forall fun _ => rfl) (by simp [hx])
  have h₄ : HasDerivAt Real.exp (Real.exp _) _ := hasDerivAt_exp _
  have h₅ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => Real.log x / Real.log 5) (1 / (x * Real.log 5)) x := fun x hx =>
    ((hasDerivAt_log hx).div (hasDerivAt_const x (Real.log 5)) (by simp [hx])).congr_of_eventuallyEq
      (eventually_of_forall fun _ => rfl) (by simp [hx])
  have h₆ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => (Real.log (5 * x + 2)) ^ 3)
    (3 * Real.log (5 * x + 2) ^ 2 * (5 / (5 * x + 2))) x := fun x hx =>
    ((hasDerivAt_log (by linarith)).pow 3).congr_of_eventuallyEq (eventually_of_forall fun _ => rfl)
      (by simp [hx])
  have h₇ : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun x => x ^ 3 * (Real.log x / Real.log 5) *
    Real.log (5 * x + 2) ^ 3)
    (((3 * x ^ 2) * (Real.log x / Real.log 5) + (x ^ 3 * ((1 / x) * (Real.log 5 / Real.log 5)))) *
    (Real.log (5 * x + 2) ^ 3) +
    (x ^ 3 * (Real.log x / Real.log 5)) * (3 * Real.log (5 * x + 2) ^ 2 * (5 / (5 * x + 2)))) x :=
    fun x hx => (h₁ x hx).mul <| (h₅ x hx).mul (h₆ x hx)
  exact h₇ _ h_log_ne_zero_11

example (x: ℝ)  (h_log_ne_zero_1: ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ))) * (Real.log (((5:ℝ) * x + (2:ℝ)))) ^ 3) ≠ 0) (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.log ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3)) x = ((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) / ((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) := by
  apply Eq.symm
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17,
    Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17,
    Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  field_simp [h_log_ne_zero_1, h_div_ne_zero_10, h_log_ne_zero_11, h_log_ne_zero_13, h_log_ne_zero_17,
    Real.log_ne_zero, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  <;> simp_all
  <;> apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num

example (x: ℝ)  (h_div_ne_zero_9: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_10: x ≠ 0) (h_log_ne_zero_12: (5:ℝ) ≠ 0) (h_log_ne_zero_16: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 + (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))))) + (Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) := by
  simp [*, deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id, deriv_log, deriv_exp,
    mul_comm, mul_assoc, mul_left_comm, mul_add, mul_sub, add_mul, sub_mul]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one, mul_comm, mul_assoc, mul_left_comm, mul_add, mul_sub,
    add_mul, sub_mul]
  ring
  <;> linarith

example (x: ℝ)  (h_div_ne_zero_10: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_11: x ≠ 0) (h_log_ne_zero_13: (5:ℝ) ≠ 0) (h_log_ne_zero_17: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ (x ^ 3) * (Real.log x / Real.log (5:ℝ)) * (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3 * (Real.exp x) * (x ^ 2 + (3:ℝ))) x = (((((((((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) * (Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3)) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))))) * Real.exp x) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3) * Real.exp x)) * (x ^ 2 + (3:ℝ))) + (((x ^ 3) * (Real.log x / Real.log (5:ℝ)) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 3 * Real.exp x) * ((2:ℝ) * x)) := by
  simp_all only [one_div, mul_assoc, mul_comm, mul_left_comm, mul_one, mul_div_assoc, mul_div_cancel_left]
  field_simp
  ring
  <;> norm_num
  <;> apply Real.log_ne_zero_of_pos_of_ne_one
  <;> norm_num
  <;> apply Real.log_ne_zero_of_pos_of_ne_one
  <;> norm_num
  <;> apply Real.log_ne_zero_of_pos_of_ne_one
  <;> norm_num
  <;> apply Real.log_ne_zero_of_pos_of_ne_one
  <;> norm_num

