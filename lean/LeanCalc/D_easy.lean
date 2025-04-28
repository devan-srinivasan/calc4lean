import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real

-- 107: y = (tan x - e^x) / sqrt(x)
example (x0 : ℝ) (h : 0 < x0) (h2: cos x0 ≠ 0) :
    deriv (λ x ↦ (tan x - exp x) / sqrt x) x0 =
    ( exp x0 * (1 - 2*x0) - tan x0 + 2*x0*(1/cos x0)^2 ) / (2 * x0^(3/2)):= by
  rw [deriv_div]
  rw [deriv_sub]
  rw [deriv_tan]
  rw [Real.deriv_exp]
  rw [deriv_sqrt]
  rw [deriv_id'']
  field_simp [h, h2]
  nth_rewrite 2 [← mul_assoc]
  nth_rewrite 3 [mul_comm]
  nth_rewrite 2 [← mul_assoc]
  -- rw [mul_self_sqrt h]
  sorry

-- 137: y = 2^x * cos x
example (x0 : ℝ) :
    deriv (λ x ↦ (2 : ℝ)^x * cos x) x0 = x0 := by
  rw [deriv_mul]
  rw [Real.deriv_cos]
  sorry

-- 152: y = arctan(sqrt(x))
example (x0 : ℝ) (h : 0 ≤ x0) :
    deriv arctan (sqrt x0) = 1 / (1 + x0) := by
  rw [Real.deriv_arctan]
  ring_nf
  rw [sq_sqrt]
  exact h

-- 167: y = cos(ln x)
example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ cos (log x)) x0 = -sin (log x0) / x0 := by
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [Real.deriv_cos]
  rw [Real.deriv_log]
  field_simp
  exact Real.differentiableAt_cos
  exact Real.differentiableAt_log (ne_of_gt h)

-- 183: y = ln(x + sqrt(x^2 + 1))
example (x0 : ℝ) :
    deriv (λ x ↦ log (x + sqrt (x^2 + 1))) x0 = 1/√(x0^2 + 1) := by
    rw [← Function.comp_def]
    rw [deriv_comp]
    rw [deriv_log]
    rw [deriv_add]
    rw [deriv_id'']
    nth_rewrite 2 [← Function.comp_def]
    rw [deriv_comp]
    rw [deriv_sqrt]
    rw [deriv_id'']
    rw [deriv_add]
    rw [deriv_pow]
    rw [deriv_const]
    ring_nf
    field_simp
    sorry

-- 197: y = sin^3(x^2) * arccos(sqrt x)
example (x0 : ℝ) (h : 0 < x0 ∧ x0 ≤ 1) :
    deriv (λ x ↦ (sin (x^2))^3 * arccos (sqrt x)) x0 =
    6*x0*(sin ( x0^2 ))^2 * arccos (sqrt x0) * cos (x0^2) - (sin ( x0^2 ))^3 / (2 * sqrt ( x0 - x0^2)) := by
    rw [deriv_mul]
    rw [← Function.comp_def]
    rw [deriv_pow'']
    rw [← Function.comp_def]
    rw [deriv_comp]
    rw [Real.deriv_sin]
    rw [deriv_pow'']
    rw [deriv_id'']
    rw [deriv_comp]
    rw [deriv_arccos]
    rw [deriv_sqrt]
    ring_nf
    field_simp [h]
    -- almost there, what's wrong?
    sorry


-- 212: y = cos²(2x) / tan(x²)
example (x0 : ℝ) (h : cos (2 * x0) ≠ 0 ∧ tan (x0^2) ≠ 0) :
    deriv (λ x ↦ (cos (2 * x))^2 / tan (x^2)) x0 =
    -2 * cos (2*x0) * (x0 * cos (2 * x0) * (1/(sin ( x0^2 ))^2)) + 2 * sin (2*x0) / tan (x0^2):= by
  rw [deriv_div]
  rw [deriv_pow'']
  rw [← Function.comp_def]
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [deriv_comp]
  rw [Real.deriv_cos]
  rw [Real.deriv_tan]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [tan_eq_sin_div_cos]
  ring_nf
  field_simp
  sorry


-- 242: y = e^x * (x^2 + 3)
example (x0 : ℝ) :
    deriv (λ x ↦ exp x * (x^2 + 3)) x0 = (exp x0) * x0^2 + (exp x0) * 2 * x0 + 3 * exp x0 := by
  rw [deriv_mul]
  rw [Real.deriv_exp]
  rw [deriv_add]
  rw [deriv_pow'']
  rw [deriv_const]
  ring_nf
  field_simp
  exact differentiableAt_id
  exact differentiableAt_pow 2
  exact differentiableAt_const 3
  exact differentiableAt_exp
  exact DifferentiableAt.add (differentiableAt_pow 2) (differentiableAt_const 3)


-- 677a: y = x^(5/6) + 7
example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ x^(5/6 : ℝ) + 7) x0 = 5 / (6 * x0 ^ (1/6)) := by
  -- rw [Real.deriv_rpow_const]
  sorry

-- 677b: y = (3x^3)/(x^(2/5)) - 9/(x^(2/3)) + 2 * x^(5/6)
example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ (3 * x^3 / x^(2/5 : ℝ)) - 9 / x^(2/3 : ℝ) + 2 * x^(5/6 : ℝ)) x0 =
    x0 := by
  sorry

-- 677c: y = x * x^(1/3) + 1/sqrt(x) + 0.1 * x^10
example (x0 : ℝ) (h : 0 < x0) :
    deriv (λ x ↦ x * x^(1/3 : ℝ) + 1 / sqrt x + 0.1 * x^10) x0 =
    x0 := by
  sorry

-- 677d: y = (2x^3 + sqrt(5)) * 7^x
example (x0 : ℝ) :
    deriv (λ x ↦ (2 * x^3 + sqrt 5) * (7 : ℝ)^x) x0 =
    x0 := by
  sorry

-- 677e: y = x / (2 - cos x) - x^3 / sqrt(7)
example (x0 : ℝ) (h : cos x0 ≠ 2) :
    deriv (λ x ↦ x / (2 - cos x) - x^3 / sqrt 7) x0 =
    x0 := by
  sorry

-- 677f: y = 5 / sin x + ln x / x^2
example (x0 : ℝ) (h : 0 < x0 ∧ sin x0 ≠ 0) :
    deriv (λ x ↦ 5 / sin x + log x / x^2) x0 =
    x0 := by
  sorry
