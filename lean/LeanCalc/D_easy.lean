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
    ((1 / (cos x0)^2 - exp x0) * √x0 - (tan x0 - exp x0) / (2 * √x0))/x0 := by
    -- ( exp x0 * (1 - 2*x0) - tan x0 + 2*x0/(cos x0)^2 ) / (2 * x0^((3:ℝ)/(2:ℝ))):= by
  rw [deriv_div]
  rw [deriv_sub]
  rw [deriv_tan]
  rw [Real.deriv_exp]
  rw [deriv_sqrt]
  rw [deriv_id'']
  field_simp [h, h2]
  exact differentiableAt_id
  exact (ne_of_gt h)
  apply differentiableAt_tan.mpr (h2)
  exact differentiableAt_exp
  exact DifferentiableAt.sub (differentiableAt_tan.mpr (h2)) differentiableAt_exp
  sorry
  apply ne_of_gt (sqrt_pos.mpr (h))

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
example (x0 : ℝ):
    deriv (λ x ↦ log (x + √(x^2 + 1))) x0 = 1/√(x0^2 + 1) := by
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
    field_simp
    -- am i tripping or can you not prove this without assuming x0 != 1/2 - root(5)/2

-- SOME OTHER WORK I DID THAT MAY BE MEANINGLESS AHHH
    -- field_simp
    -- have reorder_numerator: (2 * √(x0 ^ 2 + 1) + 2 * x0) * √(x0 ^ 2 + 1) =
    --   (2 * (√(x0 ^ 2 + 1) + x0) * √(x0 ^ 2 + 1)) := by
    --   ring
    -- have reorder_denominator: ((x0 + √(x0 ^ 2 + 1)) * (2 * √(x0 ^ 2 + 1))) =
    --   (2 * (√(x0 ^ 2 + 1) + x0)) * √(x0 ^ 2 + 1) := by
    --   ring
    -- rw [reorder_numerator]
    -- rw [reorder_denominator]
    -- have h1 : (2 * (√(x0 ^ 2 + 1) + x0)) * √(x0 ^ 2 + 1) ≠ 0 := by
    --   have rhs: √(x0 ^ 2 + 1) ≠ 0 := by
    --     have inside_positive: x0 ^ 2 + 1 > 0 := by
    --       apply lt_add_of_le_of_pos (sq_nonneg x0) (zero_lt_one)
    --     have rhs_positive: √(x0 ^ 2 + 1) > 0 := by
    --       apply sqrt_pos.mpr (inside_positive)
    --     apply ne_of_gt (rhs_positive)
    --   have lhs: 2 * (√(x0 ^ 2 + 1) + x0) ≠ 0 := by
    --     have rhs_neq_zero: √(x0 ^ 2 + 1) + x0 ≠ 0 := by
    --       by_contra rhs_eq_zero

    --     apply mul_ne_zero (two_ne_zero) (rhs_neq_zero)
    --   apply mul_ne_zero (lhs) (rhs)
    -- field_simp [h1]


-- 197: y = sin^3(x^2) * arccos(sqrt x)
example (x0 : ℝ) (h1 : 0 < x0) (h2: x0 < 1) :
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
    field_simp [h1, h2]
    have lhs: 3 * sin (x0 ^ 2) ^ 2 * (cos (x0 ^ 2) * (2 * x0)) * arccos √x0 + -sin (x0 ^ 2) ^ 3 / (√(1 - x0) * (2 * √x0))
      = 6 * x0 * sin (x0 ^ 2) ^ 2 * arccos √x0 * cos (x0 ^ 2) - sin (x0 ^ 2) ^ 3 / (2 * √(1 - x0) * √x0) := by ring
    rw [lhs]
    have sqrt_denom_part: √(1 - x0) * √x0 = √(x0 - x0 ^ 2) := by
      rw [← sqrt_mul]
      ring
      simp [h2]
    rw [← sqrt_denom_part]
    ring
    exact differentiableAt_id
    exact (ne_of_gt h1)
    -- exact differentiableOn_arccos
    sorry
    sorry
    exact differentiableAt_id

-- 212: y = cos²(2x) / tan(x²)
example (x0 : ℝ) (h1 : cos (2 * x0) ≠ 0) (h2: tan (x0^2) ≠ 0) :
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
  field_simp [h1, h2]
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
    deriv (λ x ↦ x / (2 - cos x) - x^3 / sqrt 7) x0 = 1/(2 - cos x0) - (x0 * sin x0)/((2 - cos x0)^2) - (3 * x0^2)/√7:= by
  rw [deriv_sub]
  rw [deriv_div]
  rw [deriv_div]
  rw [deriv_id'']
  rw [deriv_sub]
  rw [deriv_const]
  rw [Real.deriv_cos]
  rw [deriv_pow]
  rw [deriv_const]
  field_simp [h]
  -- these are equivalent, just need to do some algebra



-- 677f: y = 5 / sin x + ln x / x^2
example (x0 : ℝ) (h : 0 < x0) (h2: sin x0 ≠ 0) :
    deriv (λ x ↦ 5 / sin x + log x / x^2) x0 =
    -5 * cos x0 / (sin x0)^2 + 1 / x0^3 - 2 * log x0 / x0^3 := by
  rw [deriv_add]
  rw [deriv_div]
  rw [deriv_const]
  rw [Real.deriv_sin]
  rw [deriv_div]
  rw [deriv_log]
  rw [deriv_pow]
  field_simp [h, h2]
  ring_nf
  exact differentiableAt_log (ne_of_gt h)
  exact differentiableAt_pow 2
  have hx2_pos : 0 < x0 ^ 2 := pow_pos h 2
  have hx2_ne_zero : x0 ^ 2 ≠ 0 := ne_of_gt hx2_pos
  exact hx2_ne_zero
  exact differentiableAt_const 5
  exact differentiableAt_sin
  exact h2
  exact DifferentiableAt.div (differentiableAt_const 5) (differentiableAt_sin) (h2)
  have hx2_pos : 0 < x0 ^ 2 := pow_pos h 2
  have hx2_ne_zero : x0 ^ 2 ≠ 0 := ne_of_gt hx2_pos
  exact DifferentiableAt.div (differentiableAt_log (ne_of_gt h)) (differentiableAt_pow 2) (hx2_ne_zero)
