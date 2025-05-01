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

-- theorem deriv_const_pow {a x: ℝ} (ha: a > 0):
--   (deriv fun x : ℝ => a ^ x) = fun x => a ^ x * log x := by sorry

-- 137: y = 2^x * cos x
example (x0 : ℝ) :
    deriv (λ x ↦ (2 : ℝ)^x * cos x) x0 = x0 := by
  rw [deriv_mul]
  rw [Real.deriv_cos]
  -- rw [Real.deriv_rpow_const]
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
example (x0 : ℝ) (h2 : tan (x0^2) ≠ 0) (h4 : (cos (x0^2))^2 ≠ 0) :
    deriv (λ x ↦ (cos (2 * x))^2 / tan (x^2)) x0 =
      -4 * cos (2*x0) * sin (2 * x0) / tan (x0 ^ 2) - ((cos (2 * x0))^2 * 2 * x0 / ((tan (x0^2))^2 * (cos (x0^2)^2))):= by
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
  field_simp [h2, h4]

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
  field_simp
  have two_sub_cos_ne_zero: 2 - cos x0 ≠ 0 := by
    by_contra h2_contra
    have h2_contra_a: cos x0 = 2 := by linarith
    contradiction
  have lhs: ((2 - cos x0 - x0 * sin x0) * 7 / (2 - cos x0) ^ 2 - 3 * x0 ^ 2 * √7) * √7 =
    (((2 - cos x0) - (x0 * sin x0)) / (2 - cos x0) ^ 2 * 7 * √7 - 3 * x0 ^ 2 * √7 * √7)  := by ring
  have rhs:  ((1 / (2 - cos x0) - x0 * sin x0 / (2 - cos x0) ^ 2) * √7 - 3 * x0 ^ 2) * 7 =
     ((1 / (2 - cos x0) - x0 * sin x0 / (2 - cos x0) ^ 2) * 7 * √7 - 3 * x0 ^ 2 * 7) := by ring
  rw [lhs]
  rw [rhs]
  have lhs_simplify: (2 - cos x0 - x0 * sin x0) / (2 - cos x0) ^ 2 =
     (2 - cos x0) / ((2 - cos x0) * (2 - cos x0)) - (x0 * sin x0) / (2 - cos x0) ^ 2 := by
     ring
  rw [lhs_simplify]
  have lhs_cancel: (2 - cos x0) / ((2 - cos x0) * (2 - cos x0)) = 1 / (2 - cos x0) := by
    field_simp [two_sub_cos_ne_zero]
  rw [lhs_cancel]
  have sqrt7: (7: ℝ) = √(7: ℝ) * √(7: ℝ) := by
    nth_rewrite 1 [← sq_sqrt (by norm_num : 0 ≤ (7 : ℝ))]
    field_simp
  nth_rewrite 7 [sqrt7]
  ring
  exact differentiableAt_const 2
  exact differentiableAt_cos
  exact differentiableAt_pow 3
  exact differentiableAt_const √7
  apply ne_of_gt (sqrt_pos.mpr (by norm_num))
  exact differentiableAt_id
  exact DifferentiableAt.sub (differentiableAt_const 2) (differentiableAt_cos)
  by_contra h2_contra
  have h2_contra_a: cos x0 = 2 := by linarith
  contradiction
  have two_sub_cos_ne_zero: 2 - cos x0 ≠ 0 := by
    by_contra h2_contra
    have h2_contra_a: cos x0 = 2 := by linarith
    contradiction
  exact DifferentiableAt.div (differentiableAt_id) (DifferentiableAt.sub (differentiableAt_const 2) (differentiableAt_cos)) (two_sub_cos_ne_zero)
  exact DifferentiableAt.div (differentiableAt_pow 3) (differentiableAt_const √7) (ne_of_gt (sqrt_pos.mpr (by norm_num)))

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

-- 692: $y=\\sin ^{2}(2 x-1)$
example (x0 : ℝ) : deriv (λ x ↦ (sin (2 * x - 1))^2) x0 = 4 * sin (2 * x0 - 1) * cos (2 * x0 - 1) := by
  rw [deriv_pow'']
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [Real.deriv_sin]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const 1
  exact differentiableAt_sin
  exact DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const 1)
  exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const 1))

-- 707: $y=x^{3} \\log _{5} x$
example (x0 : ℝ) (hx : 0 < x0) : deriv (λ x ↦ x ^ 3 * (Real.log x / Real.log 5)) x02
  = 3 * x0 ^ 2 * Real.log x0 / Real.log 5 + x0 ^ 2 / Real.log 5 := by
  rw [deriv_mul]
  rw [deriv_pow]
  rw [deriv_div]
  rw [Real.deriv_log]
  rw [deriv_const]
  field_simp [hx]
  ring
  exact differentiableAt_log (ne_of_gt hx)
  exact differentiableAt_const (log 5)
  apply log_ne_zero.mpr (by norm_num)
  exact differentiableAt_pow 3
  exact DifferentiableAt.div (differentiableAt_log (ne_of_gt hx)) (differentiableAt_const (log 5)) (log_ne_zero.mpr (by norm_num))

-- 737: $y=x \\tan x+\\cot x$
example (x0 : ℝ) (hx1 : Real.cos x0 ≠ 0) (hx2 : Real.sin x0 ≠ 0) :
  deriv (λ x ↦ x * Real.tan x + 1 / Real.tan x) x0
  = Real.tan x0 + x0 / Real.cos x0 ^ 2 - 1 / Real.sin x0 ^ 2 := by
  rw [deriv_add]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_tan]
  rw [deriv_div]
  rw [deriv_const]
  rw [deriv_tan]
  nth_rewrite 3 [Real.tan_eq_sin_div_cos]
  have simplify_lhs: (0 * tan x0 - 1 * (1 / cos x0 ^ 2)) / (sin x0 / cos x0) ^ 2 = - cos x0 ^ 2 / (cos x0 ^ 2 * sin x0 ^ 2) := by
    field_simp [hx1, hx2]
  rw [simplify_lhs]
  have cancellation: cos x0 ^ 2 / (cos x0 ^ 2 * sin x0 ^ 2) = 1 / sin x0 ^ 2 := by field_simp
  rw [← cancellation]
  ring
  exact differentiableAt_const 1
  exact differentiableAt_tan.mpr hx1
  rw [Real.tan_eq_sin_div_cos]
  apply div_ne_zero hx2 hx1
  exact differentiableAt_id
  exact differentiableAt_tan.mpr hx1
  exact DifferentiableAt.mul (differentiableAt_id) (differentiableAt_tan.mpr hx1)
  exact DifferentiableAt.div (differentiableAt_const 1) (differentiableAt_tan.mpr hx1) (by rw [Real.tan_eq_sin_div_cos]; exact div_ne_zero hx2 hx1)

-- 767: $y=\\ln ^{3}(5 x+2)$
example (x0 : ℝ) (hx : 0 < 5 * x0 + 2) :
  deriv (λ x ↦ (Real.log (5 * x + 2)) ^ 3) x0
  = 15 * (Real.log (5 * x0 + 2)) ^ 2 / (5 * x0 + 2) := by
  rw [deriv_pow'']
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact differentiableAt_log (ne_of_gt hx)
  exact DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)) (ne_of_gt hx)

-- 812: $y=\\tan 5 x$
example (x0 : ℝ) (hx : Real.cos (5 * x0) ≠ 0) :
  deriv (λ x ↦ Real.tan (5 * x)) x0
  = 5 / cos (5 * x0) ^ 2 := by
  rw [← Function.comp_def]
  rw [deriv_comp]
  rw [deriv_tan]
  rw [deriv_const_mul]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_tan.mpr hx
  exact DifferentiableAt.const_mul differentiableAt_id _

-- 842: $y=x^{x}$
example (x0 : ℝ) (hx : 0 < x0) :
  deriv (λ x ↦ x ^ x) x0
  = x0 ^ x0 * (Real.log x0 + 1) := by
  -- nth_rewrite 1 [rpow_def_of_pos hx]
  sorry

-- 857: r=(\\sin \\varphi)^{\\cos 2 \\varphi}

-- 872: z=\\frac{4 x^{2}}{\\sqrt[5]{(2-x)^{3}}}

-- 887: Show that the function $y=\\cos 2 x$ satisfies the differential equation $y^{\\prime \\prime}+4 y=0$.
