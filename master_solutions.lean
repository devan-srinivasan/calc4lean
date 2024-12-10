import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

import «Calc4lean».LLMStep

open Real


/-
--------------------------------------------------------------------------
Remember the protocol to write a new solution
  - First check if the original problem is aligning properly with the formalization
    i.e -- Original Problem: y = """2{t^4} - 10{t^2} + 13t"""
           example (x0: ℝ): deriv (λ t ↦ """2*t^4 - 10*t^2 + 13*t""") x0 = 2*x0^3 + x0*(6*x0^2 - 10) - 10*x0 + 13 := by
    the text inside triple quotes should match
  - Figure out the formulas you would need to solve the derivative
  - Find that in the master file and apply those.
  - If you make partial progress in a problem, but stuck somewhere, mark them as sorry.
    Comment on the problem "TO BE CHECKED BY BINDU"
    I will take a look later.
--------------------------------------------------------------------------
-/


-- Polynomial Solution 1
-- Original Problem: f( x ) = 6{x^3} - 9x + 4
example (x0: ℝ): deriv (λ x ↦ 6*x^3 - 9*x + 4) x0 = 18*x0^2 - 9 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _

-- Polynomial Solution 2
-- Original Problem: y = 2{t^4} - 10{t^2} + 13t
example (x0: ℝ): deriv (λ t ↦ 2*t^4 - 10*t^2 + 13*t) x0 = 2*x0^3 + x0*(6*x0^2 - 10) - 10*x0 + 13 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_pow]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
  exact DifferentiableAt.const_mul differentiableAt_id _


-- Solution for exp and log and function of type f(x)*g(x)
-- Original Problem: f( x ) = e^x * ln(x)
example (x0 : ℝ) (h : 0 < x0) : deriv (fun x => exp x * log x) x0 = exp x0 / x0 + exp x0 * log x0 := by
  -- Apply the product rule
  rw [deriv_mul]
  -- Derivative of log(x), under the condition x > 0
  rw [Real.deriv_log]
  -- Simplify the resulting expression
  rw [Real.deriv_exp]
  ring
  exact differentiableAt_exp
  exact differentiableAt_log (ne_of_gt h)


-- A solution that also prooves that the multiplication is differentiable at a point
-- Original Problem: g( y ) = ( {y - 4} )( {2y + {y^2}} )
example (x0: ℝ): deriv (λ y ↦ y*(y - 4)*(y + 2)) x0 = x0*(x0 - 4) + x0*(x0 + 2) + (x0 - 4)*(x0 + 2) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_sub]
  rw [deriv_id'']
  rw [deriv_const]
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_id
  exact DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)
  exact DifferentiableAt.mul differentiableAt_id (DifferentiableAt.sub differentiableAt_id (differentiableAt_const _))
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)

-- A solution that also prooves that the multiplication is differentiable at a point
-- Original Problem: g( y ) = ( {y - 4} )( {2y + {y^2}} )
example (x0: ℝ): deriv (λ y ↦ y*(y - 4)*(y + 2)) x0 = x0*(x0 - 4) + x0*(x0 + 2) + (x0 - 4)*(x0 + 2) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_sub]
  rw [deriv_id'']
  rw [deriv_const]
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_id
  exact differentiableAt_id.sub (differentiableAt_const _)
  exact differentiableAt_id.mul (DifferentiableAt.sub differentiableAt_id (differentiableAt_const _))
  exact differentiableAt_id.add (differentiableAt_const _)


-- Example with f(x)/g(x) format
-- Original Problem: g( x ) = \frac{{6{x^2}}}{{2 - x}}
example (x0: ℝ) (h: x0 - 2 ≠ 0): deriv (λ x ↦ -6*x^2/(x - 2)) x0 = 6*x0^2/(x0 - 2)^2 - 12*x0/(x0 - 2) := by
  rw [deriv_div]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_sub]
  rw [deriv_id'']
  rw [deriv_const]
  field_simp [h]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)
  exact h
  --llmstep ""
  --exact fun h' => h (sub_eq_zero.mp h')


-- Original Problem: f( x ) = {( {5 - 3{x^2}} )^7}\sqrt {6{x^2} + 8x - 12}
example (x0: ℝ): deriv (λ x ↦ -(3*x^2 - 5)^7) x0 = -42*x0*(3*x0^2 - 5)^6 := by
  have h_comp: deriv (λ x ↦ -(3*x^2 - 5)^7) x0 = deriv ((λ x ↦ -x^7) ∘ (λ x ↦ 3*x^2 - 5)) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv.neg]
  rw [deriv_pow]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact differentiableAt_const _
  exact DifferentiableAt.neg (differentiableAt_pow _)
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (differentiableAt_const _)


-- Original Problem: F( y ) = \ln ( {1 - 5{y^2} + {y^3}} )
example (x0: ℝ) (h: x0^3 - 5*x0^2 + 1 > 0): deriv (λ y ↦ (log (y^3 - 5*y^2 + 1))) x0 = (3*x0^2 - 10*x0)/(x0^3 - 5*x0^2 + 1) := by
  have h_comp: deriv (λ y ↦ (log (y^3 - 5*y^2 + 1))) x0 = deriv ((λ y ↦ log y) ∘ (λ y ↦ (y^3 - 5*y^2 + 1))) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
  exact differentiableAt_const _
  exact differentiableAt_log (ne_of_gt h)
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)) (differentiableAt_const _)


example (x0: ℝ) : deriv (λ y ↦ y^3 - 5*y^2 + 1) x0 = 3*x0^2 - 10*x0 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
  exact differentiableAt_const _


example (x0: ℝ) (h: x0 > 0) : deriv (λ y ↦ log y) x0 = 1/x0 := by
  rw [deriv_log]
  ring


-- Original Problem: g( z ) = 4{z^7} - 3{z^{ - 7}} + 9z
example (x0: ℝ) (h: x0 ≠ 0): deriv (λ z ↦ 4*z^7 + 9*z - 3/z^7) x0 = 28*x0^6 + 9 + 21/x0^8 := by
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_div]
  rw [deriv_const]
  rw [deriv_pow]
  field_simp [h]
  ring
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact pow_ne_zero _ h
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_id) _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_id) _)
  exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_pow _) (pow_ne_zero _ h)


-- Original Problem: g( z ) = 4{z^7} - 3{z^{ - 7}} + 9z
example (x0: ℝ) (h: x0 ≠ 0): deriv (λ z ↦ 4*z^7 + 9*z - 3*z^(-7:ℤ)) x0 = 28*x0^6 + 9 + 21*x0^(-8:ℤ) := by
  rw [deriv_sub]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const_mul]
  rw [deriv_zpow]
  ring
  exact (differentiableAt_zpow.mpr (Or.inl h))
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_id) _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_id) _)
  exact DifferentiableAt.const_mul ((hasDerivAt_zpow _ _ (Or.inl h)).differentiableAt) _


-- Original Problem: f( x ) = {( {5 - 3{x^2}} )^7}\sqrt {6{x^2} + 8x - 12}
example (x0: ℝ) (h: 6*x0^2 + 8*x0 - 12 > 0): deriv (λ x ↦ -(3*x^2 - 5)^7*(sqrt (6*x^2 + 8*x - 12))) x0 =
  -(2*(3*x^2 - 5)^6 * (135*x^3 + 174*x^2 - 267*x - 10))/(sqrt (6*x^2 + 8*x - 12)) := by
  -- rw [deriv_mul]
  -- have h_comp: deriv (λ x ↦ -(3*x^2 - 5)^7) x0 = deriv ((λ x ↦ -x^7) ∘ (λ x ↦ 3*x^2 - 5)) x0 := by rfl
  -- rw [h_comp]
  -- rw [deriv_comp]
  -- rw [deriv.neg]
  -- rw [deriv_pow]
  -- rw [deriv_sub]
  -- rw [deriv_const_mul]
  -- rw [deriv_pow]
  -- rw [deriv_const]
  -- have h_comp: deriv (λ x ↦ sqrt (6*x^2 + 8*x - 12)) x0 = deriv ((λ x ↦ sqrt x) ∘ (λ x ↦ 6*x^2 + 8*x - 12)) x0 := by rfl
  -- rw [h_comp]
  -- rw [deriv_comp]
  -- rw [deriv_sqrt]
  -- rw [deriv_sub]
  -- rw [deriv_add]
  -- rw [deriv_const_mul]
  -- rw [deriv_pow]
  -- rw [deriv_const_mul]
  -- rw [deriv_id'']
  -- rw [deriv_const]
  sorry


example (x0: ℝ) (h: x0 ≠ 0): deriv (λ y ↦ 12 + 8/y^2 - 9/y^3 + y^(-4: ℤ)) x0 = -16/x0^3 + 27/x0^4 - 4/x0^5 := by
  -- rw [deriv_add]
  -- rw [deriv_sub]
  -- rw [deriv_add]
  -- rw [deriv_zpow]
  -- rw [deriv_const]
  -- rw [deriv_div]
  -- rw [deriv_const]
  -- rw [deriv_pow]
  -- simp
  -- rw [deriv_div]
  -- rw [deriv_const]
  -- rw [deriv_pow]
  -- simp
  -- field_simp [h]
  -- ring
  sorry

-- Original Problem: f(x)=x^2 \ln (x+6)
example (x0: ℝ) (h: x0 + 6 ≠ 0): deriv (λ x ↦ x^2*(log (x + 6))) x0 = x0^2/(x0 + 6) + 2*x0*(log (x0 + 6)) := by
  rw [deriv_mul]
  rw [deriv_pow]
  have h_comp: deriv (λ x ↦ log (x + 6)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x + 6)) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  field_simp [h]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_log h
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)
  exact differentiableAt_pow _
  exact DifferentiableAt.comp x0 (differentiableAt_log h) (DifferentiableAt.add differentiableAt_id (differentiableAt_const _))


example (x0: ℝ) (h: x0^2 - 1 ≠ 0): deriv (λ x ↦ (x + 1)*(log (x^2 - 1))) x0 = 2*x0*(x0 + 1)/(x0^2 - 1) + (log (x0^2 - 1)) := by
  rw [deriv_mul]
  have h_comp: deriv (λ x ↦ log (x^2 - 1)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x^2 - 1)) x0 := by rfl
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const]
  field_simp [h]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact differentiableAt_log h
  exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_const _)
  exact differentiableAt_id
  exact differentiableAt_const _
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)
  exact DifferentiableAt.comp x0 (differentiableAt_log h) (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_const _))


  example (x0: ℝ) (h: x0 ≠ 0): deriv (λ x ↦ (4*x^2 - 7*x + 8)/x) x0 = 4 - 8/x0^2 := by
    rw [deriv_div]
    rw [deriv_add]
    rw [deriv_sub]
    rw [deriv_const_mul]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_id'']
    rw [deriv_const]
    field_simp [h]
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.const_mul (differentiableAt_pow _) _
    exact DifferentiableAt.const_mul (differentiableAt_id) _
    exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_id) _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_id) _)) (differentiableAt_const _)
    exact differentiableAt_id
    exact h


  example (x0: ℝ) (h: x0^5 > 0): deriv (λ t ↦ t^2*(log (t^5))) x0 = 2*x0*(log (x0^5)) + 5*x0 := by
    rw [deriv_mul]
    rw [deriv_pow]
    have h_comp: deriv (λ x ↦ (log (x^5))) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x^5)) x0 := by rfl
    rw [h_comp]
    rw [deriv_comp]
    rw [deriv_log]
    rw [deriv_pow]
    field_simp [h]
    ring
    exact differentiableAt_log (ne_of_gt h)
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.log (differentiableAt_pow _) (ne_of_gt h)


-- Original Problem: f(x) = \log_7 (2x-3)
example (x0: ℝ) (h : 2*x0 - 3 > 0): deriv (λ x ↦ (log (2*x - 3))/(log 7)) x0 = 2/((2*x0 - 3)*(log 7)) := by
  rw [deriv_div]
  have h_comp: deriv (λ x ↦ log (2*x - 3)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ (2*x - 3))) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_log]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  rw [deriv_const]
  field_simp [h]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul (differentiableAt_id) _
  exact differentiableAt_const _
  exact differentiableAt_log (ne_of_gt h)
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_id) _) (differentiableAt_const _)
  exact DifferentiableAt.comp x0 (differentiableAt_log (ne_of_gt h)) (DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_id) _) (differentiableAt_const _))
  exact differentiableAt_const _
  exact ne_of_gt (log_pos (by norm_num))

example : log 7 > 0 := by
  exact log_pos (by norm_num)
  --exact log_pos (by linarith)
  -- apply log_pos
  -- norm_num

-- Original Problem: f(x) = x(x+1)^4
example (x0: ℝ): deriv (λ x ↦ x*(x + 1)^4) x0 = 4*x0*(x0 + 1)^3 + (x0 + 1)^4 := by
  rw [deriv_mul]
  rw [deriv_id'']
  have h_comp: deriv (λ x ↦ (x + 1)^4) x0 = deriv ((λ x ↦ x ^ 4) ∘ (λ x ↦ x + 1)) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_pow]
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact DifferentiableAt.add (differentiableAt_id) (differentiableAt_const _)
  exact differentiableAt_id
  exact DifferentiableAt.comp x0 (differentiableAt_pow _) (DifferentiableAt.add (differentiableAt_id) (differentiableAt_const _))


example (x0 : ℝ) (h : x0 ≠ 0) : deriv (fun x ↦ x^(2/3 :ℝ)) x0 = (2/3)*x^((2/3)-1) := by
  rw [deriv_rpow_const (Or.inl h)]
  sorry

example (x0 : ℝ) (h : x0 ≠ 0) : deriv (λ x ↦ x^(2/3 :ℝ)) x0 = (2/3)*x^((2/3)-1) := by
  rw [deriv_rpow_const (Or.inl h)]
  sorry

example (x0 : ℝ) (h : x0 > 0) : deriv (λ x ↦ x^(2/3 :ℝ)) x0 = (2/3)*x0^((2/3 :ℝ)-1) := by
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]

example (x0: ℝ) (h: x0 > 0): deriv (λ x ↦ x^(2/3 :ℝ)) x0 = (2 :ℝ)/((3:ℝ)*x0^(1/3:ℝ)) := by
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
  field_simp [h]
  ring
  norm_num
  rw [←rpow_add h (-(1/3)) (1/3)]
  simp [add_neg_cancel_right, rpow_zero]

example (x0: ℝ) (h: x0 > 0): deriv (λ x ↦ x^(2/3 :ℝ)) x0 = (2 :ℝ)/(3*x0^(1/3:ℝ)) := by
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
  field_simp [h]
  ring
  norm_num
  rw [←rpow_add h]
  simp [add_neg_cancel_right, rpow_zero]


example (x0: ℝ)(h: x0 > 0): deriv (λ t ↦ 8*t^(1/4:ℝ)) x0 = (2:ℝ)/x0^(3/4:ℝ) := by
  rw [deriv_const_mul]
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
  field_simp [h]
  ring
  norm_num
  rw [←rpow_add h]
  simp [add_neg_cancel_right, rpow_zero]
  exact DifferentiableAt.rpow_const differentiableAt_id (Or.inl (ne_of_gt h))


-- example (x0: ℝ) (h: x0 ≠ 0): deriv (λ y ↦ 12 + 8/y^2 - 9/y^3 + y^(-4: ℤ)) x0 = -16/x0^3 + 27/x0^4 - 4/x0^5 := by
--   rw [deriv_add]
--   rw [deriv_sub]
--   rw [deriv_add]
--   rw [deriv_const]
--   rw [deriv_div]
--   rw [deriv_const]
--   rw [deriv_pow]
--   rw [deriv_div]
--   rw [deriv_const]
--   rw [deriv_pow]
--   rw [deriv_zpow]
--   field_simp [h]
--   ring_nf
--   -- norm_num
--   -- rw [←zpow_neg]
--   rw [←zpow_add]
--   sorry

-- example (x0 : ℝ) (h : x0 ≠ 0) :
--     deriv (λ y ↦ 12 + 8 / y ^ 2 - 9 / y ^ 3 + y ^ (-4 : ℤ)) x0 =
--     -16 / x0 ^ 3 + 27 / x0 ^ 4 - 4 / x0 ^ 5 :=
-- by
--   rw [deriv_add]
--   rw [deriv_sub]
--   rw [deriv_add]
--   rw [deriv_const]
--   rw [deriv_div]
--   rw [deriv_const]
--   rw [deriv_pow]
--   rw [deriv_div]
--   rw [deriv_const]
--   rw [deriv_pow]
--   rw [deriv_zpow]
--   field_simp [h]
--   ring_nf -- Normalize terms with multiplication and powers
--   rw [zpow_add] -- Rewrite to combine exponents where applicable
--   ring -- Finish simplifying the expression


-- example (x0: ℝ) (h: x0 ≠ 0): deriv (λ x ↦ 6*x^3 + 5/x^2) x0 = 18*x0^2 - 10*x0^(-3:ℤ) := by
--   rw [zpow_neg x0 3]
--   rw [<- div_eq_mul_inv]
--   rw [deriv_add]
--   rw [deriv_const_mul]
--   rw [deriv_pow]
--   rw [deriv_div]
--   rw [deriv_const]
--   rw [deriv_pow]
--   field_simp [h]
--   ring
--   simp
--   rw [←zpow_one_add x0]
--   --exact zpow_one_add x0 3
--   exact differentiableAt_const _
--   exact differentiableAt_pow _
--   exact pow_ne_zero _ h
--   exact differentiableAt_pow _
--   exact DifferentiableAt.const_mul (differentiableAt_pow _) _
--   exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_pow _) (pow_ne_zero _ h)
--   -- TO BE CHECKED BY BINDU


example (x0: ℝ) (h: x0 ≠ 0): deriv (λ y ↦ (y^2 - 3)/y^2) x0 = 6/x0^3 := by
  rw [deriv_div]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const]
  field_simp [h]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_const _)
  exact differentiableAt_pow _
  exact pow_ne_zero _ h

example (x0: ℝ) (h: x0 > 0) (h1: (log x0) ≠ 0): deriv (λ t ↦ (5*t + 1)/(log t)) x0 = 5/(log x0) - (5*x0 + 1)/(x0*(log x0)^2) := by
  rw [deriv_div]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_log]
  field_simp [h, h1]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul (differentiableAt_id) _
  exact differentiableAt_const _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_id) _) (differentiableAt_const _)
  exact differentiableAt_log (ne_of_gt h)
  exact h1

-- example (x0: ℝ) (h: 4*x0^2 - 3*x0 + 2 ≠ 0): deriv (λ t ↦ (4*t^2 - 3*t + 2)^(-2:ℤ)) x0 = (6 - 16*x0)/(4*x0^2 - 3*x0 + 2)^3 := by
--   have h_comp: deriv (λ t ↦ (4*t^2 - 3*t + 2)^(-2:ℤ)) x0 = deriv ((λ x ↦ x ^ (-2:ℤ)) ∘ (λ x ↦ 4*x^2 - 3*x + 2)) x0 := by rfl
--   rw [h_comp]
--   rw [deriv_comp]
--   rw [deriv_zpow]
--   rw [deriv_add]
--   rw [deriv_sub]
--   rw [deriv_const_mul]
--   rw [deriv_pow]
--   rw [deriv_const_mul]
--   rw [deriv_id'']
--   rw [deriv_const]
--   simp
--   field_simp [h]
--   ring

example (x0: ℝ) (h: x0 ≠ 0): deriv (λ x ↦ x^(-1: ℤ) - x^(-5: ℤ)) x0 = -1/(x0^2) + 5/(x0^6) := by
  -- rw [deriv_sub]
  -- rw [deriv_zpow]
  -- rw [deriv_zpow]
  -- field_simp [h]
  -- ring
  -- norm_num
  -- rw [←zpow_add h]
  -- simp [add_neg_cancel_right, rpow_zero]
  -- -- rw [pow_]
  sorry

-- example (x0: ℝ) (h: x0 > 0): deriv (λ t ↦ 5*t^(-3:ℝ)) x0 = -15/x0^4 := by
--   rw [deriv_const_mul]
--   rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
--   field_simp [h]
--   ring
--   norm_num
--   rw [←rpow_add h]
--   simp [add_neg_cancel_right, rpow_zero]


-- example (x0: ℝ) (h: sin x0 - cos x0 > 0): deriv (λ x ↦ log (sin x - cos x)) x0 = (sin x + cos x)/(sin x - cos x) := by
--   have h_comp: deriv (λ x ↦ log (sin x - cos x)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ sin x - cos x)) x0 := by rfl
--   rw [h_comp]
--   rw [deriv_comp]
--   rw [deriv_log]
--   rw [deriv_sub]
--   rw [Real.deriv_sin]
--   rw [Real.deriv_cos]
--   field_simp [h]
--   norm_num
--   simp
--   ring
--   exact differentiableAt_sin
--   exact differentiableAt_cos
--   exact differentiableAt_log (ne_of_gt h)
--   exact DifferentiableAt.sub differentiableAt_sin differentiableAt_cos

-- Original Problem: f( x ) = {( {6{x^2} + 7x} )^4}
example (x0: ℝ): deriv (λ x ↦ (6*x^2 + 7*x)^4) x0 = 4*(6*x0^2 + 7*x0)^3 * (12*x0 + 7) := by
  rw [deriv_pow'']
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)


-- Original Problem: f( x ) = {( {6{x^2} + 7x} )^4}
example (x0: ℝ) (h: (6*x0^2 + 7*x0) > 0): deriv (λ x ↦ log ((6*x^2 + 7*x)^4)) x0 = 4 * (12*x0 + 7)/(6*x0^2 + 7*x0) := by
  have h_comp: deriv (λ x ↦ log ((6*x^2 + 7*x)^4)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ (6*x^2 + 7*x)^4)) x0 := by rfl
  rw [h_comp]
  rw [deriv_comp]
  rw [deriv_pow'']
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  field_simp [h]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_log (pow_ne_zero _ (ne_of_gt h))
  exact DifferentiableAt.pow (DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)) _
