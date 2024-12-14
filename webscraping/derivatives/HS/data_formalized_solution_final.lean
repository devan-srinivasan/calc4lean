import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real

/-
I will be using this file for generating augmentations
(If you want to add anything to the file then add at the end)
(Don't add any incomplete proofs to this file)
-/

-- Original Problem: f( x ) = 6{x^3} - 9x + 4
example (x0: ℝ): deriv (λ x ↦ 6*x^3 - 9*x + 4) x0 = 18*x0^2 - 9 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _

-- Original Problem: y = 2{t^4} - 10{t^2} + 13t
example (x0: ℝ): deriv (λ t ↦ 2*t^4 - 10*t^2 + 13*t) x0 = 2*x0^3 + x0*(6*x0^2 - 10) - 10*x0 + 13 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
  exact DifferentiableAt.const_mul differentiableAt_id _

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
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_pow _) (pow_ne_zero _ h)

-- Original Problem: z = x( {3{x^2} - 9} )
example (x0: ℝ): deriv (λ x ↦ 3*x*(x^2 - 3)) x0 = 9*x0^2 - 9 := by
  rw [deriv_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_const _)

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

-- Original Problem: h( x ) = \frac{{4{x^3} - 7x + 8}}{x}
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

-- Original Problem: f( y ) = \frac{{{y^5} - 5{y^3} + 2y}}{{{y^3}}}
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


-- Original Problem: f( t ) = ( {4{t^2} - t} )( {{t^3} - 8{t^2} + 12} )
example (x0: ℝ): deriv (λ t ↦ t*(4*t - 1)*(t^3 - 8*t^2 + 12)) x0 = x0*(4*x0 - 1)*(3*x0^2 - 16*x0) + 4*x0*(x0^3 - 8*x0^2 + 12) + (4*x0 - 1)*(x0^3 - 8*x0^2 + 12) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
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
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact differentiableAt_id
  exact DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact DifferentiableAt.mul differentiableAt_id (DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)) (differentiableAt_const _)

-- Original Problem: h( z ) = ( {5z + 8{z^2} - {z^3}} )( {1 + 2z + 3{z^2}} )
example (x0: ℝ): deriv (λ z ↦ z*(-(z^2) + 8*z + 5)*(3*z^2 + 2*z + 1)) x0 = x0*(8 - 2*x0)*(3*x0^2 + 2*x0 + 1) + x0*(6*x0 + 2)*(-x0^2 + 8*x0 + 5) + (-x0^2 + 8*x0 + 5)*(3*x0^2 + 2*x0 + 1) := by
  rw [deriv_mul]
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv.neg]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_const]
  rw [deriv_id'']
  rw [deriv_add]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _
  exact differentiableAt_id
  exact DifferentiableAt.neg (differentiableAt_pow _)
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.add (DifferentiableAt.neg (differentiableAt_pow _)) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _
  exact differentiableAt_id
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.neg (differentiableAt_pow _)) (DifferentiableAt.const_mul differentiableAt_id _)) (differentiableAt_const _)
  exact DifferentiableAt.mul differentiableAt_id (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.neg (differentiableAt_pow _)) (DifferentiableAt.const_mul differentiableAt_id _)) (differentiableAt_const _))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_pow _) _) (DifferentiableAt.const_mul differentiableAt_id _)) (differentiableAt_const _)

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

-- Original Problem: f( t ) = \frac{{1 + 5t}}{{\ln ( t )}}
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


-- Original Problem: R( w ) = \csc ( {w} )
example (x0: ℝ) (h: sin x0 ≠ 0): deriv (λ w ↦ 1/sin w) x0 = -cos x0 / (sin x0)^2 := by
  rw [deriv_div]
  rw [deriv_const]
  rw [Real.deriv_sin]
  simp
  exact differentiableAt_const _
  exact differentiableAt_sin
  exact h

-- Original Problem: G( x ) = 2\sin ( {3x + \tan ( x )} )
-- Tweaked Problem: G( x ) = 2\sin ( {3x + \tan ( x )} )
example (x0: ℝ): deriv (λ x ↦ 2*sin (3*x + cos x)) x0 = -2*(sin x0 - 3) * cos (3*x0 + cos x0) := by
  rw [deriv_const_mul]
  have h_comp: deriv (λ x ↦ sin (3*x + cos x)) x0 = deriv ((λ x ↦ sin x) ∘ (λ x ↦ 3*x + cos x)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [Real.deriv_cos]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_cos
  exact differentiableAt_sin
  exact DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_cos)
  exact DifferentiableAt.sin (DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) differentiableAt_cos)

-- Original Problem: h( u ) = \tan ( {4 + 10u} )
-- Tweaked Problem: h( u ) = \sin ( {4 + 10u} )
example (x0: ℝ): deriv (λ x ↦ sin (10*x + 4)) x0 = 10 * cos (4 + 10 * x0) := by
  have h_comp: deriv (λ x ↦ sin (10*x + 4)) x0 = deriv ((λ x ↦ sin x) ∘ (λ x ↦10 * x + 4)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact differentiableAt_sin
  exact DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)

-- Original Problem: F( y ) = \ln ( {1 - 5{y^2} + {y^3}} )
example (x0: ℝ) (h: x0^3 - 5*x0^2 + 1 > 0): deriv (λ y ↦ (log (y^3 - 5*y^2 + 1))) x0 = (3*x0^2 - 10*x0)/(x0^3 - 5*x0^2 + 1) := by
  have h_comp: deriv (λ y ↦ (log (y^3 - 5*y^2 + 1))) x0 = deriv ((λ y ↦ log y) ∘ (λ y ↦ (y^3 - 5*y^2 + 1))) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
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

-- Original Problem: g( z ) = 3{z^7} - \sin ( {{z^2} + 6} )
example (x0: ℝ): deriv (λ z ↦ 3*z^7 - sin (z^2 + 6)) x0 = 21*x0^6 - cos (x0^2 + 6) * 2 * x0 := by
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_pow]
  have h_comp: deriv (λ y ↦ sin (y^2 + 6)) x0 = deriv ((λ y ↦ sin y) ∘ (λ y ↦ y^2 + 6)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact differentiableAt_sin
  exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.sin (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))


-- Original Problem: q( t ) = {t^2}\ln ( {{t^5}} )
example (x0: ℝ) (h: x0^5 > 0): deriv (λ t ↦ t^2*(log (t^5))) x0 = 2*x0*(log (x0^5)) + 5*x0 := by
  rw [deriv_mul]
  rw [deriv_pow]
  have h_comp: deriv (λ x ↦ (log (x^5))) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x^5)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [deriv_log]
  rw [deriv_pow]
  field_simp [h]
  ring
  exact differentiableAt_log (ne_of_gt h)
  exact differentiableAt_pow _
  exact differentiableAt_pow _
  exact DifferentiableAt.log (differentiableAt_pow _) (ne_of_gt h)

-- -- Original Problem: f(x) = (\sin (2x+1))^2
example (x0: ℝ): deriv (λ x ↦ sin (2*x + 1)^2) x0 = 4 * sin (2 * x0 + 1) * cos (2 * x0 + 1) := by
  rw [deriv_pow'']
  have h_comp: deriv (λ x ↦ sin (2*x + 1)) x0 = deriv ((λ x ↦ sin x) ∘ (λ x ↦ 2*x + 1)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [Real.deriv_sin]
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact differentiableAt_sin
  exact DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact DifferentiableAt.sin (DifferentiableAt.add (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _))

-- Original Problem: f(x) = \log_7 (2x-3)
example (x0: ℝ) (h : 2*x0 - 3 > 0): deriv (λ x ↦ (log (2*x - 3))/(log 7)) x0 = 2/((2*x0 - 3)*(log 7)) := by
  rw [deriv_div]
  have h_comp: deriv (λ x ↦ log (2*x - 3)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ (2*x - 3))) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
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

-- Original Problem: f(x) = \frac{x+1}{x}
example (x0: ℝ) (h : x0 ≠ 0): deriv (λ x ↦ (x + 1)/x) x0 = -1/x0^2 := by
  rw [deriv_div]
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)
  exact differentiableAt_id
  exact h

-- Original Problem: f(x) = 3\cot (x) + 5 \csc (x)
-- Tweaked Problem: f(x) = 3\cos (x) + 5 \csc (x)
example (x0: ℝ) (h: sin x0 ≠ 0): deriv (λ x ↦ 3*(cos x) + 5/sin x) x0 = -3 * sin x0 - 5 * cos x0 / (sin x0)^2 := by
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [Real.deriv_cos]
  rw [deriv_div]
  rw [deriv_const]
  rw [Real.deriv_sin]
  ring
  exact differentiableAt_const _
  exact differentiableAt_sin
  exact h
  exact differentiableAt_cos
  exact DifferentiableAt.const_mul differentiableAt_cos _
  exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_sin) h

-- Original Problem: f(x) = x(x+1)^4
example (x0: ℝ): deriv (λ x ↦ x*(x + 1)^4) x0 = 4*x0*(x0 + 1)^3 + (x0 + 1)^4 := by
  rw [deriv_mul]
  rw [deriv_id'']
  have h_comp: deriv (λ x ↦ (x + 1)^4) x0 = deriv ((λ x ↦ x ^ 4) ∘ (λ x ↦ x + 1)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
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


-- Original Problem: f(x)=x\ln (3x)
-- Tweaked Problem: f(x)=x\ln x ... honestly in hindsight could've just done the original, was shi* at lean back then
example (x0: ℝ) (h: x0 > 0): deriv (λ x ↦ x*(log x)) x0 = (log x0) + 1 := by
  rw [deriv_mul]
  rw [deriv_id'']
  rw [Real.deriv_log]
  field_simp [h]
  exact differentiableAt_id
  exact differentiableAt_log (ne_of_gt h)

-- Original Problem: f(x)=x^2(x-1)^3
example (x0: ℝ): deriv (λ x ↦ x^2*(x - 1)^3) x0 = 3*x0^2*(x0 - 1)^2 + 2*x0*(x0 - 1)^3 := by
  rw [deriv_mul]
  rw [deriv_pow]
  rw [deriv_pow'']
  rw [deriv_sub]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)
  exact differentiableAt_pow _
  exact DifferentiableAt.pow (DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)) _

-- Original Problem: f(x)=x^3 \ln (2x)
example (x0: ℝ) (h: 2*x0 > 0): deriv (λ x ↦ x^3*(log (2*x))) x0 = 3*x0^2*(log (2*x0)) + x0^2 := by
  rw [deriv_mul]
  rw [deriv_pow]
  have h_comp: deriv (λ y ↦ log (2 * y)) x0 = deriv ((λ y ↦ log y) ∘ (λ y ↦ 2 * y)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
  rw [deriv_log]
  rw [deriv_const_mul]
  rw [deriv_id'']
  field_simp [h]
  ring
  exact differentiableAt_id
  exact differentiableAt_log (ne_of_gt h)
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_pow _
  exact DifferentiableAt.log (DifferentiableAt.const_mul differentiableAt_id _) (ne_of_gt h)

-- Original Problem: f(x)=2x^4(5+x)^3
example (x0: ℝ): deriv (λ x ↦ 2*x^4*(x + 5)^3) x0 = 6*x0^4*(x0 + 5)^2 + 8*x0^3*(x0 + 5)^3 := by
  rw [deriv_mul]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_pow'']
  rw [deriv_add]
  rw [deriv_const]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.pow (DifferentiableAt.add differentiableAt_id (differentiableAt_const _)) _

-- Original Problem: f(x)=x^2(x-3)^4
example (x0: ℝ): deriv (λ x ↦ x^2*(x - 3)^4) x0 = 4*x0^2*(x0 - 3)^3 + 2*x0*(x0 - 3)^4 := by
  rw [deriv_mul]
  rw [deriv_pow]
  rw [deriv_pow'']
  rw [deriv_sub]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_const _
  exact DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)
  exact differentiableAt_pow _
  exact DifferentiableAt.pow (DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)) _

-- Original Problem: f(x)=x(2x-1)^3
example (x0: ℝ): deriv (λ x ↦ x*(2*x - 1)^3) x0 = 6*x0*(2*x0 - 1)^2 + (2*x0 - 1)^3 := by
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_pow'']
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact differentiableAt_id
  exact DifferentiableAt.pow (DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)) _

-- Original Problem: f(x)=x^2 \ln (x+6)
example (x0: ℝ) (h: x0 + 6 ≠ 0): deriv (λ x ↦ x^2*(log (x + 6))) x0 = x0^2/(x0 + 6) + 2*x0*(log (x0 + 6)) := by
  rw [deriv_mul]
  rw [deriv_pow]
  have h_comp: deriv (λ x ↦ log (x + 6)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x + 6)) x0 := by rfl
  rw [h_comp]
  rw [deriv.comp]
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


-- Original Problem: f(x)=x(1-5x)^4
example (x0: ℝ): deriv (λ x ↦ x*(5*x - 1)^4) x0 = 20*x0*(5*x0 - 1)^3 + (5*x0 - 1)^4 := by
  rw [deriv_mul]
  rw [deriv_id'']
  rw [deriv_pow'']
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact differentiableAt_const _
  exact DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)
  exact differentiableAt_id
  exact DifferentiableAt.pow (DifferentiableAt.sub (DifferentiableAt.const_mul differentiableAt_id _) (differentiableAt_const _)) _

-- Original Problem: f(x)=(x+1)\ln (x^2 - 1)
example (x0: ℝ) (h: x0^2 - 1 ≠ 0): deriv (λ x ↦ (x + 1)*(log (x^2 - 1))) x0 = 2*x0*(x0 + 1)/(x0^2 - 1) + (log (x0^2 - 1)) := by
  rw [deriv_mul]
  have h_comp: deriv (λ x ↦ log (x^2 - 1)) x0 = deriv ((λ x ↦ log x) ∘ (λ x ↦ x^2 - 1)) x0 := by rfl
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_const]
  rw [h_comp]
  rw [deriv.comp]
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

-- Original Problem: f(x)=(x+2)(x-3)^3
example (x0: ℝ): deriv (λ x ↦ (x - 3)^3*(x + 2)) x0 = (x0 - 3)^3 + 3*(x0 - 3)^2*(x0 + 2) := by
  rw [deriv_mul]
  rw [deriv_pow'']
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
  exact DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)
  exact DifferentiableAt.pow (DifferentiableAt.sub differentiableAt_id (differentiableAt_const _)) _
  exact DifferentiableAt.add differentiableAt_id (differentiableAt_const _)

-- Original Problem: f(x) = x^5 + x^2
example (x0: ℝ): deriv (λ x ↦ x^5 + x^2) x0 = 5*x0^4 + 2*x0 := by
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_pow]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_pow _

-- Original Problem: f(x) = x + x^3
example (x0: ℝ): deriv (λ x ↦ x^3 + x) x0 = 3*x0^2 + 1 := by
  rw [deriv_add]
  rw [deriv_id'']
  rw [deriv_pow]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_id

-- Original Problem: f(x) = x^4 + 2
example (x0: ℝ): deriv (λ x ↦ x^4 + 2) x0 = 4*x0^3 := by
  rw [deriv_add]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact differentiableAt_const _

-- Original Problem: f(x) = x^6 - 2x
example (x0: ℝ): deriv (λ x ↦ x^6 - 2*x) x0 = 6*x0^5 - 2 := by
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul differentiableAt_id _


-- Original Problem: f(x) = 6x^3 + 5x^{-2}
example (x0: ℝ) (h: x0 ≠ 0): deriv (λ x ↦ 6*x^3 + 5/x^2) x0 = 18*x0^2 - 10/x0^3 := by
  rw [deriv_add]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_div]
  rw [deriv_const]
  rw [deriv_pow]
  field_simp [h]
  ring
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact pow_ne_zero _ h
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_pow _) (pow_ne_zero _ h)


-- Original Problem: f(x) = x^2 - 4x + 1
example (x0: ℝ): deriv (λ x ↦ x^2 - 4*x + 1) x0 = 2*x0 - 4 := by
  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul differentiableAt_id _
  exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.const_mul differentiableAt_id _)
  exact differentiableAt_const _


-- Original Problem: f(t) = t^6
example (x0: ℝ): deriv (λ t ↦ t^6) x0 = 6*x0^5 := by
  rw [deriv_pow]
  ring

-- Original Problem: f(t) = t^{2/3}
example (x0 : ℝ) (h : x0 > 0) : deriv (λ t ↦ t^(2/3 :ℝ)) x0 = (2/3)*x0^((2/3 :ℝ)-1) := by
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]

-- Original Problem: f(t) = t^{2/3}
example (x0: ℝ) (h: x0 > 0): deriv (λ t ↦ t^(2/3 :ℝ)) x0 = (2 :ℝ)/(3*x0^(1/3:ℝ)) := by
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
  field_simp [h]
  ring
  norm_num
  rw [←rpow_add h]
  simp [add_neg_cancel_right, rpow_zero]

-- Original Problem: f(t) = \frac{3}{4}t^2
example (x0: ℝ): deriv (λ t ↦ 3*t^2/4) x0 = 3*x0/2 := by
  rw [deriv_div]
  rw [deriv_const_mul]
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact differentiableAt_const _
  simp

-- Original Problem: f(t) = 8t^{\frac{1}{4}}
example (x0: ℝ)(h: x0 > 0): deriv (λ t ↦ 8*t^(1/4:ℝ)) x0 = (2:ℝ)/x0^(3/4:ℝ) := by
  rw [deriv_const_mul]
  rw [deriv_rpow_const (Or.inl (ne_of_gt h))]
  field_simp [h]
  ring
  norm_num
  rw [←rpow_add h]
  simp [add_neg_cancel_right, rpow_zero]
  exact DifferentiableAt.rpow_const differentiableAt_id (Or.inl (ne_of_gt h))
