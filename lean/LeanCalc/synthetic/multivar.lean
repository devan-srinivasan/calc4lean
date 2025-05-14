
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 5 + p.2 ^ 3 - 25) (x-3, y-4) (3, 4) = 0) → (3 * (3*(x-3)^2 + 10*(x-3) + 2) + 4 * (5*(y-4)^4 + 3*(y-4)^2) = 0) := by
  intro h
  -- fderiv_sub or fderiv_add based on we subtract or add the constant
  rw [fderiv_sub] at h

  -- This is to split the expression into p.1 and p.2
  have h_split 
  -- We assume they are differentiable (anyways we will prove that later)
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 5 + p.2 ^ 3) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 5 + p.2 ^ 3) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) (x - 3, y - 4) +
      fderiv ℝ (fun p => p.2 ^ 5 + p.2 ^ 3) (x - 3, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- Now we are back on track
  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (3 * (x-3) ^ 2 + 10 * (x-3) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 3 + 5 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    -- expandable part 1 --
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    -- end --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    -- expandable part 2 --
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))
    exact differentiableAt_const _
    -- ends --
    exact differentiableAt_fst

  -- Let's solve part 2
  have h2 : (fderiv ℝ (fun p => p.2 ^ 5 + p.2 ^ 3) (x - 3, y - 4)) (3, 4) = 4 * (5 * (y-4) ^ 4 + 3 * (y-4) ^ 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 5 + p.2 ^ 3) = (fun x => x ^ 5 + x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    -- expandable part 1 --
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    -- end --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    -- expandable part 2 --
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    -- ends --
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (25:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  -- Now this part is tricky, but let me help you out with a hint --
  -- This is different from the normal differentiableAt. Here we write the entire expression in one go
  -- Notice the exact statement matches (+ (+ (x^3) (5x^2))) (2x))
  -- Since you have the tree you can generate this. 

  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.const_mul (differentiableAt_fst.pow _) _)) (DifferentiableAt.const_mul differentiableAt_fst _)

  -- Let's do the same for p.2
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)
  
  -- Now we add the p.1 expression and p.2 expression
  -- This can be done, but don't tree p.1 and p.2 as separate expressions,
  -- It's a nested DifferentiableAt.add that adds one term in order
  -- I.e. given p.1 ^ 3 + 5*p.1^2 + 2*p.1 + p.2 ^ 5 + p.2^3
  -- We are basically doing (((p.1 ^ 3 + 5*p.1^2) + 2*p.1) + p.2 ^ 5) + p.2^3
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.const_mul (differentiableAt_fst.pow _) _)) (DifferentiableAt.const_mul differentiableAt_fst _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)

  -- Finally for the const part
  exact differentiableAt_const _
  -- And we are done :)
