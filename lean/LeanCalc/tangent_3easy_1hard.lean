import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic
open Real
open Set

-- Simple Example 1
example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) → (3 * x + 4 * y - 25 = 0) := by
  intro h
  rw [fderiv_sub] at h
  rw [fderiv_add] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- I am explaining the idea here. We have 3 hypotheis.
  -- First is for the first variable,i.e. p.1. Every expression that uses p.1 goes here.
  -- Second is for the second variable, i.e. p.2. Every expression that uses p.2 goes afterwards.
  -- Third is for const
  -- For now keep the expressions with p.1 next to each other and expressions with p.2 next to each other. 
  -- And don't do p.1*p.2 (I have no idea how to solve them and can't think I can figure that out by the deadline)
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2) (x-3, y-4) (3, 4) = 6 * x - 18 := by
  -- (@Devan) Here is how I solved it and how it can be expanded
    -- The following part is constant for everything
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst] -- We write fst here since it is p.1
    rw [←deriv_fderiv] -- this converts fderiv to deriv
    -- constant part ends--
    -- the following is the expandable part (we do as if it was a normal derivative)
    -- whatever is the function wrt p.1 apply accordingly --
    rw [deriv_pow]
    -- expandable part ends --
    -- constant part 2 begins --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst'] -- again fst because p.1 --
    field_simp
    ring
    -- expandable part 2  (is differentiableAt part)--
    exact differentiableAt_pow _
    -- expandable part ends --
    exact differentiableAt_fst -- In the end we add this always

  -- This is very similar to the previous part --
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.2 ^ 2) (x-3, y-4) (3, 4) = 8 * y - 32  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun y => y ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    rw [deriv_pow]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_pow _
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (25:ℝ)) (x-3, y-4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith
  exact differentiableAt_fst.pow _
  exact differentiableAt_snd.pow _
  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)
  exact differentiableAt_const _

-- Simple Example 2
example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) → (9 * x^2 - 54*x + 8 * y + 49 = 0) := by
  intro h
  rw [fderiv_sub] at h
  rw [fderiv_add] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 3) (x-3, y-4) (3, 4) = 9 * (x-3)^2 := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    rw [deriv_pow]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_pow _
    exact differentiableAt_fst

  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.2 ^ 2) (x-3, y-4) (3, 4) = 8 * y - 32  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun y => y ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    rw [deriv_pow]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_pow _
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (25:ℝ)) (x-3, y-4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith
  exact differentiableAt_fst.pow _
  exact differentiableAt_snd.pow _
  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)
  exact differentiableAt_const _

-- Simple Example 3
example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.1 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) → ((3:ℝ) * ((2:ℝ) * (x - (3:ℝ)) + (1:ℝ)) + (4:ℝ) * ((2:ℝ) * (y - (4:ℝ))) = 0) := by
  intro h
  rw [fderiv_sub] at h
  rw [fderiv_add] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- @Devan (this is a good example because we have a slightly more complicated fn wrt p.1)
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) (x-3, y-4) (3, 4) = (3:ℝ) * ((2:ℝ) * (x - (3:ℝ)) + (1:ℝ)) := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) = (fun x => x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    -- expandable part 1 (since the fn is p.1 ^ 2 + p.1, solve how you would have solved x^2 + x) --
    rw [deriv_add]
    rw [deriv_pow]
    rw [deriv_id'']
    -- expandable part ends --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    -- expandable part 2 (since the fn is p.1 ^ 2 + p.1, solve how you would have solved x^2 + x) --
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) differentiableAt_id
    -- expandable part ends --
    exact differentiableAt_fst
    
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.2 ^ 2) (x-3, y-4) (3, 4) = (4:ℝ) * ((2:ℝ) * (y - (4:ℝ)))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun y => y ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    rw [deriv_pow]
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_pow _
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (25:ℝ)) (x-3, y-4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith
  exact DifferentiableAt.add (differentiableAt_fst.pow _) differentiableAt_fst
  exact differentiableAt_snd.pow _
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) differentiableAt_fst) (differentiableAt_snd.pow _)
  exact differentiableAt_const _

-- Harder example
-- The problem with the simple examples is, we have to stick to just one expression with p.2
-- If we want to do more expression with p.2 then it becomes a bit more complicated.
-- Check if you can code for it. If not we will just expand simple examples 1-3
-- I will try one more to demonstrate the idea
example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5*p.1^2 + 2*p.1 + p.2 ^ 5 + p.2^3 - 25) (x-3, y-4) (3, 4) = 0) → (3 * (3*(x-3)^2 + 10*(x-3) + 2) + 4 * (5*(y-4)^4 + 3*(y-4)^2) = 0) := by
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
  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (3*(x-3)^2 + 10*(x-3) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 3 + 5 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    -- expandable part 1 --
    rw [deriv_add]
    rw [deriv_add]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_id'']
    -- end --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    -- expandable part 2 --
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.const_mul (differentiableAt_pow _) _
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)
    exact DifferentiableAt.const_mul differentiableAt_id _
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.const_mul (differentiableAt_pow _) _)) (DifferentiableAt.const_mul differentiableAt_id _)
    -- ends --
    exact differentiableAt_fst

  -- Let's solve part 2
  have h2 : (fderiv ℝ (fun p => p.2 ^ 5 + p.2 ^ 3) (x - 3, y - 4)) (3, 4) = 4 * (5*(y-4)^4 + 3*(y-4)^2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 5 + p.2 ^ 3) = (fun x => x ^ 5 + x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    -- expandable part 1 --
    rw [deriv_add]
    rw [deriv_pow]
    rw [deriv_pow]
    -- end --
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    -- expandable part 2 --
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    -- ends --
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (25:ℝ)) (x-3, y-4) (3, 4) = 0 := by
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

  
