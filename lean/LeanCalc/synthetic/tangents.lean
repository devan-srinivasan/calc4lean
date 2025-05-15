
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

open Real
open Set

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + 3 * p.1 + 3 * p.2 ^ 2 + 4 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (8 * (x-5) + 3) + 5 * (6 * (y-5) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + 3 * p.1 + 3 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (8 * (x-5) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + 3 * p.1) = (fun x => 4 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (6 * (y-5) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 4 * p.1 - 3 * p.2 ^ 3 + 5 * p.2 ^ 2 + 5 * p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (15 * (x-4) ^ 2 - 4) - 6 * (9 * (y-6) ^ 2 - 10 * (y-6) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 4 * p.1 - 3 * p.2 ^ 3 + 5 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (15 * (x-4) ^ 2 - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 4 * p.1) = (fun x => 5 * x ^ 3 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 6)) (4, 6) = 6 * (9 * (y-6) ^ 2 - 10 * (y-6) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) = (fun x => 3 * x ^ 3 - 5 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (2 * (x-6) - 3) + 6 * (4 * (y-6) ^ 3 - 9 * (y-6) ^ 2 + 4 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 3 * p.1) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 3 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) (x - 6, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 6, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) (x - 6, y - 6)) (6, 6) = 6 * (2 * (x-6) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 3 * p.1) = (fun x => x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 6, y - 6)) (6, 6) = 6 * (4 * (y-6) ^ 3 - 9 * (y-6) ^ 2 + 4 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2) = (fun x => x ^ 4 - 3 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (4 * (x-6) ^ 3 - 3 * (x-6) ^ 2 + 10 * (x-6) - 4) + 4 * (12 * (y-4) ^ 2 + 6 * (y-4) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (4 * (x-6) ^ 3 - 3 * (x-6) ^ 2 + 10 * (x-6) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 - p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 4 - x ^ 3 + 5 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (12 * (y-4) ^ 2 + 6 * (y-4) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 4 * x ^ 3 + 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (4 * (x-5) ^ 3 - 9 * (x-5) ^ 2 - 8 * (x-5) - 2) + 5 * (12 * (y-5) ^ 3 + 3 * (y-5) ^ 2 - 8 * (y-5) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (4 * (x-5) ^ 3 - 9 * (x-5) ^ 2 - 8 * (x-5) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 - 3 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) = (fun x => x ^ 4 - 3 * x ^ 3 - 4 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (12 * (y-5) ^ 3 + 3 * (y-5) ^ 2 - 8 * (y-5) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) = (fun x => 3 * x ^ 4 + x ^ 3 - 4 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - p.2 ^ 4 - 5 * p.2 - c) (x-6, y-3) (6, 3) = 0) → (6 * (15 * (x-6) ^ 2 + 8 * (x-6)) - 3 * (4 * (y-3) ^ 3 + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 5 * p.2) (x - 6, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 4 * p.1 ^ 2 - p.2 ^ 4 - 5 * p.2) (x - 6, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 3) -
      fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2) (x - 6, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 3)) (6, 3) = 6 * (15 * (x-6) ^ 2 + 8 * (x-6))  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => 5 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2) (x - 6, y - 3)) (6, 3) = 3 * (4 * (y-3) ^ 3 + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 5 * p.2) = (fun x => x ^ 4 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 3) (6, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (8 * (x-3) + 4) - 4 * (8 * (y-4) ^ 3 + 15 * (y-4) ^ 2 - 8 * (y-4) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + 4 * p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + 4 * p.1) (x - 3, y - 4) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 3, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + 4 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (8 * (x-3) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + 4 * p.1) = (fun x => 4 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 3, y - 4)) (3, 4) = 4 * (8 * (y-4) ^ 3 + 15 * (y-4) ^ 2 - 8 * (y-4) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) = (fun x => 2 * x ^ 4 + 5 * x ^ 3 - 4 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 3 * p.1 + 5 * p.2 ^ 2 + p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (15 * (x-3) ^ 2 - 3) + 2 * (10 * (y-2) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 3 * p.1 + 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (15 * (x-3) ^ 2 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 3 * p.1) = (fun x => 5 * x ^ 3 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)) (3, 2) = 2 * (10 * (y-2) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 2 - 5 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (4 * (x-5) + 4) + 4 * (6 * (y-4) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + 4 * p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + 4 * p.1) (x - 5, y - 4) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + 4 * p.1) (x - 5, y - 4)) (5, 4) = 5 * (4 * (x-5) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 4 * p.1) = (fun x => 2 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (6 * (y-4) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 - 5 * p.2) = (fun x => 3 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + 3 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (6 * (x-4) + 2) + 2 * (10 * (y-2) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + 3 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (6 * (x-4) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 2 * p.1) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (10 * (y-2) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 2 + 4 * p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (8 * (x-4) ^ 3 + 3 * (x-4) ^ 2 + 8 * (x-4) + 1) + 4 * (4 * (y-4) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1) (x - 4, y - 4) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1) (x - 4, y - 4)) (4, 4) = 4 * (8 * (x-4) ^ 3 + 3 * (x-4) ^ 2 + 8 * (x-4) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 4 + x ^ 3 + 4 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 4)) (4, 4) = 4 * (4 * (y-4) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 4 * p.2) = (fun x => 2 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 4 * p.1 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (16 * (x-6) ^ 3 - 12 * (x-6) ^ 2) - 6 * (8 * (y-6) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 3) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 - p.2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - 4 * p.1 ^ 3 - 4 * p.2 ^ 2 + p.2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 3) (x - 6, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2 - p.2) (x - 6, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 3) (x - 6, y - 6)) (6, 6) = 6 * (16 * (x-6) ^ 3 - 12 * (x-6) ^ 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 4 * p.1 ^ 3) = (fun x => 4 * x ^ 4 - 4 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 - p.2) (x - 6, y - 6)) (6, 6) = 6 * (8 * (y-6) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 - p.2) = (fun x => 4 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1 + p.2 ^ 2 + 4 * p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (8 * (x-2) ^ 3 + 12 * (x-2) ^ 2 - 10 * (x-2) + 1) + 5 * (2 * (y-5) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1 + p.2 ^ 2 + 4 * p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1) (x - 2, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 2, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1) (x - 2, y - 5)) (2, 5) = 2 * (8 * (x-2) ^ 3 + 12 * (x-2) ^ 2 - 10 * (x-2) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 4 + 4 * x ^ 3 - 5 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 2, y - 5)) (2, 5) = 5 * (2 * (y-5) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 4 * p.2) = (fun x => x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 + p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (15 * (x-4) ^ 2 - 10 * (x-4) - 3) + 3 * (6 * (y-3) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 + p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 4, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (15 * (x-4) ^ 2 - 10 * (x-4) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) = (fun x => 5 * x ^ 3 - 5 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 4, y - 3)) (4, 3) = 3 * (6 * (y-3) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + p.2) = (fun x => 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.1 - 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (6 * (x-4) + 1) - 4 * (15 * (y-4) ^ 2 - 10 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + p.1 - 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 4, y - 4) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 4, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 4, y - 4)) (4, 4) = 4 * (6 * (x-4) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + p.1) = (fun x => 3 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)) (4, 4) = 4 * (15 * (y-4) ^ 2 - 10 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 3 - 5 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + p.1 ^ 2 + p.1 + 4 * p.2 ^ 2 - 3 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (15 * (x-3) ^ 2 + 2 * (x-3) + 1) + 5 * (8 * (y-5) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 - 3 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + p.1 ^ 2 + p.1 + 4 * p.2 ^ 2 - 3 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 3, y - 5) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 - 3 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 3, y - 5)) (3, 5) = 3 * (15 * (x-3) ^ 2 + 2 * (x-3) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + p.1 ^ 2 + p.1) = (fun x => 5 * x ^ 3 + x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 - 3 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (8 * (y-5) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 - 3 * p.2) = (fun x => 4 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - c) (x-5, y-6) (5, 6) = 0) → (5 * (6 * (x-5) - 3) + 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 6) +
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 5, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 6)) (5, 6) = 5 * (6 * (x-5) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 5, y - 6)) (5, 6) = 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) = (fun x => 4 * x ^ 4 - 2 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.2 ^ 4 + p.2 ^ 2 + 5 * p.2 - c) (x-3, y-6) (3, 6) = 0) → (3 * (12 * (x-3) ^ 2 + 2 * (x-3)) - 6 * (8 * (y-6) ^ 3 - 2 * (y-6) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 2 - 5 * p.2) (x - 3, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.2 ^ 4 + p.2 ^ 2 + 5 * p.2) (x - 3, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 2 - 5 * p.2) (x - 3, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6)) (3, 6) = 3 * (12 * (x-3) ^ 2 + 2 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + p.1 ^ 2) = (fun x => 4 * x ^ 3 + x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 2 - 5 * p.2) (x - 3, y - 6)) (3, 6) = 6 * (8 * (y-6) ^ 3 - 2 * (y-6) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - p.2 ^ 2 - 5 * p.2) = (fun x => 2 * x ^ 4 - x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 6) (3, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 2 - 5 * p.2 - c) (x-6, y-3) (6, 3) = 0) → (6 * (6 * (x-6) - 5) + 3 * (10 * (y-3) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 3)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 3) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 3)) (6, 3) = 6 * (6 * (x-6) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 3)) (6, 3) = 3 * (10 * (y-3) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 5 * p.2) = (fun x => 5 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 3) (6, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (16 * (x-4) ^ 3 + 9 * (x-4) ^ 2 - 2 * (x-4) - 1) - 2 * (12 * (y-2) ^ 2 + 10 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1) (x - 4, y - 2) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1) (x - 4, y - 2)) (4, 2) = 4 * (16 * (x-4) ^ 3 + 9 * (x-4) ^ 2 - 2 * (x-4) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 - p.1 ^ 2 - p.1) = (fun x => 4 * x ^ 4 + 3 * x ^ 3 - x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (12 * (y-2) ^ 2 + 10 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) = (fun x => 4 * x ^ 3 + 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 + p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (8 * (x-5) - 1) - 3 * (6 * (y-3) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 + p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - p.1) (x - 5, y - 3) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 5, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - p.1) (x - 5, y - 3)) (5, 3) = 5 * (8 * (x-5) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - p.1) = (fun x => 4 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 5, y - 3)) (5, 3) = 3 * (6 * (y-3) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 - p.2) = (fun x => 3 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1 - 3 * p.2 ^ 2 - 5 * p.2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (16 * (x-5) ^ 3 + 9 * (x-5) ^ 2 + 2 * (x-5) + 1) - 2 * (6 * (y-2) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1 - 3 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 5, y - 2) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1) (x - 5, y - 2)) (5, 2) = 5 * (16 * (x-5) ^ 3 + 9 * (x-5) ^ 2 + 2 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 ^ 2 + p.1) = (fun x => 4 * x ^ 4 + 3 * x ^ 3 + x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 2)) (5, 2) = 2 * (6 * (y-2) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1 + 3 * p.2 ^ 3 + 5 * p.2 ^ 2 - c) (x-6, y-5) (6, 5) = 0) → (6 * (15 * (x-6) ^ 2 - 6 * (x-6) + 5) + 5 * (9 * (y-5) ^ 2 + 10 * (y-5)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 6, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1 + 3 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 6, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 6, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 5)) (6, 5) = 6 * (15 * (x-6) ^ 2 - 6 * (x-6) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 3 * p.1 ^ 2 + 5 * p.1) = (fun x => 5 * x ^ 3 - 3 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 6, y - 5)) (6, 5) = 5 * (9 * (y-5) ^ 2 + 10 * (y-5))  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 5 * p.2 ^ 2) = (fun x => 3 * x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 5) (6, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 4 * p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (6 * (x-6) - 4) - 2 * (10 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 4 * p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (6 * (x-6) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 4 * p.1) = (fun x => 3 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)) (6, 2) = 2 * (10 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 4 * p.2) = (fun x => 5 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 + 4 * p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (10 * (x-6) - 4) - 2 * (10 * (y-2) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 6, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (10 * (x-6) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 4 * p.1) = (fun x => 5 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 6, y - 2)) (6, 2) = 2 * (10 * (y-2) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 4 * p.2) = (fun x => 5 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 - p.2 ^ 4 + 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (4 * (x-5) - 3) - 4 * (4 * (y-4) ^ 3 - 12 * (y-4) ^ 2 - 8 * (y-4) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 3 * p.1 - p.2 ^ 4 + 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4)) (5, 4) = 5 * (4 * (x-5) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 3 * p.1) = (fun x => 2 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (4 * (y-4) ^ 3 - 12 * (y-4) ^ 2 - 8 * (y-4) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) = (fun x => x ^ 4 - 4 * x ^ 3 - 4 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + p.1 + 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (8 * (x-5) ^ 3 + 1) + 3 * (15 * (y-3) ^ 2 + 10 * (y-3)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + p.1 + 5 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1) (x - 5, y - 3)) (5, 3) = 5 * (8 * (x-5) ^ 3 + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + p.1) = (fun x => 2 * x ^ 4 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 3)) (5, 3) = 3 * (15 * (y-3) ^ 2 + 10 * (y-3))  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 5 * p.2 ^ 2) = (fun x => 5 * x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2 - c) (x-2, y-4) (2, 4) = 0) → (2 * (6 * (x-2) - 3) + 4 * (12 * (y-4) ^ 2 - 10 * (y-4) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 2, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 2, y - 4) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 2, y - 4)) (2, 4) = 2 * (6 * (x-2) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4)) (2, 4) = 4 * (12 * (y-4) ^ 2 - 10 * (y-4) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - 5 * p.2) = (fun x => 4 * x ^ 3 - 5 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 4) (2, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 - c) (x-2, y-6) (2, 6) = 0) → (2 * (3 * (x-2) ^ 2 + 4 * (x-2) + 1) - 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 2 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 2, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 2, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 2, y - 6)) (2, 6) = 2 * (3 * (x-2) ^ 2 + 4 * (x-2) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) = (fun x => x ^ 3 + 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) (x - 2, y - 6)) (2, 6) = 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 2 * p.2 ^ 3) = (fun x => 4 * x ^ 4 - 2 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + p.1 + 4 * p.2 ^ 3 + p.2 ^ 2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (9 * (x-6) ^ 2 + 1) + 4 * (12 * (y-4) ^ 2 + 2 * (y-4)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + p.1 + 4 * p.2 ^ 3 + p.2 ^ 2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + p.1) (x - 6, y - 4)) (6, 4) = 6 * (9 * (x-6) ^ 2 + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + p.1) = (fun x => 3 * x ^ 3 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 6, y - 4)) (6, 4) = 4 * (12 * (y-4) ^ 2 + 2 * (y-4))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + p.2 ^ 2) = (fun x => 4 * x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 - 4 * p.2 - c) (x-3, y-3) (3, 3) = 0) → (3 * (15 * (x-3) ^ 2 + 5) - 3 * (15 * (y-3) ^ 2 + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1) (x - 3, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2) (x - 3, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 - 4 * p.2) (x - 3, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1) (x - 3, y - 3) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2) (x - 3, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1) (x - 3, y - 3)) (3, 3) = 3 * (15 * (x-3) ^ 2 + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 5 * p.1) = (fun x => 5 * x ^ 3 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2) (x - 3, y - 3)) (3, 3) = 3 * (15 * (y-3) ^ 2 + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 4 * p.2) = (fun x => 5 * x ^ 3 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 3) (3, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 4 * p.1 + 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (12 * (x-4) ^ 2 - 4) + 2 * (12 * (y-2) ^ 3 + 15 * (y-2) ^ 2 + 6 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 4 * p.1 + 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (12 * (x-4) ^ 2 - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 4 * p.1) = (fun x => 4 * x ^ 3 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (12 * (y-2) ^ 3 + 15 * (y-2) ^ 2 + 6 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 2 + 4 * p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (2 * (x-6) - 2) + 2 * (6 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 6, y - 2) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (2 * (x-6) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 2 * p.1) = (fun x => x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)) (6, 2) = 2 * (6 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.1 + p.2 ^ 3 + p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (2 * (x-2) + 1) + 5 * (3 * (y-5) ^ 2 + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + p.1 + p.2 ^ 3 + p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 2, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 3 + p.2) (x - 2, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 2, y - 5)) (2, 5) = 2 * (2 * (x-2) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) = (fun x => x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2) (x - 2, y - 5)) (2, 5) = 5 * (3 * (y-5) ^ 2 + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + p.2) = (fun x => x ^ 3 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + 2 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (4 * (x-6) + 2) - 4 * (12 * (y-4) ^ 3 - 3 * (y-4) ^ 2 + 4 * (y-4) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + 2 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (4 * (x-6) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.1) = (fun x => 2 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (12 * (y-4) ^ 3 - 3 * (y-4) ^ 2 + 4 * (y-4) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 4 - x ^ 3 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 4 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (6 * (x-6) - 4) - 2 * (16 * (y-2) ^ 3 + 3 * (y-2) ^ 2 - 6 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 4 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (6 * (x-6) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 4 * p.1) = (fun x => 3 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 2)) (6, 2) = 2 * (16 * (y-2) ^ 3 + 3 * (y-2) ^ 2 - 6 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 4 * x ^ 4 + x ^ 3 - 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (12 * (x-5) ^ 2 + 4 * (x-5)) + 3 * (6 * (y-3) ^ 2 - 2 * (y-3) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 5, y - 3) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 5, y - 3)) (5, 3) = 5 * (12 * (x-5) ^ 2 + 4 * (x-5))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 2 * p.1 ^ 2) = (fun x => 4 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 3)) (5, 3) = 3 * (6 * (y-3) ^ 2 - 2 * (y-3) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) = (fun x => 2 * x ^ 3 - x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (12 * (x-2) ^ 2 + 3) + 3 * (15 * (y-3) ^ 2 + 8 * (y-3)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 3 * p.1) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 3 * p.1) (x - 2, y - 3) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 2, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 3 * p.1) (x - 2, y - 3)) (2, 3) = 2 * (12 * (x-2) ^ 2 + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 3 * p.1) = (fun x => 4 * x ^ 3 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 2, y - 3)) (2, 3) = 3 * (15 * (y-3) ^ 2 + 8 * (y-3))  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) = (fun x => 5 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 - p.2 ^ 2 - 5 * p.2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (20 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) + 2) + 6 * (3 * (y-6) ^ 2 - 2 * (y-6) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 5 * p.2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 - p.2 ^ 2 - 5 * p.2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 5 * p.2) (x - 5, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 6)) (5, 6) = 5 * (20 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 + 2 * p.1) = (fun x => 5 * x ^ 4 + x ^ 3 + 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 5 * p.2) (x - 5, y - 6)) (5, 6) = 6 * (3 * (y-6) ^ 2 - 2 * (y-6) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - p.2 ^ 2 - 5 * p.2) = (fun x => x ^ 3 - x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1 + 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (12 * (x-6) ^ 3 - 3 * (x-6) ^ 2 - 4) + 4 * (20 * (y-4) ^ 3 + 3 * (y-4) ^ 2 - 6 * (y-4) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1 + 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (12 * (x-6) ^ 3 - 3 * (x-6) ^ 2 - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 - p.1 ^ 3 - 4 * p.1) = (fun x => 3 * x ^ 4 - x ^ 3 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (20 * (y-4) ^ 3 + 3 * (y-4) ^ 2 - 6 * (y-4) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - 2 * p.2) = (fun x => 5 * x ^ 4 + x ^ 3 - 3 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - p.1 + 4 * p.2 ^ 3 + p.2 ^ 2 - c) (x-2, y-6) (2, 6) = 0) → (2 * (6 * (x-2) - 1) + 6 * (12 * (y-6) ^ 2 + 2 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - p.1 + 4 * p.2 ^ 3 + p.2 ^ 2) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - p.1) (x - 2, y - 6) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 2, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - p.1) (x - 2, y - 6)) (2, 6) = 2 * (6 * (x-2) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - p.1) = (fun x => 3 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2) (x - 2, y - 6)) (2, 6) = 6 * (12 * (y-6) ^ 2 + 2 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + p.2 ^ 2) = (fun x => 4 * x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 - 3 * p.2 ^ 2 - 2 * p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (8 * (x-4) + 1) - 6 * (6 * (y-6) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + p.1 - 3 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) (x - 4, y - 6)) (4, 6) = 4 * (8 * (x-4) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + p.1) = (fun x => 4 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 4, y - 6)) (4, 6) = 6 * (6 * (y-6) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 2 * p.2) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2 - c) (x-4, y-5) (4, 5) = 0) → (4 * (3 * (x-4) ^ 2 + 3) + 5 * (20 * (y-5) ^ 3 - 3 * (y-5) ^ 2 - 8 * (y-5) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 3 * p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 3 * p.1) (x - 4, y - 5) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 4, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 3 * p.1) (x - 4, y - 5)) (4, 5) = 4 * (3 * (x-4) ^ 2 + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 3 * p.1) = (fun x => x ^ 3 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 4, y - 5)) (4, 5) = 5 * (20 * (y-5) ^ 3 - 3 * (y-5) ^ 2 - 8 * (y-5) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 - p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) = (fun x => 5 * x ^ 4 - x ^ 3 - 4 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 3 - 2 * p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (10 * (x-4) + 1) + 4 * (6 * (y-4) ^ 2 - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + p.1) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - 2 * p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 3 - 2 * p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) (x - 4, y - 4) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - 2 * p.2) (x - 4, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) (x - 4, y - 4)) (4, 4) = 4 * (10 * (x-4) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + p.1) = (fun x => 5 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - 2 * p.2) (x - 4, y - 4)) (4, 4) = 4 * (6 * (y-4) ^ 2 - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - 2 * p.2) = (fun x => 2 * x ^ 3 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 5 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 - c) (x-4, y-5) (4, 5) = 0) → (4 * (9 * (x-4) ^ 2 - 5) - 5 * (16 * (y-5) ^ 3 - 9 * (y-5) ^ 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 5 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 5) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3) (x - 4, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 5)) (4, 5) = 4 * (9 * (x-4) ^ 2 - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 5 * p.1) = (fun x => 3 * x ^ 3 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3) (x - 4, y - 5)) (4, 5) = 5 * (16 * (y-5) ^ 3 - 9 * (y-5) ^ 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 3 * p.2 ^ 3) = (fun x => 4 * x ^ 4 - 3 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 3 * p.1 - 5 * p.2 ^ 2 + 4 * p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (8 * (x-4) ^ 3 - 3) - 6 * (10 * (y-6) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 3 * p.1 - 5 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (8 * (x-4) ^ 3 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 3 * p.1) = (fun x => 2 * x ^ 4 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 6)) (4, 6) = 6 * (10 * (y-6) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 4 * p.2) = (fun x => 5 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.1 - 5 * p.2 ^ 2 + 3 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (2 * (x-5) + 1) - 4 * (10 * (y-4) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + p.1 - 5 * p.2 ^ 2 + 3 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 5, y - 4)) (5, 4) = 5 * (2 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) = (fun x => x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (10 * (y-4) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 3 * p.2) = (fun x => 5 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 + 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) (x-2, y-2) (2, 2) = 0) → (2 * (15 * (x-2) ^ 2 + 2 * (x-2) - 2) - 2 * (12 * (y-2) ^ 3 - 12 * (y-2) ^ 2 + 8 * (y-2) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 2, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - p.2) (x - 2, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 + 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) (x - 2, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 2, y - 2) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - p.2) (x - 2, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 2, y - 2)) (2, 2) = 2 * (15 * (x-2) ^ 2 + 2 * (x-2) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 3 + x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - p.2) (x - 2, y - 2)) (2, 2) = 2 * (12 * (y-2) ^ 3 - 12 * (y-2) ^ 2 + 8 * (y-2) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - p.2) = (fun x => 3 * x ^ 4 - 4 * x ^ 3 + 4 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 2) (2, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2 - c) (x-3, y-6) (3, 6) = 0) → (3 * (6 * (x-3) - 5) + 6 * (20 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 8 * (y-6) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6)) (3, 6) = 3 * (6 * (x-3) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 6)) (3, 6) = 6 * (20 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 8 * (y-6) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 - 2 * p.2 ^ 3 - 4 * p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 4 - 2 * x ^ 3 - 4 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 6) (3, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1 - 3 * p.2 ^ 4 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2 - c) (x-6, y-3) (6, 3) = 0) → (6 * (3 * (x-6) ^ 2 + 8 * (x-6) - 3) - 3 * (12 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 4 * (y-3) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1 - 3 * p.2 ^ 4 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 3)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 3) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 3)) (6, 3) = 6 * (3 * (x-6) ^ 2 + 8 * (x-6) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 4 * p.1 ^ 2 - 3 * p.1) = (fun x => x ^ 3 + 4 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 3)) (6, 3) = 3 * (12 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 4 * (y-3) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2) = (fun x => 3 * x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 3) (6, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) (x-2, y-4) (2, 4) = 0) → (2 * (20 * (x-2) ^ 3 + 9 * (x-2) ^ 2 + 1) - 4 * (12 * (y-4) ^ 2 + 6 * (y-4) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1) (x - 2, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1) (x - 2, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1) (x - 2, y - 4)) (2, 4) = 2 * (20 * (x-2) ^ 3 + 9 * (x-2) ^ 2 + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 + p.1) = (fun x => 5 * x ^ 4 + 3 * x ^ 3 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 4)) (2, 4) = 4 * (12 * (y-4) ^ 2 + 6 * (y-4) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 - 5 * p.2) = (fun x => 4 * x ^ 3 + 3 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 4) (2, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 4 * p.1 ^ 2 + p.2 ^ 3 + 3 * p.2 ^ 2 + p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (12 * (x-4) ^ 2 - 8 * (x-4)) + 2 * (3 * (y-2) ^ 2 + 6 * (y-2) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1 ^ 2) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 4 * p.1 ^ 2 + p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1 ^ 2) (x - 4, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 4 * p.1 ^ 2) (x - 4, y - 2)) (4, 2) = 4 * (12 * (x-4) ^ 2 - 8 * (x-4))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 4 * p.1 ^ 2) = (fun x => 4 * x ^ 3 - 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 4, y - 2)) (4, 2) = 2 * (3 * (y-2) ^ 2 + 6 * (y-2) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) = (fun x => x ^ 3 + 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (3 * (x-5) ^ 2 - 4) - 4 * (12 * (y-4) ^ 2 + 10 * (y-4) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 4 * p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 4 * p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1) (x - 5, y - 4)) (5, 4) = 5 * (3 * (x-5) ^ 2 - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 4 * p.1) = (fun x => x ^ 3 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (12 * (y-4) ^ 2 + 10 * (y-4) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2) = (fun x => 4 * x ^ 3 + 5 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 + 3 * p.2 ^ 2 + 4 * p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (4 * (x-3) ^ 3 + 3 * (x-3) ^ 2 - 8 * (x-3) + 1) + 4 * (6 * (y-4) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 + 3 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (x - 3, y - 4) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (x - 3, y - 4)) (3, 4) = 3 * (4 * (x-3) ^ 3 + 3 * (x-3) ^ 2 - 8 * (x-3) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) = (fun x => x ^ 4 + x ^ 3 - 4 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 4)) (3, 4) = 4 * (6 * (y-4) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (15 * (x-4) ^ 2 - 4 * (x-4) - 2) + 2 * (8 * (y-2) ^ 3 + 12 * (y-2) ^ 2 + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (15 * (x-4) ^ 2 - 4 * (x-4) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 3 - 2 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (8 * (y-2) ^ 3 + 12 * (y-2) ^ 2 + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 5 * p.2) = (fun x => 2 * x ^ 4 + 4 * x ^ 3 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3 + 3 * p.2 ^ 2 - p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (4 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) - 5) + 3 * (3 * (y-3) ^ 2 + 6 * (y-3) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 3)) (5, 3) = 5 * (4 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) = (fun x => x ^ 4 + x ^ 3 + 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) (x - 5, y - 3)) (5, 3) = 3 * (3 * (y-3) ^ 2 + 6 * (y-3) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) = (fun x => x ^ 3 + 3 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 3 * p.1 + 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (6 * (x-6) + 3) + 4 * (15 * (y-4) ^ 2 - 4 * (y-4) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 3 * p.1 + 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (6 * (x-6) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 3 * p.1) = (fun x => 3 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (15 * (y-4) ^ 2 - 4 * (y-4) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 2 * p.2 ^ 2 + 2 * p.2) = (fun x => 5 * x ^ 3 - 2 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2 - c) (x-3, y-3) (3, 3) = 0) → (3 * (16 * (x-3) ^ 3 - 6 * (x-3) ^ 2 + 4 * (x-3)) - 3 * (15 * (y-3) ^ 2 + 8 * (y-3) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 3, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2) (x - 3, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - p.2) (x - 3, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 3, y - 3) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2) (x - 3, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) (x - 3, y - 3)) (3, 3) = 3 * (16 * (x-3) ^ 3 - 6 * (x-3) ^ 2 + 4 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) = (fun x => 4 * x ^ 4 - 2 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2) (x - 3, y - 3)) (3, 3) = 3 * (15 * (y-3) ^ 2 + 8 * (y-3) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 4 * p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 3 + 4 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 3) (3, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 2 + p.2 - c) (x-4, y-5) (4, 5) = 0) → (4 * (2 * (x-4) - 5) - 5 * (6 * (y-5) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 2 + p.2) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 4, y - 5) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 4, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 4, y - 5)) (4, 5) = 4 * (2 * (x-4) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 5 * p.1) = (fun x => x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 4, y - 5)) (4, 5) = 5 * (6 * (y-5) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 - p.2) = (fun x => 3 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - 3 * p.1 ^ 3 - p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (4 * (x-3) ^ 3 - 9 * (x-3) ^ 2) - 2 * (3 * (y-2) ^ 2 - 10 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 - 3 * p.1 ^ 3 - p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3) (x - 3, y - 2) -
      fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 - 3 * p.1 ^ 3) (x - 3, y - 2)) (3, 2) = 3 * (4 * (x-3) ^ 3 - 9 * (x-3) ^ 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 - 3 * p.1 ^ 3) = (fun x => x ^ 4 - 3 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (3 * (y-2) ^ 2 - 10 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 3 - 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 5 * p.1 + 2 * p.2 ^ 2 - 5 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (4 * (x-3) - 5) + 5 * (4 * (y-5) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 5 * p.1 + 2 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 5) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 5)) (3, 5) = 3 * (4 * (x-3) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 5 * p.1) = (fun x => 2 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (4 * (y-5) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 - 5 * p.2) = (fun x => 2 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - c) (x-3, y-3) (3, 3) = 0) → (3 * (4 * (x-3) + 1) + 3 * (4 * (y-3) ^ 3 + 6 * (y-3) ^ 2 + 6 * (y-3)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2) (x - 3, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2) (x - 3, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2) (x - 3, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 3)) (3, 3) = 3 * (4 * (x-3) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2) (x - 3, y - 3)) (3, 3) = 3 * (4 * (y-3) ^ 3 + 6 * (y-3) ^ 2 + 6 * (y-3))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2) = (fun x => x ^ 4 + 2 * x ^ 3 + 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 3) (3, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 4 + p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (8 * (x-5) + 3) + 3 * (4 * (y-3) ^ 3 + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 4 + p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 4 + p.2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 5, y - 3)) (5, 3) = 5 * (8 * (x-5) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + 3 * p.1) = (fun x => 4 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + p.2) (x - 5, y - 3)) (5, 3) = 3 * (4 * (y-3) ^ 3 + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + p.2) = (fun x => x ^ 4 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 + p.2 - c) (x-4, y-5) (4, 5) = 0) → (4 * (6 * (x-4) - 2) + 5 * (2 * (y-5) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 + p.2) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 5)) (4, 5) = 4 * (6 * (x-4) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 5)) (4, 5) = 5 * (2 * (y-5) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + p.2) = (fun x => x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 3 * p.1 ^ 2 - 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + p.2 ^ 2 - 2 * p.2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (15 * (x-5) ^ 2 - 6 * (x-5)) - 6 * (8 * (y-6) ^ 3 - 12 * (y-6) ^ 2 - 2 * (y-6) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - p.2 ^ 2 + 2 * p.2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 3 * p.1 ^ 2 - 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + p.2 ^ 2 - 2 * p.2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2) (x - 5, y - 6) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - p.2 ^ 2 + 2 * p.2) (x - 5, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 3 * p.1 ^ 2) (x - 5, y - 6)) (5, 6) = 5 * (15 * (x-5) ^ 2 - 6 * (x-5))  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 3 * p.1 ^ 2) = (fun x => 5 * x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - p.2 ^ 2 + 2 * p.2) (x - 5, y - 6)) (5, 6) = 6 * (8 * (y-6) ^ 3 - 12 * (y-6) ^ 2 - 2 * (y-6) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - p.2 ^ 2 + 2 * p.2) = (fun x => 2 * x ^ 4 - 4 * x ^ 3 - x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 5 * p.1 + 3 * p.2 ^ 2 + p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (10 * (x-6) - 5) + 4 * (6 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 5 * p.1 + 3 * p.2 ^ 2 + p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (10 * (x-6) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 5 * p.1) = (fun x => 5 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + p.2) (x - 6, y - 4)) (6, 4) = 4 * (6 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + p.2) = (fun x => 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (6 * (x-6) + 2) + 4 * (15 * (y-4) ^ 2 - 2 * (y-4) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (6 * (x-6) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 2 * p.1) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (15 * (y-4) ^ 2 - 2 * (y-4) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) = (fun x => 5 * x ^ 3 - x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 3 * p.1 - 3 * p.2 ^ 2 + p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (9 * (x-2) ^ 2 - 3) - 5 * (6 * (y-5) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 3 * p.1 - 3 * p.2 ^ 2 + p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 5) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 2, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 5)) (2, 5) = 2 * (9 * (x-2) ^ 2 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 3 * p.1) = (fun x => 3 * x ^ 3 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) (x - 2, y - 5)) (2, 5) = 5 * (6 * (y-5) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 - p.2) = (fun x => 3 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - p.1 - p.2 ^ 4 + 2 * p.2 ^ 3 + 2 * p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (15 * (x-5) ^ 2 - 1) - 3 * (4 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - p.1 - p.2 ^ 4 + 2 * p.2 ^ 3 + 2 * p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - p.1) (x - 5, y - 3) -
      fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2) (x - 5, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - p.1) (x - 5, y - 3)) (5, 3) = 5 * (15 * (x-5) ^ 2 - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - p.1) = (fun x => 5 * x ^ 3 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2) (x - 5, y - 3)) (5, 3) = 3 * (4 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2) = (fun x => x ^ 4 - 2 * x ^ 3 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (2 * (x-6) + 5) + 2 * (15 * (y-2) ^ 2 + 10 * (y-2) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 5 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 5 * p.1) (x - 6, y - 2) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 5 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (2 * (x-6) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 5 * p.1) = (fun x => x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)) (6, 2) = 2 * (15 * (y-2) ^ 2 + 10 * (y-2) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) = (fun x => 5 * x ^ 3 + 5 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 2 + p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (2 * (x-6) - 4) - 2 * (4 * (y-2) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 2 + p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 6, y - 2) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) (x - 6, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (2 * (x-6) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) (x - 6, y - 2)) (6, 2) = 2 * (4 * (y-2) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 - p.2) = (fun x => 2 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (2 * (x-5) + 2) + 3 * (8 * (y-3) ^ 3 - 6 * (y-3) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 5, y - 3)) (5, 3) = 5 * (2 * (x-5) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2) (x - 5, y - 3)) (5, 3) = 3 * (8 * (y-3) ^ 3 - 6 * (y-3) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - 3 * p.2 ^ 2 - 3 * p.2) = (fun x => 2 * x ^ 4 - 3 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 2 + 2 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (2 * (x-3) + 4) + 2 * (6 * (y-2) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (2 * (x-3) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 4 * p.1) = (fun x => x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (6 * (y-2) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 2 * p.2) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 3 + p.2 ^ 2 + 4 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (12 * (x-3) ^ 3 - 10 * (x-3) - 2) - 2 * (6 * (y-2) ^ 2 - 2 * (y-2) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 3 + p.2 ^ 2 + 4 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (12 * (x-3) ^ 3 - 10 * (x-3) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 - 5 * p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 4 - 5 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (6 * (y-2) ^ 2 - 2 * (y-2) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - p.2 ^ 2 - 4 * p.2) = (fun x => 2 * x ^ 3 - x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1 + p.2 ^ 2 + 4 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (12 * (x-4) ^ 2 + 4 * (x-4) + 4) + 2 * (2 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1 + p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (12 * (x-4) ^ 2 + 4 * (x-4) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) = (fun x => 4 * x ^ 3 + 2 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (2 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 4 * p.2) = (fun x => x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 5 * p.1 ^ 2 - p.2 ^ 3 - 3 * p.2 ^ 2 - p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (12 * (x-3) ^ 2 + 10 * (x-3)) - 4 * (3 * (y-4) ^ 2 + 6 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 5 * p.1 ^ 2 - p.2 ^ 3 - 3 * p.2 ^ 2 - p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 4) -
      fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 3, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 4)) (3, 4) = 3 * (12 * (x-3) ^ 2 + 10 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 5 * p.1 ^ 2) = (fun x => 4 * x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) (x - 3, y - 4)) (3, 4) = 4 * (3 * (y-4) ^ 2 + 6 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 3 * p.2 ^ 2 + p.2) = (fun x => x ^ 3 + 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 2 + 3 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (6 * (x-6) ^ 2 + 4 * (x-6) + 5) + 4 * (10 * (y-4) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (6 * (x-6) ^ 2 + 4 * (x-6) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 5 * p.1) = (fun x => 2 * x ^ 3 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (10 * (y-4) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - p.1 - 2 * p.2 ^ 2 - 5 * p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (10 * (x-2) - 1) - 5 * (4 * (y-5) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - p.1 - 2 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 2, y - 5) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 2, y - 5)) (2, 5) = 2 * (10 * (x-2) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 5)) (2, 5) = 5 * (4 * (y-5) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1 - p.2 ^ 3 + 3 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (15 * (x-3) ^ 2 + 8 * (x-3) - 4) - 5 * (3 * (y-5) ^ 2 - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 3 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1 - p.2 ^ 3 + 3 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1) (x - 3, y - 5) -
      fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1) (x - 3, y - 5)) (3, 5) = 3 * (15 * (x-3) ^ 2 + 8 * (x-3) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 4 * p.1 ^ 2 - 4 * p.1) = (fun x => 5 * x ^ 3 + 4 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (3 * (y-5) ^ 2 - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 3 * p.2) = (fun x => x ^ 3 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (2 * (x-6) + 2) + 2 * (12 * (y-2) ^ 2 + 10 * (y-2) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (2 * (x-6) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) (x - 6, y - 2)) (6, 2) = 2 * (12 * (y-2) ^ 2 + 10 * (y-2) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) = (fun x => 4 * x ^ 3 + 5 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2 - 4 * p.2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (6 * (x-2) - 5) + 3 * (2 * (y-3) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 4 * p.2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2 - 4 * p.2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 2, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) (x - 2, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 2, y - 3)) (2, 3) = 2 * (6 * (x-2) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) (x - 2, y - 3)) (2, 3) = 3 * (2 * (y-3) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - 4 * p.2) = (fun x => x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + p.1 ^ 2 + p.2 ^ 3 - p.2 ^ 2 - 2 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (6 * (x-4) ^ 2 + 2 * (x-4)) + 2 * (3 * (y-2) ^ 2 - 2 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + p.1 ^ 2) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + p.1 ^ 2 + p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + p.1 ^ 2) (x - 4, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + p.1 ^ 2) (x - 4, y - 2)) (4, 2) = 4 * (6 * (x-4) ^ 2 + 2 * (x-4))  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + p.1 ^ 2) = (fun x => 2 * x ^ 3 + x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (3 * (y-2) ^ 2 - 2 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 3 - x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.2 ^ 2 + p.2 - c) (x-3, y-6) (3, 6) = 0) → (3 * (12 * (x-3) ^ 2 - 2 * (x-3)) + 6 * (8 * (y-6) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2) (x - 3, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 3, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.2 ^ 2 + p.2) (x - 3, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2) (x - 3, y - 6) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 3, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2) (x - 3, y - 6)) (3, 6) = 3 * (12 * (x-3) ^ 2 - 2 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - p.1 ^ 2) = (fun x => 4 * x ^ 3 - x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 3, y - 6)) (3, 6) = 6 * (8 * (y-6) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + p.2) = (fun x => 4 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 6) (3, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 2 + 4 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (6 * (x-5) + 2) + 5 * (2 * (y-5) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (6 * (x-5) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 2 * p.1) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (2 * (y-5) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 4 * p.2) = (fun x => x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 4 * p.2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (4 * (x-2) + 2) - 3 * (8 * (y-3) ^ 3 - 12 * (y-3) ^ 2 - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 4 + 4 * p.2 ^ 3 + 4 * p.2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 2, y - 3) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2) (x - 2, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + 2 * p.1) (x - 2, y - 3)) (2, 3) = 2 * (4 * (x-2) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 2 * p.1) = (fun x => 2 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2) (x - 2, y - 3)) (2, 3) = 3 * (8 * (y-3) ^ 3 - 12 * (y-3) ^ 2 - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - 4 * p.2 ^ 3 - 4 * p.2) = (fun x => 2 * x ^ 4 - 4 * x ^ 3 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.1 - 2 * p.2 ^ 2 - 5 * p.2 - c) (x-6, y-5) (6, 5) = 0) → (6 * (2 * (x-6) + 1) - 5 * (4 * (y-5) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + p.1) (x - 6, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + p.1 - 2 * p.2 ^ 2 - 5 * p.2) (x - 6, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 6, y - 5) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + p.1) (x - 6, y - 5)) (6, 5) = 6 * (2 * (x-6) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) = (fun x => x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 5)) (6, 5) = 5 * (4 * (y-5) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 5) (6, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 ^ 2 - p.2 - c) (x-2, y-6) (2, 6) = 0) → (2 * (10 * (x-2) + 5) - 6 * (8 * (y-6) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 ^ 2 - p.2) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 2, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 6)) (2, 6) = 2 * (10 * (x-2) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 5 * p.1) = (fun x => 5 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) (x - 2, y - 6)) (2, 6) = 6 * (8 * (y-6) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + p.2) = (fun x => 4 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1 + 4 * p.2 ^ 2 - 4 * p.2 - c) (x-2, y-2) (2, 2) = 0) → (2 * (8 * (x-2) ^ 3 + 4 * (x-2) + 5) + 2 * (8 * (y-2) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 - 4 * p.2) (x - 2, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1 + 4 * p.2 ^ 2 - 4 * p.2) (x - 2, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 2) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 - 4 * p.2) (x - 2, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 2)) (2, 2) = 2 * (8 * (x-2) ^ 3 + 4 * (x-2) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + 2 * p.1 ^ 2 + 5 * p.1) = (fun x => 2 * x ^ 4 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 - 4 * p.2) (x - 2, y - 2)) (2, 2) = 2 * (8 * (y-2) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 - 4 * p.2) = (fun x => 4 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 2) (2, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3 + p.2 ^ 2 + 3 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (15 * (x-5) ^ 2 - 2) - 5 * (9 * (y-5) ^ 2 - 2 * (y-5) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1) (x - 5, y - 5) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (15 * (x-5) ^ 2 - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 2 * p.1) = (fun x => 5 * x ^ 3 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (9 * (y-5) ^ 2 - 2 * (y-5) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) = (fun x => 3 * x ^ 3 - x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 2 + 5 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (10 * (x-3) - 2) + 2 * (4 * (y-2) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (10 * (x-3) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (4 * (y-2) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 3 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + p.2 ^ 2 - c) (x-2, y-6) (2, 6) = 0) → (2 * (9 * (x-2) ^ 2 - 3) - 6 * (16 * (y-6) ^ 3 - 9 * (y-6) ^ 2 - 2 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2 ^ 2) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 3 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + p.2 ^ 2) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2 ^ 2) (x - 2, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 2, y - 6)) (2, 6) = 2 * (9 * (x-2) ^ 2 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 3 * p.1) = (fun x => 3 * x ^ 3 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2 ^ 2) (x - 2, y - 6)) (2, 6) = 6 * (16 * (y-6) ^ 3 - 9 * (y-6) ^ 2 - 2 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2 ^ 2) = (fun x => 4 * x ^ 4 - 3 * x ^ 3 - x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 2 * p.1 + p.2 ^ 3 - 2 * p.2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (3 * (x-6) ^ 2 - 2) + 6 * (3 * (y-6) ^ 2 - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 2 * p.1) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 2 * p.2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 2 * p.1 + p.2 ^ 3 - 2 * p.2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 2 * p.1) (x - 6, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2) (x - 6, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 2 * p.1) (x - 6, y - 6)) (6, 6) = 6 * (3 * (x-6) ^ 2 - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 2 * p.1) = (fun x => x ^ 3 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2) (x - 6, y - 6)) (6, 6) = 6 * (3 * (y-6) ^ 2 - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 2 * p.2) = (fun x => x ^ 3 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (2 * (x-4) - 2) - 6 * (8 * (y-6) ^ 3 + 6 * (y-6) ^ 2 + 10 * (y-6) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 2 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (2 * (x-4) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 2 * p.1) = (fun x => x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 6)) (4, 6) = 6 * (8 * (y-6) ^ 3 + 6 * (y-6) ^ 2 + 10 * (y-6) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 2 * p.2) = (fun x => 2 * x ^ 4 + 2 * x ^ 3 + 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + p.1 ^ 2 + 4 * p.1 + 2 * p.2 ^ 2 + 2 * p.2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (4 * (x-2) ^ 3 + 2 * (x-2) + 4) + 3 * (4 * (y-3) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + p.1 ^ 2 + 4 * p.1) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + p.1 ^ 2 + 4 * p.1 + 2 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 2 + 4 * p.1) (x - 2, y - 3) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 2 + 4 * p.1) (x - 2, y - 3)) (2, 3) = 2 * (4 * (x-2) ^ 3 + 2 * (x-2) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + p.1 ^ 2 + 4 * p.1) = (fun x => x ^ 4 + x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 3)) (2, 3) = 3 * (4 * (y-3) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 2 * p.2) = (fun x => 2 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (6 * (x-6) + 2) + 6 * (3 * (y-6) ^ 2 - 10 * (y-6) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) (x - 6, y - 6)) (6, 6) = 6 * (6 * (x-6) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 2 * p.1) = (fun x => 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 6, y - 6)) (6, 6) = 6 * (3 * (y-6) ^ 2 - 10 * (y-6) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 3 - 5 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (12 * (x-5) ^ 3 - 12 * (x-5) ^ 2 - 6 * (x-5) + 1) + 5 * (15 * (y-5) ^ 2 - 8 * (y-5)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1) (x - 5, y - 5)) (5, 5) = 5 * (12 * (x-5) ^ 3 - 12 * (x-5) ^ 2 - 6 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 - 4 * p.1 ^ 3 - 3 * p.1 ^ 2 + p.1) = (fun x => 3 * x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2) (x - 5, y - 5)) (5, 5) = 5 * (15 * (y-5) ^ 2 - 8 * (y-5))  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 4 * p.2 ^ 2) = (fun x => 5 * x ^ 3 - 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 4 * p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (9 * (x-2) ^ 2 - 4 * (x-2) + 4) - 5 * (6 * (y-5) ^ 2 + 10 * (y-5) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 4 * p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 4 * p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1) (x - 2, y - 5) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 4 * p.2) (x - 2, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1) (x - 2, y - 5)) (2, 5) = 2 * (9 * (x-2) ^ 2 - 4 * (x-2) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 4 * p.1) = (fun x => 3 * x ^ 3 - 2 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 4 * p.2) (x - 2, y - 5)) (2, 5) = 5 * (6 * (y-5) ^ 2 + 10 * (y-5) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 4 * p.2) = (fun x => 2 * x ^ 3 + 5 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1 - 3 * p.2 ^ 4 + 2 * p.2 ^ 3 + p.2 ^ 2 + 3 * p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (15 * (x-5) ^ 2 + 4 * (x-5) + 1) - 3 * (12 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 2 * (y-3) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1 - 3 * p.2 ^ 4 + 2 * p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 5, y - 3) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) (x - 5, y - 3)) (5, 3) = 5 * (15 * (x-5) ^ 2 + 4 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 + p.1) = (fun x => 5 * x ^ 3 + 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) (x - 5, y - 3)) (5, 3) = 3 * (12 * (y-3) ^ 3 - 6 * (y-3) ^ 2 - 2 * (y-3) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - 2 * p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) = (fun x => 3 * x ^ 4 - 2 * x ^ 3 - x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) (x-4, y-5) (4, 5) = 0) → (4 * (12 * (x-4) ^ 2 + 2 * (x-4) - 4) + 5 * (4 * (y-5) ^ 3 + 15 * (y-5) ^ 2 + 2 * (y-5)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1) (x - 4, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1) (x - 4, y - 5)) (4, 5) = 4 * (12 * (x-4) ^ 2 + 2 * (x-4) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + p.1 ^ 2 - 4 * p.1) = (fun x => 4 * x ^ 3 + x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 5)) (4, 5) = 5 * (4 * (y-5) ^ 3 + 15 * (y-5) ^ 2 + 2 * (y-5))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) = (fun x => x ^ 4 + 5 * x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 4 - 3 * p.2 ^ 2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (4 * (x-5) + 1) + 3 * (16 * (y-3) ^ 3 - 6 * (y-3)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 4 - 3 * p.2 ^ 2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 5, y - 3)) (5, 3) = 5 * (4 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 2) (x - 5, y - 3)) (5, 3) = 3 * (16 * (y-3) ^ 3 - 6 * (y-3))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 3 * p.2 ^ 2) = (fun x => 4 * x ^ 4 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 + p.2 - c) (x-5, y-3) (5, 3) = 0) → (5 * (8 * (x-5) ^ 3 - 12 * (x-5) ^ 2 + 6 * (x-5) - 3) + 3 * (2 * (y-3) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) (x - 5, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 + p.2) (x - 5, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 5, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 3)) (5, 3) = 5 * (8 * (x-5) ^ 3 - 12 * (x-5) ^ 2 + 6 * (x-5) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 4 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 2 * x ^ 4 - 4 * x ^ 3 + 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 5, y - 3)) (5, 3) = 3 * (2 * (y-3) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + p.2) = (fun x => x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 3) (5, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1 + p.2 ^ 2 + p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (8 * (x-4) ^ 3 - 6 * (x-4) ^ 2 - 2) + 6 * (2 * (y-6) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1 + p.2 ^ 2 + p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1) (x - 4, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (8 * (x-4) ^ 3 - 6 * (x-4) ^ 2 - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 - 2 * p.1) = (fun x => 2 * x ^ 4 - 2 * x ^ 3 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 4, y - 6)) (4, 6) = 6 * (2 * (y-6) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + p.2) = (fun x => x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.2 ^ 2 + p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (6 * (x-4) ^ 2 - 10 * (x-4)) + 4 * (10 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 4, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 4, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 4, y - 4)) (4, 4) = 4 * (6 * (x-4) ^ 2 - 10 * (x-4))  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 5 * p.1 ^ 2) = (fun x => 2 * x ^ 3 - 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)) (4, 4) = 4 * (10 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.2 ^ 2 + 5 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (3 * (x-3) ^ 2 + 10 * (x-3)) - 5 * (10 * (y-5) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 5) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) (x - 3, y - 5)) (3, 5) = 3 * (3 * (x-3) ^ 2 + 10 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 5 * p.1 ^ 2) = (fun x => x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (10 * (y-5) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 5 * p.2) = (fun x => 5 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 + 5 * p.2 - c) (x-6, y-2) (6, 2) = 0) → (6 * (2 * (x-6) + 2) + 2 * (3 * (y-2) ^ 2 + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 5 * p.2) (x - 6, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + p.2 ^ 3 + 5 * p.2) (x - 6, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 + 5 * p.2) (x - 6, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 6, y - 2)) (6, 2) = 6 * (2 * (x-6) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 5 * p.2) (x - 6, y - 2)) (6, 2) = 2 * (3 * (y-2) ^ 2 + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 5 * p.2) = (fun x => x ^ 3 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 2) (6, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 5 * p.1 - p.2 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (10 * (x-5) - 5) - 2 * (3 * (y-2) ^ 2 - 2 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 5 * p.1 - p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 2) -
      fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 5, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) (x - 5, y - 2)) (5, 2) = 5 * (10 * (x-5) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 5 * p.1) = (fun x => 5 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) (x - 5, y - 2)) (5, 2) = 2 * (3 * (y-2) ^ 2 - 2 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 3 - x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 5 * p.2 - c) (x-2, y-6) (2, 6) = 0) → (2 * (2 * (x-2) - 4) - 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 10 * (y-6) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 5 * p.2) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 2, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 2, y - 6)) (2, 6) = 2 * (2 * (x-2) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 2, y - 6)) (2, 6) = 6 * (16 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 10 * (y-6) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) = (fun x => 4 * x ^ 4 - 2 * x ^ 3 - 5 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1 - 4 * p.2 ^ 4 - 4 * p.2 ^ 3 + p.2 ^ 2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (6 * (x-4) ^ 2 + 4 * (x-4) + 4) - 6 * (16 * (y-6) ^ 3 + 12 * (y-6) ^ 2 - 2 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 + 4 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1 - 4 * p.2 ^ 4 - 4 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 + 4 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (6 * (x-4) ^ 2 + 4 * (x-4) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.1) = (fun x => 2 * x ^ 3 + 2 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 + 4 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 6)) (4, 6) = 6 * (16 * (y-6) ^ 3 + 12 * (y-6) ^ 2 - 2 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 + 4 * p.2 ^ 3 - p.2 ^ 2) = (fun x => 4 * x ^ 4 + 4 * x ^ 3 - x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 4 * p.1 ^ 2 - 5 * p.2 ^ 2 - 3 * p.2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (3 * (x-2) ^ 2 + 8 * (x-2)) - 3 * (10 * (y-3) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 4 * p.1 ^ 2 - 5 * p.2 ^ 2 - 3 * p.2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2) (x - 2, y - 3) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 2, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2) (x - 2, y - 3)) (2, 3) = 2 * (3 * (x-2) ^ 2 + 8 * (x-2))  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) (x - 2, y - 3)) (2, 3) = 3 * (10 * (y-3) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 2 + p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (10 * (x-4) + 5) - 3 * (2 * (y-3) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 2 + p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 4, y - 3) -
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 4, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (10 * (x-4) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 5 * p.1) = (fun x => 5 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 4, y - 3)) (4, 3) = 3 * (2 * (y-3) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - p.2) = (fun x => x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (10 * (x-4) + 4) + 2 * (9 * (y-2) ^ 2 + 4 * (y-2)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 4 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (10 * (x-4) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 4 * p.1) = (fun x => 5 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 4, y - 2)) (4, 2) = 2 * (9 * (y-2) ^ 2 + 4 * (y-2))  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 2 * p.2 ^ 2) = (fun x => 3 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 + 2 * p.2 ^ 2 - 2 * p.2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (2 * (x-5) - 4) + 6 * (4 * (y-6) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 4 * p.1 + 2 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 5, y - 6) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) (x - 5, y - 6)) (5, 6) = 5 * (2 * (x-5) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 6)) (5, 6) = 6 * (4 * (y-6) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 - 2 * p.2) = (fun x => 2 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - p.1 + p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (10 * (x-4) - 1) + 2 * (3 * (y-2) ^ 2 + 8 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - p.1 + p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 2)) (4, 2) = 4 * (10 * (x-4) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (3 * (y-2) ^ 2 + 8 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 3 + 4 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 5 * p.1 - 4 * p.2 ^ 2 - 5 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (2 * (x-5) - 5) - 4 * (8 * (y-4) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 5 * p.1 - 4 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 5 * p.1) (x - 5, y - 4)) (5, 4) = 5 * (2 * (x-5) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - 5 * p.1) = (fun x => x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (8 * (y-4) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + 5 * p.2) = (fun x => 4 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 2 + p.2 - c) (x-6, y-5) (6, 5) = 0) → (6 * (15 * (x-6) ^ 2 - 8 * (x-6) - 2) + 5 * (4 * (y-5) ^ 3 - 6 * (y-5) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 5)) (6, 5) = 6 * (15 * (x-6) ^ 2 - 8 * (x-6) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 3 - 4 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 5)) (6, 5) = 5 * (4 * (y-5) ^ 3 - 6 * (y-5) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2 ^ 2 + p.2) = (fun x => x ^ 4 - 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 5) (6, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (16 * (x-3) ^ 3 - 3 * (x-3) ^ 2 - 10 * (x-3) - 1) - 2 * (8 * (y-2) ^ 3 + 3 * (y-2) ^ 2 - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 2 * p.2 ^ 4 - p.2 ^ 3 + p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 3, y - 2) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2) (x - 3, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 3, y - 2)) (3, 2) = 3 * (16 * (x-3) ^ 3 - 3 * (x-3) ^ 2 - 10 * (x-3) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) = (fun x => 4 * x ^ 4 - x ^ 3 - 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2) (x - 3, y - 2)) (3, 2) = 2 * (8 * (y-2) ^ 3 + 3 * (y-2) ^ 2 - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2) = (fun x => 2 * x ^ 4 + x ^ 3 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 3 * p.1 + 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (2 * (x-5) + 3) + 5 * (12 * (y-5) ^ 3 - 4 * (y-5) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 3 * p.1 + 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (2 * (x-5) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 3 * p.1) = (fun x => x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (12 * (y-5) ^ 3 - 4 * (y-5) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 - 4 * p.2) = (fun x => 3 * x ^ 4 - 2 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 3 + p.2 ^ 2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (10 * (x-4) - 1) - 3 * (9 * (y-3) ^ 2 - 2 * (y-3)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 3 + p.2 ^ 2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 3) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 4, y - 3)) (4, 3) = 4 * (10 * (x-4) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - p.2 ^ 2) (x - 4, y - 3)) (4, 3) = 3 * (9 * (y-3) ^ 2 - 2 * (y-3))  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - p.2 ^ 2) = (fun x => 3 * x ^ 3 - x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (3 * (x-3) ^ 2 - 10 * (x-3)) + 2 * (6 * (y-2) ^ 2 + 4 * (y-2) - 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2) (x - 3, y - 2) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2) (x - 3, y - 2)) (3, 2) = 3 * (3 * (x-3) ^ 2 - 10 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 5 * p.1 ^ 2) = (fun x => x ^ 3 - 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (6 * (y-2) ^ 2 + 4 * (y-2) - 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 2 * p.2) = (fun x => 2 * x ^ 3 + 2 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 3 * p.1 + p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (2 * (x-3) + 3) + 2 * (3 * (y-2) ^ 2 - 10 * (y-2) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 3 * p.1 + p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (2 * (x-3) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 3 * p.1) = (fun x => x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) (x - 3, y - 2)) (3, 2) = 2 * (3 * (y-2) ^ 2 - 10 * (y-2) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) = (fun x => x ^ 3 - 5 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (4 * (x-4) ^ 3 + 15 * (x-4) ^ 2 + 10 * (x-4) - 3) + 4 * (3 * (y-4) ^ 2 - 4 * (y-4) - 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 4) +
      fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 4)) (4, 4) = 4 * (4 * (x-4) ^ 3 + 15 * (x-4) ^ 2 + 10 * (x-4) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 5 * p.1 ^ 3 + 5 * p.1 ^ 2 - 3 * p.1) = (fun x => x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2) (x - 4, y - 4)) (4, 4) = 4 * (3 * (y-4) ^ 2 - 4 * (y-4) - 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 2 * p.2 ^ 2 - 4 * p.2) = (fun x => x ^ 3 - 2 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 ^ 2 - p.1 + p.2 ^ 2 - 5 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (3 * (x-3) ^ 2 + 2 * (x-3) - 1) + 5 * (2 * (y-5) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + p.1 ^ 2 - p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + p.1 ^ 2 - p.1 + p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + p.1 ^ 2 - p.1) (x - 3, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 2 - 5 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + p.1 ^ 2 - p.1) (x - 3, y - 5)) (3, 5) = 3 * (3 * (x-3) ^ 2 + 2 * (x-3) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + p.1 ^ 2 - p.1) = (fun x => x ^ 3 + x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 5 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (2 * (y-5) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - 5 * p.2) = (fun x => x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 + p.2 - c) (x-2, y-3) (2, 3) = 0) → (2 * (10 * (x-2) - 2) + 3 * (2 * (y-3) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 2, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) (x - 2, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 + p.2) (x - 2, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 2, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 2, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) (x - 2, y - 3)) (2, 3) = 2 * (10 * (x-2) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) (x - 2, y - 3)) (2, 3) = 3 * (2 * (y-3) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + p.2) = (fun x => x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 3) (2, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (20 * (x-6) ^ 3 - 4 * (x-6) + 4) + 6 * (15 * (y-6) ^ 2 - 8 * (y-6) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1 + 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1) (x - 6, y - 6) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1) (x - 6, y - 6)) (6, 6) = 6 * (20 * (x-6) ^ 3 - 4 * (x-6) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 - 2 * p.1 ^ 2 + 4 * p.1) = (fun x => 5 * x ^ 4 - 2 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) (x - 6, y - 6)) (6, 6) = 6 * (15 * (y-6) ^ 2 - 8 * (y-6) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) = (fun x => 5 * x ^ 3 - 4 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 3 * p.1 + p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 - c) (x-6, y-6) (6, 6) = 0) → (6 * (16 * (x-6) ^ 3 - 3) + 6 * (4 * (y-6) ^ 3 + 3 * (y-6) ^ 2 - 6 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 3 * p.1) (x - 6, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2) (x - 6, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - 3 * p.1 + p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2) (x - 6, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - 3 * p.1) (x - 6, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2) (x - 6, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 3 * p.1) (x - 6, y - 6)) (6, 6) = 6 * (16 * (x-6) ^ 3 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 3 * p.1) = (fun x => 4 * x ^ 4 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2) (x - 6, y - 6)) (6, 6) = 6 * (4 * (y-6) ^ 3 + 3 * (y-6) ^ 2 - 6 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2) = (fun x => x ^ 4 + x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 6) (6, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (12 * (x-5) ^ 3 + 15 * (x-5) ^ 2 + 2 * (x-5) - 2) + 6 * (4 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 10 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 5, y - 6) +
      fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 5, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) (x - 5, y - 6)) (5, 6) = 5 * (12 * (x-5) ^ 3 + 15 * (x-5) ^ 2 + 2 * (x-5) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 4 + 5 * x ^ 3 + x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
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
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 5, y - 6)) (5, 6) = 6 * (4 * (y-6) ^ 3 - 6 * (y-6) ^ 2 - 10 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) = (fun x => x ^ 4 - 2 * x ^ 3 - 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) (x-3, y-6) (3, 6) = 0) → (3 * (16 * (x-3) ^ 3 + 3 * (x-3) ^ 2 + 2 * (x-3)) - 6 * (16 * (y-6) ^ 3 - 9 * (y-6) ^ 2 - 4 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2) (x - 3, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2) (x - 3, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2) (x - 3, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2) (x - 3, y - 6)) (3, 6) = 3 * (16 * (x-3) ^ 3 + 3 * (x-3) ^ 2 + 2 * (x-3))  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + p.1 ^ 3 + p.1 ^ 2) = (fun x => 4 * x ^ 4 + x ^ 3 + x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2) (x - 3, y - 6)) (3, 6) = 6 * (16 * (y-6) ^ 3 - 9 * (y-6) ^ 2 - 4 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2) = (fun x => 4 * x ^ 4 - 3 * x ^ 3 - 2 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 6) (3, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 - p.2 ^ 2 - 5 * p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (4 * (x-3) + 1) - 4 * (2 * (y-4) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + p.1 - p.2 ^ 2 - 5 * p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 4) -
      fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 4)) (3, 4) = 3 * (4 * (x-3) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4)) (3, 4) = 4 * (2 * (y-4) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 3 * p.1 + 3 * p.2 ^ 2 + 5 * p.2 - c) (x-4, y-2) (4, 2) = 0) → (4 * (9 * (x-4) ^ 2 - 3) + 2 * (6 * (y-2) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 4, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 3 * p.1 + 3 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 2)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 4, y - 2) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 3 * p.1) (x - 4, y - 2)) (4, 2) = 4 * (9 * (x-4) ^ 2 - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 3 * p.1) = (fun x => 3 * x ^ 3 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 2)) (4, 2) = 2 * (6 * (y-2) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 2) (4, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (9 * (x-5) ^ 2 + 3) - 5 * (16 * (y-5) ^ 3 - 6 * (y-5) ^ 2 - 10 * (y-5) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 3 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - 4 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1) (x - 5, y - 5) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (9 * (x-5) ^ 2 + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 3 * p.1) = (fun x => 3 * x ^ 3 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (16 * (y-5) ^ 3 - 6 * (y-5) ^ 2 - 10 * (y-5) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 + 4 * p.2) = (fun x => 4 * x ^ 4 - 2 * x ^ 3 - 5 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 5 * p.1 ^ 2 - 5 * p.2 ^ 2 + p.2 - c) (x-4, y-4) (4, 4) = 0) → (4 * (20 * (x-4) ^ 3 - 10 * (x-4)) - 4 * (10 * (y-4) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 - 5 * p.1 ^ 2) (x - 4, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - p.2) (x - 4, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 - 5 * p.1 ^ 2 - 5 * p.2 ^ 2 + p.2) (x - 4, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 - 5 * p.1 ^ 2) (x - 4, y - 4) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) (x - 4, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 - 5 * p.1 ^ 2) (x - 4, y - 4)) (4, 4) = 4 * (20 * (x-4) ^ 3 - 10 * (x-4))  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 - 5 * p.1 ^ 2) = (fun x => 5 * x ^ 4 - 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) (x - 4, y - 4)) (4, 4) = 4 * (10 * (y-4) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - p.2) = (fun x => 5 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 4) (4, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 + 4 * p.2 ^ 2 + 5 * p.2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (15 * (x-5) ^ 2 - 10 * (x-5) - 1) + 6 * (8 * (y-6) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 + 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 5, y - 6) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 6) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) (x - 5, y - 6)) (5, 6) = 5 * (15 * (x-5) ^ 2 - 10 * (x-5) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 3 - 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 6)) (5, 6) = 6 * (8 * (y-6) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + 5 * p.2) = (fun x => 4 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 - 4 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) (x-2, y-6) (2, 6) = 0) → (2 * (2 * (x-2) + 2) - 6 * (12 * (y-6) ^ 2 - 2 * (y-6) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 2, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - p.2 ^ 2 - p.2) (x - 2, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 - 4 * p.2 ^ 3 + p.2 ^ 2 + p.2) (x - 2, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 2, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - p.2 ^ 2 - p.2) (x - 2, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) (x - 2, y - 6)) (2, 6) = 2 * (2 * (x-2) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - p.2 ^ 2 - p.2) (x - 2, y - 6)) (2, 6) = 6 * (12 * (y-6) ^ 2 - 2 * (y-6) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - p.2 ^ 2 - p.2) = (fun x => 4 * x ^ 3 - x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 6) (2, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (2 * (x-3) + 4) + 5 * (12 * (y-5) ^ 3 + 15 * (y-5) ^ 2 + 6 * (y-5) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 4 * p.1) (x - 3, y - 5)) (3, 5) = 3 * (2 * (x-3) + 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + 4 * p.1) = (fun x => x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (12 * (y-5) ^ 3 + 15 * (y-5) ^ 2 + 6 * (y-5) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1 - 5 * p.2 ^ 2 + 5 * p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (12 * (x-4) ^ 3 + 6 * (x-4) ^ 2 - 10 * (x-4) - 2) - 3 * (10 * (y-3) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1 - 5 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (12 * (x-4) ^ 3 + 6 * (x-4) ^ 2 - 10 * (x-4) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 4 + 2 * x ^ 3 - 5 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 3)) (4, 3) = 3 * (10 * (y-3) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 5 * p.2) = (fun x => 5 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 2 + 3 * p.2 - c) (x-2, y-2) (2, 2) = 0) → (2 * (4 * (x-2) - 4) + 2 * (2 * (y-2) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 3 * p.2) (x - 2, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 2 + 3 * p.2) (x - 2, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 2 + 3 * p.2) (x - 2, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 2)) (2, 2) = 2 * (4 * (x-2) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 4 * p.1) = (fun x => 2 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 3 * p.2) (x - 2, y - 2)) (2, 2) = 2 * (2 * (y-2) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 3 * p.2) = (fun x => x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 2) (2, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (15 * (x-5) ^ 2 - 4 * (x-5) + 1) + 4 * (9 * (y-4) ^ 2 + 4 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1) (x - 5, y - 4) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2) (x - 5, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1) (x - 5, y - 4)) (5, 4) = 5 * (15 * (x-5) ^ 2 - 4 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 2 * p.1 ^ 2 + p.1) = (fun x => 5 * x ^ 3 - 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2) (x - 5, y - 4)) (5, 4) = 4 * (9 * (y-4) ^ 2 + 4 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 + p.2) = (fun x => 3 * x ^ 3 + 2 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 + 5 * p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (8 * (x-3) - 3) + 4 * (2 * (y-4) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 + 5 * p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) (x - 3, y - 4) +
      fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (8 * (x-3) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - 3 * p.1) = (fun x => 4 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) (x - 3, y - 4)) (3, 4) = 4 * (2 * (y-4) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (4 * (x-4) - 3) + 3 * (15 * (y-3) ^ 2 - 2 * (y-3) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) (x - 4, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (4 * (x-4) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 3 * p.1) = (fun x => 2 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) (x - 4, y - 3)) (4, 3) = 3 * (15 * (y-3) ^ 2 - 2 * (y-3) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 3 - x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - c) (x-6, y-4) (6, 4) = 0) → (6 * (10 * (x-6) - 3) + 4 * (12 * (y-4) ^ 3 + 9 * (y-4) ^ 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 4) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3) (x - 6, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (10 * (x-6) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 3 * p.1) = (fun x => 5 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3) (x - 6, y - 4)) (6, 4) = 4 * (12 * (y-4) ^ 3 + 9 * (y-4) ^ 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 3 * p.2 ^ 3) = (fun x => 3 * x ^ 4 + 3 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2 - c) (x-5, y-5) (5, 5) = 0) → (5 * (3 * (x-5) ^ 2 + 6 * (x-5) - 4) + 5 * (15 * (y-5) ^ 2 - 2 * (y-5) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1) (x - 5, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1 + 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1) (x - 5, y - 5) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1) (x - 5, y - 5)) (5, 5) = 5 * (3 * (x-5) ^ 2 + 6 * (x-5) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 3 * p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 3 + 3 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) (x - 5, y - 5)) (5, 5) = 5 * (15 * (y-5) ^ 2 - 2 * (y-5) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 3 - x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 5) (5, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (10 * (x-5) - 1) + 2 * (2 * (y-2) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 5, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 5, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - p.1) (x - 5, y - 2)) (5, 2) = 5 * (10 * (x-5) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 5, y - 2)) (5, 2) = 2 * (2 * (y-2) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - p.2) = (fun x => x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (6 * (x-5) - 3) - 4 * (12 * (y-4) ^ 2 + 10 * (y-4)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 3 * p.1 - 4 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 4)) (5, 4) = 5 * (6 * (x-5) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 5, y - 4)) (5, 4) = 4 * (12 * (y-4) ^ 2 + 10 * (y-4))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 5 * p.2 ^ 2) = (fun x => 4 * x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (8 * (x-3) + 3) + 2 * (3 * (y-2) ^ 2 + 2 * (y-2) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + 3 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (8 * (x-3) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + 3 * p.1) = (fun x => 4 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (3 * (y-2) ^ 2 + 2 * (y-2) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) = (fun x => x ^ 3 + x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 2 + 4 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (4 * (x-3) - 5) + 2 * (8 * (y-2) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 2) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 2)) (3, 2) = 3 * (4 * (x-3) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 5 * p.1) = (fun x => 2 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + 4 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (8 * (y-2) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + 4 * p.2) = (fun x => 4 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 3 + p.2 ^ 2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (8 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) - 3) + 2 * (6 * (y-2) ^ 2 + 2 * (y-2)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + p.2 ^ 2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 3 + p.2 ^ 2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 2) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + p.2 ^ 2) (x - 5, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) (x - 5, y - 2)) (5, 2) = 5 * (8 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 6 * (x-5) - 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 2 * x ^ 4 + x ^ 3 + 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + p.2 ^ 2) (x - 5, y - 2)) (5, 2) = 2 * (6 * (y-2) ^ 2 + 2 * (y-2))  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + p.2 ^ 2) = (fun x => 2 * x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.1 + 5 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (6 * (x-5) + 1) + 4 * (15 * (y-4) ^ 2 - 6 * (y-4)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + p.1 + 5 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 5, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4)) (5, 4) = 5 * (6 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + p.1) = (fun x => 3 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 5, y - 4)) (5, 4) = 4 * (15 * (y-4) ^ 2 - 6 * (y-4))  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 3 * p.2 ^ 2) = (fun x => 5 * x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2 - c) (x-5, y-6) (5, 6) = 0) → (5 * (4 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 2) - 6 * (9 * (y-6) ^ 2 + 8 * (y-6)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 2 * p.1) (x - 5, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 5, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2) (x - 5, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 2 * p.1) (x - 5, y - 6) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 5, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + p.1 ^ 3 + 2 * p.1) (x - 5, y - 6)) (5, 6) = 5 * (4 * (x-5) ^ 3 + 3 * (x-5) ^ 2 + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + p.1 ^ 3 + 2 * p.1) = (fun x => x ^ 4 + x ^ 3 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2) (x - 5, y - 6)) (5, 6) = 6 * (9 * (y-6) ^ 2 + 8 * (y-6))  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 4 * p.2 ^ 2) = (fun x => 3 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 6) (5, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 + 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (12 * (x-4) ^ 2 - 5) + 3 * (9 * (y-3) ^ 2 + 2 * (y-3) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 5 * p.1 + 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 3) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2) (x - 4, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (12 * (x-4) ^ 2 - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 5 * p.1) = (fun x => 4 * x ^ 3 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)) (4, 3) = 3 * (9 * (y-3) ^ 2 + 2 * (y-3) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 3 + x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (6 * (x-4) - 2) + 3 * (12 * (y-3) ^ 3 - 4 * (y-3) + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 2 * p.1 + 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (6 * (x-4) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2) (x - 4, y - 3)) (4, 3) = 3 * (12 * (y-3) ^ 3 - 4 * (y-3) + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - 2 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 4 - 2 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 4 * p.1 ^ 2 + 4 * p.2 ^ 2 + 2 * p.2 - c) (x-6, y-5) (6, 5) = 0) → (6 * (15 * (x-6) ^ 2 + 8 * (x-6)) + 5 * (8 * (y-5) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 4 * p.1 ^ 2 + 4 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 5) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) (x - 6, y - 5)) (6, 5) = 6 * (15 * (x-6) ^ 2 + 8 * (x-6))  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => 5 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)) (6, 5) = 5 * (8 * (y-5) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 + 2 * p.2) = (fun x => 4 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 5) (6, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 2 - 2 * p.2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (3 * (x-5) ^ 2 - 10 * (x-5) + 5) - 2 * (4 * (y-2) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 2 - 2 * p.2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1) (x - 5, y - 2) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1) (x - 5, y - 2)) (5, 2) = 5 * (3 * (x-5) ^ 2 - 10 * (x-5) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 5 * p.1 ^ 2 + 5 * p.1) = (fun x => x ^ 3 - 5 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) (x - 5, y - 2)) (5, 2) = 2 * (4 * (y-2) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 2 * p.2) = (fun x => 2 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 - p.2 ^ 4 + 3 * p.2 ^ 2 - 3 * p.2 - c) (x-3, y-2) (3, 2) = 0) → (3 * (4 * (x-3) + 1) - 2 * (4 * (y-2) ^ 3 - 6 * (y-2) + 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + p.1 - p.2 ^ 4 + 3 * p.2 ^ 2 - 3 * p.2) (x - 3, y - 2)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 2) -
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 2) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) (x - 3, y - 2)) (3, 2) = 3 * (4 * (x-3) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 2 + 3 * p.2) (x - 3, y - 2)) (3, 2) = 2 * (4 * (y-2) ^ 3 - 6 * (y-2) + 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2 ^ 2 + 3 * p.2) = (fun x => x ^ 4 - 3 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 2) (3, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2 - c) (x-6, y-3) (6, 3) = 0) → (6 * (6 * (x-6) ^ 2 - 8 * (x-6) - 1) + 3 * (2 * (y-3) - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1) (x - 6, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) (x - 6, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1 + p.2 ^ 2 - p.2) (x - 6, y - 3)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1) (x - 6, y - 3) +
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 6, y - 3) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1) (x - 6, y - 3)) (6, 3) = 6 * (6 * (x-6) ^ 2 - 8 * (x-6) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - p.1) = (fun x => 2 * x ^ 3 - 4 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) (x - 6, y - 3)) (6, 3) = 3 * (2 * (y-3) - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - p.2) = (fun x => x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 3) (6, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2 - c) (x-2, y-4) (2, 4) = 0) → (2 * (20 * (x-2) ^ 3 - 9 * (x-2) ^ 2 - 4 * (x-2) + 5) + 4 * (15 * (y-4) ^ 2 + 6 * (y-4) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 4)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 4) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 4) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) (x - 2, y - 4)) (2, 4) = 2 * (20 * (x-2) ^ 3 - 9 * (x-2) ^ 2 - 4 * (x-2) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) = (fun x => 5 * x ^ 4 - 3 * x ^ 3 - 2 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2) (x - 2, y - 4)) (2, 4) = 4 * (15 * (y-4) ^ 2 + 6 * (y-4) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 3 * p.2 ^ 2 + 2 * p.2) = (fun x => 5 * x ^ 3 + 3 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 4) (2, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - c) (x-2, y-4) (2, 4) = 0) → (2 * (8 * (x-2) ^ 3 - 9 * (x-2) ^ 2 - 2 * (x-2) + 2) - 4 * (6 * (y-4) ^ 2 + 10 * (y-4)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1) (x - 2, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 2, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2) (x - 2, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1) (x - 2, y - 4) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 2, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1) (x - 2, y - 4)) (2, 4) = 2 * (8 * (x-2) ^ 3 - 9 * (x-2) ^ 2 - 2 * (x-2) + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 - p.1 ^ 2 + 2 * p.1) = (fun x => 2 * x ^ 4 - 3 * x ^ 3 - x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) (x - 2, y - 4)) (2, 4) = 4 * (6 * (y-4) ^ 2 + 10 * (y-4))  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) = (fun x => 2 * x ^ 3 + 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 4) (2, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + 3 * p.1 - 4 * p.2 ^ 3 + 3 * p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (16 * (x-3) ^ 3 + 3) - 4 * (12 * (y-4) ^ 2 - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + 3 * p.1 - 4 * p.2 ^ 3 + 3 * p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1) (x - 3, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2) (x - 3, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (16 * (x-3) ^ 3 + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + 3 * p.1) = (fun x => 4 * x ^ 4 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2) (x - 3, y - 4)) (3, 4) = 4 * (12 * (y-4) ^ 2 - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 3 * p.2) = (fun x => 4 * x ^ 3 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 3 * p.1 - 2 * p.2 ^ 2 - 5 * p.2 - c) (x-4, y-3) (4, 3) = 0) → (4 * (10 * (x-4) + 3) - 3 * (4 * (y-3) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 3))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 3 * p.1 - 2 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 3)
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 3) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 3) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 3)) (4, 3) = 4 * (10 * (x-4) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 3 * p.1) = (fun x => 5 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 5 * p.2) (x - 4, y - 3)) (4, 3) = 3 * (4 * (y-3) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 3) (4, 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + p.2 - c) (x-3, y-4) (3, 4) = 0) → (3 * (9 * (x-3) ^ 2 + 8 * (x-3) + 5) - 4 * (16 * (y-4) ^ 3 - 9 * (y-4) ^ 2 - 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1) (x - 3, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2) (x - 3, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 ^ 4 + 3 * p.2 ^ 3 + p.2) (x - 3, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1) (x - 3, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2) (x - 3, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1) (x - 3, y - 4)) (3, 4) = 3 * (9 * (x-3) ^ 2 + 8 * (x-3) + 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.1) = (fun x => 3 * x ^ 3 + 4 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2) (x - 3, y - 4)) (3, 4) = 4 * (16 * (y-4) ^ 3 - 9 * (y-4) ^ 2 - 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 3 * p.2 ^ 3 - p.2) = (fun x => 4 * x ^ 4 - 3 * x ^ 3 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 4) (3, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 5 * p.1 ^ 2 - p.1 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2 - c) (x-4, y-5) (4, 5) = 0) → (4 * (4 * (x-4) ^ 3 + 10 * (x-4) - 1) + 5 * (6 * (y-5) ^ 2 + 4 * (y-5) - 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 2 - p.1) (x - 4, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 5 * p.1 ^ 2 - p.1 + 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 5)
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 2 - p.1) (x - 4, y - 5) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 2 - p.1) (x - 4, y - 5)) (4, 5) = 4 * (4 * (x-4) ^ 3 + 10 * (x-4) - 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 5 * p.1 ^ 2 - p.1) = (fun x => x ^ 4 + 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) (x - 4, y - 5)) (4, 5) = 5 * (6 * (y-5) ^ 2 + 4 * (y-5) - 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) = (fun x => 2 * x ^ 3 + 2 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 5) (4, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 3 + 3 * p.2 ^ 2 - c) (x-2, y-4) (2, 4) = 0) → (2 * (6 * (x-2) - 4) - 4 * (12 * (y-4) ^ 2 - 6 * (y-4)) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 2, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 4 * p.1 - 4 * p.2 ^ 3 + 3 * p.2 ^ 2) (x - 2, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 4) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 2, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 4 * p.1) (x - 2, y - 4)) (2, 4) = 2 * (6 * (x-2) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 4 * p.1) = (fun x => 3 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2) (x - 2, y - 4)) (2, 4) = 4 * (12 * (y-4) ^ 2 - 6 * (y-4))  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 3 * p.2 ^ 2) = (fun x => 4 * x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 4) (2, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1 + 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2 - c) (x-5, y-2) (5, 2) = 0) → (5 * (16 * (x-5) ^ 3 + 3 * (x-5) ^ 2 - 2 * (x-5) - 4) + 2 * (20 * (y-2) ^ 3 + 15 * (y-2) ^ 2 + 4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1) (x - 5, y - 2))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2) (x - 5, y - 2)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1 + 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2) (x - 5, y - 2)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1) (x - 5, y - 2) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2) (x - 5, y - 2) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1) (x - 5, y - 2)) (5, 2) = 5 * (16 * (x-5) ^ 3 + 3 * (x-5) ^ 2 - 2 * (x-5) - 4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 4 * p.1) = (fun x => 4 * x ^ 4 + x ^ 3 - x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2) (x - 5, y - 2)) (5, 2) = 2 * (20 * (y-2) ^ 3 + 15 * (y-2) ^ 2 + 4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + 4 * p.2) = (fun x => 5 * x ^ 4 + 5 * x ^ 3 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 2) (5, 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 3 * p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (6 * (x-6) - 5) - 4 * (9 * (y-4) ^ 2 + 4 * (y-4) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 3 * p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (6 * (x-6) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) (x - 6, y - 4)) (6, 4) = 4 * (9 * (y-4) ^ 2 + 4 * (y-4) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) = (fun x => 3 * x ^ 3 + 2 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 2 + 3 * p.2 - c) (x-4, y-6) (4, 6) = 0) → (4 * (3 * (x-4) ^ 2 + 8 * (x-4) + 3) - 6 * (10 * (y-6) - 3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 4, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 2 + 3 * p.2) (x - 4, y - 6)
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 6) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 4, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1) (x - 4, y - 6)) (4, 6) = 4 * (3 * (x-4) ^ 2 + 8 * (x-4) + 3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.1) = (fun x => x ^ 3 + 4 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 3 * p.2) (x - 4, y - 6)) (4, 6) = 6 * (10 * (y-6) - 3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 3 * p.2) = (fun x => 5 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 4, y - 6) (4, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 - 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) (x-2, y-5) (2, 5) = 0) → (2 * (6 * (x-2) ^ 2 - 5) - 5 * (8 * (y-5) ^ 3 + 3 * (y-5) ^ 2 - 2 * (y-5) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1) (x - 2, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) (x - 2, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 5 * p.1 - 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) (x - 2, y - 5)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1) (x - 2, y - 5) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) (x - 2, y - 5) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1) (x - 2, y - 5)) (2, 5) = 2 * (6 * (x-2) ^ 2 - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 5 * p.1) = (fun x => 2 * x ^ 3 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) (x - 2, y - 5)) (2, 5) = 5 * (8 * (y-5) ^ 3 + 3 * (y-5) ^ 2 - 2 * (y-5) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 4 + x ^ 3 - x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 2, y - 5) (2, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2 - c) (x-3, y-5) (3, 5) = 0) → (3 * (12 * (x-3) ^ 2 + 2) + 5 * (12 * (y-5) ^ 3 + 9 * (y-5) ^ 2 - 8 * (y-5) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1) (x - 3, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1) (x - 3, y - 5) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1) (x - 3, y - 5)) (3, 5) = 3 * (12 * (x-3) ^ 2 + 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 2 * p.1) = (fun x => 4 * x ^ 3 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 5)) (3, 5) = 5 * (12 * (y-5) ^ 3 + 9 * (y-5) ^ 2 - 8 * (y-5) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 5 * p.2) = (fun x => 3 * x ^ 4 + 3 * x ^ 3 - 4 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 5) (3, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.1 - 5 * p.2 ^ 4 - 3 * p.2 ^ 3 + 5 * p.2 ^ 2 - 5 * p.2 - c) (x-5, y-4) (5, 4) = 0) → (5 * (6 * (x-5) + 1) - 4 * (20 * (y-4) ^ 3 + 9 * (y-4) ^ 2 - 10 * (y-4) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 + 3 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + p.1 - 5 * p.2 ^ 4 - 3 * p.2 ^ 3 + 5 * p.2 ^ 2 - 5 * p.2) (x - 5, y - 4)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4) -
      fderiv ℝ (fun p => 5 * p.2 ^ 4 + 3 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) (x - 5, y - 4)) (5, 4) = 5 * (6 * (x-5) + 1)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + p.1) = (fun x => 3 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 + 3 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) (x - 5, y - 4)) (5, 4) = 4 * (20 * (y-4) ^ 3 + 9 * (y-4) ^ 2 - 10 * (y-4) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 + 3 * p.2 ^ 3 - 5 * p.2 ^ 2 + 5 * p.2) = (fun x => 5 * x ^ 4 + 3 * x ^ 3 - 5 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 5, y - 4) (5, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2 - c) (x-6, y-4) (6, 4) = 0) → (6 * (6 * (x-6) ^ 2 - 8 * (x-6) - 2) - 4 * (8 * (y-4) ^ 3 - 6 * (y-4) ^ 2 - 6 * (y-4) + 1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 4))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 4)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1 - 2 * p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) (x - 6, y - 4)
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 4) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 4) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) (x - 6, y - 4)) (6, 4) = 6 * (6 * (x-6) ^ 2 - 8 * (x-6) - 2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 4 * p.1 ^ 2 - 2 * p.1) = (fun x => 2 * x ^ 3 - 4 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2) (x - 6, y - 4)) (6, 4) = 4 * (8 * (y-4) ^ 3 - 6 * (y-4) ^ 2 - 6 * (y-4) + 1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2) = (fun x => 2 * x ^ 4 - 2 * x ^ 3 - 3 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 4) (6, 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.2 ^ 2 + 2 * p.2 - c) (x-6, y-5) (6, 5) = 0) → (6 * (9 * (x-6) ^ 2 - 10 * (x-6)) + 5 * (2 * (y-5) + 2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 6, y - 5))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 5 * p.1 ^ 2 + p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 6, y - 5) +
      fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) (x - 6, y - 5) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) (x - 6, y - 5)) (6, 5) = 6 * (9 * (x-6) ^ 2 - 10 * (x-6))  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) = (fun x => 3 * x ^ 3 - 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) (x - 6, y - 5)) (6, 5) = 5 * (2 * (y-5) + 2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 + 2 * p.2) = (fun x => x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 6, y - 5) (6, 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 5 * p.1 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2 - c) (x-3, y-6) (3, 6) = 0) → (3 * (8 * (x-3) - 5) - 6 * (12 * (y-6) ^ 2 + 6 * (y-6) + 5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 6)): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 5 * p.1 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) (x - 3, y - 6)
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 6) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) (x - 3, y - 6)) (3, 6) = 3 * (8 * (x-3) - 5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - 5 * p.1) = (fun x => 4 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) (x - 3, y - 6)) (3, 6) = 6 * (12 * (y-6) ^ 2 + 6 * (y-6) + 5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 4 * x ^ 3 + 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
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
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    ring
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) (x - 3, y - 6) (3, 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _
