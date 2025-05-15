import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

open Real
open Set

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 - p.2 ^ 3 - p.2 ^ 2 - 3 * p.2 - c) ((-1:ℝ), (6:ℝ)) (x-(-1), y-6) = 0) → ((x-(-1)) * (-4) - (y-6) * (123) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((-1:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 - p.2 ^ 3 - p.2 ^ 2 - 3 * p.2) ((-1:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((-1:ℝ), (6:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((-1:ℝ), (6:ℝ))) (x - (-1), y - 6) = (x-(-1)) * (-4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) = (fun x => x ^ 3 + 2 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (6:ℝ))) (x - (-1), y - 6) = (y-6) * (123)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) = (fun x => x ^ 3 + x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (6:ℝ)) (x - (-1), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 2 - 4 * p.2 - c) ((4:ℝ), (4:ℝ)) (x-4, y-4) = 0) → ((x-4) * (28) - (y-4) * (20) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 4 * p.1) ((4:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) ((4:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 2 - 4 * p.2) ((4:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 4 * p.1) ((4:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) ((4:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 4 * p.1) ((4:ℝ), (4:ℝ))) (x - 4, y - 4) = (x-4) * (28)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 4 * p.1) = (fun x => 3 * x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 4 * p.2) ((4:ℝ), (4:ℝ))) (x - 4, y - 4) = (y-4) * (20)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (4:ℝ)) (x - 4, y - 4) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.2 ^ 2 - c) ((0:ℝ), (-1:ℝ)) (x-0, y-(-1)) = 0) → ((x-0) * (0) - (y-(-1)) * (-8) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 4 * p.2 ^ 2) ((0:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-1:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (-1:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-1:ℝ))) (x - 0, y - (-1)) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (-1:ℝ))) (x - 0, y - (-1)) = (y-(-1)) * (-8)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (-1:ℝ)) (x - 0, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) ((4:ℝ), (1:ℝ)) (x-4, y-1) = 0) → ((x-4) * (48) + (y-1) * (8) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3) ((4:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4) ((4:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 2 * p.2 ^ 4) ((4:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3) ((4:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4) ((4:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3) ((4:ℝ), (1:ℝ))) (x - 4, y - 1) = (x-4) * (48)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4) ((4:ℝ), (1:ℝ))) (x - 4, y - 1) = (y-1) * (8)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4) = (fun x => 2 * x ^ 4) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (1:ℝ)) (x - 4, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst.pow _
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + p.1 + p.2 ^ 2 + 4 * p.2 - c) ((-4:ℝ), (5:ℝ)) (x-(-4), y-5) = 0) → ((x-(-4)) * (-767) + (y-5) * (14) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 + p.1) ((-4:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-4:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 + p.1 + p.2 ^ 2 + 4 * p.2) ((-4:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 + p.1) ((-4:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-4:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 + p.1) ((-4:ℝ), (5:ℝ))) (x - (-4), y - 5) = (x-(-4)) * (-767)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 + p.1) = (fun x => 3 * x ^ 4 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-4:ℝ), (5:ℝ))) (x - (-4), y - 5) = (y-5) * (14)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (5:ℝ)) (x - (-4), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2 - c) ((-2:ℝ), (-6:ℝ)) (x-(-2), y-(-6)) = 0) → ((x-(-2)) * (1) + (y-(-6)) * (-568) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((-2:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 + p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((-2:ℝ), (-6:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (-6:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((-2:ℝ), (-6:ℝ))) (x - (-2), y - (-6)) = (x-(-2)) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (-6:ℝ))) (x - (-2), y - (-6)) = (y-(-6)) * (-568)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) = (fun x => x ^ 4 + 3 * x ^ 3 + 2 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (-6:ℝ)) (x - (-2), y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-30) - (y-3) * (88) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2) ((-5:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) ((-5:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2) ((-5:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) ((-5:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (x-(-5)) * (-30)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2) = (fun x => 3 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (y-3) * (88)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 5 * p.2) = (fun x => 3 * x ^ 3 + 2 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (3:ℝ)) (x - (-5), y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((-1:ℝ), (2:ℝ)) (x-(-1), y-2) = 0) → ((x-(-1)) * (10) + (y-2) * (64) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2) ((-1:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + p.2 ^ 2) ((-1:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2) ((-1:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (2:ℝ))) (x - (-1), y - 2) = (x-(-1)) * (10)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1) = (fun x => 5 * x ^ 3 + 5 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2) ((-1:ℝ), (2:ℝ))) (x - (-1), y - 2) = (y-2) * (64)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + p.2 ^ 2) = (fun x => 5 * x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (2:ℝ)) (x - (-1), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.2 ^ 2 + p.2 - c) ((0:ℝ), (4:ℝ)) (x-0, y-4) = 0) → ((x-0) * (0) - (y-4) * (7) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2) ((0:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) ((0:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - p.2 ^ 2 + p.2) ((0:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2) ((0:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((0:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2) ((0:ℝ), (4:ℝ))) (x - 0, y - 4) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((0:ℝ), (4:ℝ))) (x - 0, y - 4) = (y-4) * (7)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (4:ℝ)) (x - 0, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 - c) ((1:ℝ), (-4:ℝ)) (x-1, y-(-4)) = 0) → ((x-1) * (5) - (y-(-4)) * (-1260) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1) ((1:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2) ((1:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2) ((1:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1) ((1:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2) ((1:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1) ((1:ℝ), (-4:ℝ))) (x - 1, y - (-4)) = (x-1) * (5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1) = (fun x => 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2) ((1:ℝ), (-4:ℝ))) (x - 1, y - (-4)) = (y-(-4)) * (-1260)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 + 4 * p.2) = (fun x => 4 * x ^ 4 - 5 * x ^ 3 + 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-4:ℝ)) (x - 1, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (-16) + (y-(-5)) * (5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((-3:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2) ((-3:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2) ((-3:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((-3:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2) ((-3:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (x-(-3)) * (-16)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (y-(-5)) * (5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2) = (fun x => 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-5:ℝ)) (x - (-3), y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (3:ℝ)) (x-(-4), y-3) = 0) → ((x-(-4)) * (8) + (y-3) * (2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) ((-4:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2) ((-4:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.2) ((-4:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) ((-4:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2) ((-4:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2) ((-4:ℝ), (3:ℝ))) (x - (-4), y - 3) = (x-(-4)) * (8)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2) ((-4:ℝ), (3:ℝ))) (x - (-4), y - 3) = (y-3) * (2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2) = (fun x => 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (3:ℝ)) (x - (-4), y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 + p.2 ^ 3 + p.2 - c) ((1:ℝ), (2:ℝ)) (x-1, y-2) = 0) → ((x-1) * (5) + (y-2) * (13) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1) ((1:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2) ((1:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 + p.2 ^ 3 + p.2) ((1:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1) ((1:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 + p.2) ((1:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1) ((1:ℝ), (2:ℝ))) (x - 1, y - 2) = (x-1) * (5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1) = (fun x => 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2) ((1:ℝ), (2:ℝ))) (x - 1, y - 2) = (y-2) * (13)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (2:ℝ)) (x - 1, y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c) ((-3:ℝ), (2:ℝ)) (x-(-3), y-2) = 0) → ((x-(-3)) * (-23) + (y-2) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((-3:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2) ((-3:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + p.1 + p.2) ((-3:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((-3:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => p.2) ((-3:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((-3:ℝ), (2:ℝ))) (x - (-3), y - 2) = (x-(-3)) * (-23)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2) ((-3:ℝ), (2:ℝ))) (x - (-3), y - 2) = (y-2) * (1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2) = (fun x => x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (2:ℝ)) (x - (-3), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact differentiableAt_snd
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 3 - p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (-2:ℝ)) (x-(-5), y-(-2)) = 0) → ((x-(-5)) * (421) + (y-(-2)) * (20) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-2:ℝ))) (x - (-5), y - (-2)) = (x-(-5)) * (421)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) = (fun x => 5 * x ^ 3 - 5 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-2:ℝ))) (x - (-5), y - (-2)) = (y-(-2)) * (20)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) = (fun x => x ^ 3 - x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-2:ℝ)) (x - (-5), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 + 5 * p.2 - c) ((-5:ℝ), (-4:ℝ)) (x-(-5), y-(-4)) = 0) → ((x-(-5)) * (3) + (y-(-4)) * (-3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((-5:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 + p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((-5:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((-5:ℝ), (-4:ℝ))) (x - (-5), y - (-4)) = (x-(-5)) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (-4:ℝ))) (x - (-5), y - (-4)) = (y-(-4)) * (-3)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-4:ℝ)) (x - (-5), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + p.2 - c) ((4:ℝ), (2:ℝ)) (x-4, y-2) = 0) → ((x-4) * (144) + (y-2) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3) ((4:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2) ((4:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + p.2) ((4:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3) ((4:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => p.2) ((4:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3) ((4:ℝ), (2:ℝ))) (x - 4, y - 2) = (x-4) * (144)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3) = (fun x => 3 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2) ((4:ℝ), (2:ℝ))) (x - 4, y - 2) = (y-2) * (1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2) = (fun x => x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (2:ℝ)) (x - 4, y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact differentiableAt_snd
  
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (99) - (y-(-2)) * (-216) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1) ((-3:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2) ((-3:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((-3:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1) ((-3:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2) ((-3:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (x-(-3)) * (99)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1) = (fun x => 4 * x ^ 3 + 2 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (y-(-2)) * (-216)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2) = (fun x => 5 * x ^ 4 - 5 * x ^ 3 - x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-2:ℝ)) (x - (-3), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (-4:ℝ)) (x-(-2), y-(-4)) = 0) → ((x-(-2)) * (-15) - (y-(-4)) * (7) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((-2:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) ((-2:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2) ((-2:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((-2:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) ((-2:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((-2:ℝ), (-4:ℝ))) (x - (-2), y - (-4)) = (x-(-2)) * (-15)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) ((-2:ℝ), (-4:ℝ))) (x - (-2), y - (-4)) = (y-(-4)) * (7)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 5 * p.2 ^ 2 - p.2) = (fun x => x ^ 3 + 5 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (-4:ℝ)) (x - (-2), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2 - c) ((-5:ℝ), (5:ℝ)) (x-(-5), y-5) = 0) → ((x-(-5)) * (-2417) - (y-5) * (1510) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1) ((-5:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2) ((-5:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2) ((-5:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1) ((-5:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2) ((-5:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1) ((-5:ℝ), (5:ℝ))) (x - (-5), y - 5) = (x-(-5)) * (-2417)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1) = (fun x => 5 * x ^ 4 + x ^ 3 - x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2) ((-5:ℝ), (5:ℝ))) (x - (-5), y - 5) = (y-5) * (1510)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + p.2 ^ 2) = (fun x => 3 * x ^ 4 + x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (5:ℝ)) (x - (-5), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2 - c) ((1:ℝ), (-5:ℝ)) (x-1, y-(-5)) = 0) → ((x-1) * (4) + (y-(-5)) * (-632) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-5:ℝ))) (x - 1, y - (-5)) = (x-1) * (4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - 4 * p.1) = (fun x => 4 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ), (-5:ℝ))) (x - 1, y - (-5)) = (y-(-5)) * (-632)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-5:ℝ)) (x - 1, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + 2 * p.2 ^ 2 - c) ((1:ℝ), (-1:ℝ)) (x-1, y-(-1)) = 0) → ((x-1) * (-11) + (y-(-1)) * (-4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2) ((1:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + 2 * p.2 ^ 2) ((1:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2) ((1:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) ((1:ℝ), (-1:ℝ))) (x - 1, y - (-1)) = (x-1) * (-11)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 3 - 5 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
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
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2) ((1:ℝ), (-1:ℝ))) (x - 1, y - (-1)) = (y-(-1)) * (-4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2) = (fun x => 2 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-1:ℝ)) (x - 1, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 + 3 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 0) → ((x-5) * (20) - (y-(-4)) * (221) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2) ((5:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - 3 * p.2) ((5:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 + 3 * p.2) ((5:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2) ((5:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - 3 * p.2) ((5:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2) ((5:ℝ), (-4:ℝ))) (x - 5, y - (-4)) = (x-5) * (20)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2) = (fun x => 2 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - 3 * p.2) ((5:ℝ), (-4:ℝ))) (x - 5, y - (-4)) = (y-(-4)) * (221)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - 3 * p.2) = (fun x => 4 * x ^ 3 - 4 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (-4:ℝ)) (x - 5, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (-3:ℝ)) (x-(-4), y-(-3)) = 0) → ((x-(-4)) * (240) - (y-(-3)) * (82) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3) ((-4:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) ((-4:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3) ((-4:ℝ), (-3:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3) ((-4:ℝ), (-3:ℝ))) (x - (-4), y - (-3)) = (x-(-4)) * (240)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3) = (fun x => 5 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-3:ℝ))) (x - (-4), y - (-3)) = (y-(-3)) * (82)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) = (fun x => 2 * x ^ 3 - 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (-3:ℝ)) (x - (-4), y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (12) - (y-(-2)) * (28) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((-1:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2) ((-1:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((-1:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (x-(-1)) * (12)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) = (fun x => x ^ 3 - 4 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (y-(-2)) * (28)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) = (fun x => x ^ 3 - 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-2:ℝ)) (x - (-1), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.2 - c) ((-5:ℝ), (-3:ℝ)) (x-(-5), y-(-3)) = 0) → ((x-(-5)) * (-10) - (y-(-3)) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2) ((-5:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2) ((-5:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 3 * p.2) ((-5:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2) ((-5:ℝ), (-3:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2) ((-5:ℝ), (-3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2) ((-5:ℝ), (-3:ℝ))) (x - (-5), y - (-3)) = (x-(-5)) * (-10)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2) ((-5:ℝ), (-3:ℝ))) (x - (-5), y - (-3)) = (y-(-3)) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2) = (fun x => 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-3:ℝ)) (x - (-5), y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst.pow _
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 + 3 * p.2 - c) ((1:ℝ), (1:ℝ)) (x-1, y-1) = 0) → ((x-1) * (15) + (y-1) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2) ((1:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2) ((1:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 3 * p.1 ^ 2 + 3 * p.2) ((1:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2) ((1:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2) ((1:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2) ((1:ℝ), (1:ℝ))) (x - 1, y - 1) = (x-1) * (15)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 3 * p.1 ^ 2) = (fun x => 3 * x ^ 3 + 3 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2) ((1:ℝ), (1:ℝ))) (x - 1, y - 1) = (y-1) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2) = (fun x => 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (1:ℝ)) (x - 1, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1 - p.2 ^ 4 - c) ((-6:ℝ), (-4:ℝ)) (x-(-6), y-(-4)) = 0) → ((x-(-6)) * (-2081) - (y-(-4)) * (-256) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4) ((-6:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1 - p.2 ^ 4) ((-6:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 4) ((-6:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ))) (x - (-6), y - (-4)) = (x-(-6)) * (-2081)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1) = (fun x => 2 * x ^ 4 - 3 * x ^ 3 + 2 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4) ((-6:ℝ), (-4:ℝ))) (x - (-6), y - (-4)) = (y-(-4)) * (-256)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4) = (fun x => x ^ 4) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (-4:ℝ)) (x - (-6), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 + p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (4) + (y-(-2)) * (19) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1) ((6:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) ((6:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 + p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) ((6:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1) ((6:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) ((6:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (x-6) * (4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1) = (fun x => 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (y-(-2)) * (19)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2) = (fun x => x ^ 3 - 3 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-2:ℝ)) (x - 6, y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (5) + (y-6) * (1393) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1) ((-3:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) ((-3:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) ((-3:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1) ((-3:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) ((-3:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (x-(-3)) * (5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1) = (fun x => 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (y-6) * (1393)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2) = (fun x => x ^ 4 + 5 * x ^ 3 - x ^ 2 + x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (6:ℝ)) (x - (-3), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 2 - p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (63) + (y-(-2)) * (-5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1) ((6:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) ((6:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 2 - p.2) ((6:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1) ((6:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((6:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (x-6) * (63)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1) = (fun x => x ^ 3 - 4 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (y-(-2)) * (-5)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-2:ℝ)) (x - 6, y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1 + 2 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (190) + (y-(-3)) * (72) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1) ((2:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - 3 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1 + 2 * p.2 ^ 3 - 3 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1) ((2:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - 3 * p.2 ^ 2) ((2:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (x-2) * (190)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1) = (fun x => 5 * x ^ 4 + x ^ 3 + 4 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - 3 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (y-(-3)) * (72)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - 3 * p.2 ^ 2) = (fun x => 2 * x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-3:ℝ)) (x - 2, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3 - c) ((-4:ℝ), (0:ℝ)) (x-(-4), y-0) = 0) → ((x-(-4)) * (-914) - (y-0) * (0) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3) ((-4:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3) ((-4:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3) ((-4:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4:ℝ), (0:ℝ))) (x - (-4), y - 0) = (x-(-4)) * (-914)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) = (fun x => 3 * x ^ 4 - 3 * x ^ 3 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3) ((-4:ℝ), (0:ℝ))) (x - (-4), y - 0) = (y-0) * (0)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3) = (fun x => 3 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (0:ℝ)) (x - (-4), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + p.2 ^ 2 - 4 * p.2 - c) ((-6:ℝ), (0:ℝ)) (x-(-6), y-0) = 0) → ((x-(-6)) * (236) - (y-0) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + p.2 ^ 2 - 4 * p.2) ((-6:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6:ℝ), (0:ℝ))) (x - (-6), y - 0) = (x-(-6)) * (236)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) = (fun x => 2 * x ^ 3 - 2 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6:ℝ), (0:ℝ))) (x - (-6), y - 0) = (y-0) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) = (fun x => 2 * x ^ 4 + 5 * x ^ 3 - x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (0:ℝ)) (x - (-6), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 + 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2 - c) ((-1:ℝ), (-1:ℝ)) (x-(-1), y-(-1)) = 0) → ((x-(-1)) * (-3) + (y-(-1)) * (-33) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - p.1) ((-1:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2) ((-1:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - p.1 + 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2) ((-1:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-1:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2) ((-1:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-1:ℝ), (-1:ℝ))) (x - (-1), y - (-1)) = (x-(-1)) * (-3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - p.1) = (fun x => x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2) ((-1:ℝ), (-1:ℝ))) (x - (-1), y - (-1)) = (y-(-1)) * (-33)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2) = (fun x => 4 * x ^ 4 - 5 * x ^ 3 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-1:ℝ)) (x - (-1), y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 3 - 4 * p.2 - c) ((-3:ℝ), (3:ℝ)) (x-(-3), y-3) = 0) → ((x-(-3)) * (-35) + (y-3) * (104) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ))) (x - (-3), y - 3) = (x-(-3)) * (-35)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ))) (x - (-3), y - 3) = (y-3) * (104)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 4 * p.2) = (fun x => 4 * x ^ 3 - 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (3:ℝ)) (x - (-3), y - 3) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (16) - (y-(-3)) * (-12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (-3:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2) ((2:ℝ), (-3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (x-2) * (16)  := by
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (y-(-3)) * (-12)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 2) = (fun x => 2 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-3:ℝ)) (x - 2, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1 - 3 * p.2 ^ 3 - 4 * p.2 - c) ((-1:ℝ), (3:ℝ)) (x-(-1), y-3) = 0) → ((x-(-1)) * (10) - (y-3) * (85) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1) ((-1:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2) ((-1:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1 - 3 * p.2 ^ 3 - 4 * p.2) ((-1:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1) ((-1:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2) ((-1:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1) ((-1:ℝ), (3:ℝ))) (x - (-1), y - 3) = (x-(-1)) * (10)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1) = (fun x => x ^ 4 + 2 * x ^ 3 - 3 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2) ((-1:ℝ), (3:ℝ))) (x - (-1), y - 3) = (y-3) * (85)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 4 * p.2) = (fun x => 3 * x ^ 3 + 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (3:ℝ)) (x - (-1), y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2 - c) ((-6:ℝ), (-4:ℝ)) (x-(-6), y-(-4)) = 0) → ((x-(-6)) * (463) + (y-(-4)) * (-8) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2) ((-6:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2) ((-6:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2) ((-6:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6:ℝ), (-4:ℝ))) (x - (-6), y - (-4)) = (x-(-6)) * (463)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 4 * x ^ 3 - 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2) ((-6:ℝ), (-4:ℝ))) (x - (-6), y - (-4)) = (y-(-4)) * (-8)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (-4:ℝ)) (x - (-6), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + p.1 ^ 2 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2 - c) ((5:ℝ), (3:ℝ)) (x-5, y-3) = 0) → ((x-5) * (385) - (y-3) * (101) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2) ((5:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2 - 4 * p.2) ((5:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + p.1 ^ 2 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2) ((5:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2) ((5:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2 - 4 * p.2) ((5:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + p.1 ^ 2) ((5:ℝ), (3:ℝ))) (x - 5, y - 3) = (x-5) * (385)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + p.1 ^ 2) = (fun x => 5 * x ^ 3 + x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 4 * p.2 ^ 2 - 4 * p.2) ((5:ℝ), (3:ℝ))) (x - 5, y - 3) = (y-3) * (101)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 4 * p.2 ^ 2 - 4 * p.2) = (fun x => 3 * x ^ 3 + 4 * x ^ 2 - 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (3:ℝ)) (x - 5, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 5 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c) ((1:ℝ), (2:ℝ)) (x-1, y-2) = 0) → ((x-1) * (3) - (y-2) * (25) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1) ((1:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((1:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 5 * p.1 - 5 * p.2 ^ 2 - 5 * p.2) ((1:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1) ((1:ℝ), (2:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((1:ℝ), (2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1) ((1:ℝ), (2:ℝ))) (x - 1, y - 2) = (x-1) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 5 * p.1) = (fun x => 2 * x ^ 4 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((1:ℝ), (2:ℝ))) (x - 1, y - 2) = (y-2) * (25)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 5 * p.2) = (fun x => 5 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (2:ℝ)) (x - 1, y - 2) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2 - c) ((-6:ℝ), (2:ℝ)) (x-(-6), y-2) = 0) → ((x-(-6)) * (-27) + (y-2) * (15) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) ((-6:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 - p.2) ((-6:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2) ((-6:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) ((-6:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 - p.2) ((-6:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 3 * p.1) ((-6:ℝ), (2:ℝ))) (x - (-6), y - 2) = (x-(-6)) * (-27)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2 ^ 2 - p.2) ((-6:ℝ), (2:ℝ))) (x - (-6), y - 2) = (y-2) * (15)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + p.2 ^ 2 - p.2) = (fun x => x ^ 3 + x ^ 2 - x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (2:ℝ)) (x - (-6), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + 5 * p.2 ^ 2 - p.2 - c) ((1:ℝ), (-2:ℝ)) (x-1, y-(-2)) = 0) → ((x-1) * (3) + (y-(-2)) * (-21) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((1:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((1:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 + 5 * p.2 ^ 2 - p.2) ((1:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((1:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((1:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((1:ℝ), (-2:ℝ))) (x - 1, y - (-2)) = (x-1) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((1:ℝ), (-2:ℝ))) (x - 1, y - (-2)) = (y-(-2)) * (-21)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-2:ℝ)) (x - 1, y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 2 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (3) - (y-5) * (19) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((0:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((0:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 - 2 * p.2 ^ 2 + p.2) ((0:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((0:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((0:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (x-0) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (y-5) * (19)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (5:ℝ)) (x - 0, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + p.1 ^ 2 + p.1 + p.2 - c) ((2:ℝ), (5:ℝ)) (x-2, y-5) = 0) → ((x-2) * (53) + (y-5) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 + p.1) ((2:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2) ((2:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + p.1 ^ 2 + p.1 + p.2) ((2:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 + p.1) ((2:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => p.2) ((2:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 + p.1 ^ 2 + p.1) ((2:ℝ), (5:ℝ))) (x - 2, y - 5) = (x-2) * (53)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 + p.1 ^ 2 + p.1) = (fun x => 4 * x ^ 3 + x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2) ((2:ℝ), (5:ℝ))) (x - 2, y - 5) = (y-5) * (1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2) = (fun x => x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (5:ℝ)) (x - 2, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact differentiableAt_snd
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + p.1 ^ 2 + p.1 - p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (2:ℝ)) (x-(-2), y-2) = 0) → ((x-(-2)) * (-99) - (y-2) * (67) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 + p.1 ^ 2 + p.1) ((-2:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) ((-2:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 4 + p.1 ^ 2 + p.1 - p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2) ((-2:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 4 + p.1 ^ 2 + p.1) ((-2:ℝ), (2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) ((-2:ℝ), (2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 4 + p.1 ^ 2 + p.1) ((-2:ℝ), (2:ℝ))) (x - (-2), y - 2) = (x-(-2)) * (-99)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 4 + p.1 ^ 2 + p.1) = (fun x => 3 * x ^ 4 + x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) ((-2:ℝ), (2:ℝ))) (x - (-2), y - 2) = (y-2) * (67)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2 - p.2) = (fun x => x ^ 4 + 2 * x ^ 3 + 3 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (2:ℝ)) (x - (-2), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (3) + (y-1) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((2:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 2) ((2:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 2) ((2:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((2:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 2) ((2:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (x-2) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 2) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (y-1) * (12)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 2 * p.2 ^ 2) = (fun x => 2 * x ^ 4 + 2 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (1:ℝ)) (x - 2, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 4 * p.1 ^ 3 + 5 * p.2 ^ 3 - 3 * p.2 - c) ((-3:ℝ), (-4:ℝ)) (x-(-3), y-(-4)) = 0) → ((x-(-3)) * (0) + (y-(-4)) * (237) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 4 * p.1 ^ 3) ((-3:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2) ((-3:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 4 * p.1 ^ 3 + 5 * p.2 ^ 3 - 3 * p.2) ((-3:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 4 * p.1 ^ 3) ((-3:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2) ((-3:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 4 * p.1 ^ 3) ((-3:ℝ), (-4:ℝ))) (x - (-3), y - (-4)) = (x-(-3)) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 4 * p.1 ^ 3) = (fun x => x ^ 4 + 4 * x ^ 3) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 3 * p.2) ((-3:ℝ), (-4:ℝ))) (x - (-3), y - (-4)) = (y-(-4)) * (237)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 3 * p.2) = (fun x => 5 * x ^ 3 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-4:ℝ)) (x - (-3), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + p.2 ^ 2 - 4 * p.2 - c) ((-2:ℝ), (0:ℝ)) (x-(-2), y-0) = 0) → ((x-(-2)) * (2) + (y-0) * (-4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((-2:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 + p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((-2:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((-2:ℝ), (0:ℝ))) (x - (-2), y - 0) = (x-(-2)) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((-2:ℝ), (0:ℝ))) (x - (-2), y - 0) = (y-0) * (-4)  := by
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (0:ℝ)) (x - (-2), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 5 * p.2 ^ 2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-2800) + (y-3) * (30) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((-5:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((-5:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (x-(-5)) * (-2800)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) = (fun x => 5 * x ^ 4 - 4 * x ^ 3) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (y-3) * (30)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (3:ℝ)) (x - (-5), y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 4 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (3408) + (y-3) * (168) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) ((6:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - 4 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) ((6:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (x-6) * (3408)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) = (fun x => 4 * x ^ 4 - 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (y-3) * (168)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) = (fun x => x ^ 4 + 3 * x ^ 3 - 3 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (3:ℝ)) (x - 6, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.2 ^ 2 + 2 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (-30) - (y-(-5)) * (-42) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2) ((-3:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 - 2 * p.2) ((-3:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 4 * p.2 ^ 2 + 2 * p.2) ((-3:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2) ((-3:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2 - 2 * p.2) ((-3:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (x-(-3)) * (-30)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 - 2 * p.2) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (y-(-5)) * (-42)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2 - 2 * p.2) = (fun x => 4 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-5:ℝ)) (x - (-3), y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (1:ℝ)) (x-(-5), y-1) = 0) → ((x-(-5)) * (-2390) + (y-1) * (10) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (1:ℝ))) (x - (-5), y - 1) = (x-(-5)) * (-2390)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => 5 * x ^ 4 + 2 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (1:ℝ))) (x - (-5), y - 1) = (y-1) * (10)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (1:ℝ)) (x - (-5), y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 - 3 * p.2 - c) ((-4:ℝ), (-3:ℝ)) (x-(-4), y-(-3)) = 0) → ((x-(-4)) * (-15) - (y-(-3)) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) ((-4:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2) ((-4:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + p.1 - 3 * p.2) ((-4:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) ((-4:ℝ), (-3:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2) ((-4:ℝ), (-3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + p.1) ((-4:ℝ), (-3:ℝ))) (x - (-4), y - (-3)) = (x-(-4)) * (-15)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2) ((-4:ℝ), (-3:ℝ))) (x - (-4), y - (-3)) = (y-(-3)) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2) = (fun x => 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (-3:ℝ)) (x - (-4), y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.1 - p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (1) - (y-3) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((2:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2) ((2:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 3 * p.1 - p.2) ((2:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((2:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => p.2) ((2:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (x-2) * (1)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (y-3) * (1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2) = (fun x => x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (3:ℝ)) (x - 2, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2 - c) ((0:ℝ), (-3:ℝ)) (x-0, y-(-3)) = 0) → ((x-0) * (0) - (y-(-3)) * (-32) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 2 * p.2) ((0:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2) ((0:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (-3:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 2 * p.2) ((0:ℝ), (-3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (-3:ℝ))) (x - 0, y - (-3)) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 2 * p.2) ((0:ℝ), (-3:ℝ))) (x - 0, y - (-3)) = (y-(-3)) * (-32)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 - 2 * p.2) = (fun x => 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (-3:ℝ)) (x - 0, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 4 + p.2 - c) ((2:ℝ), (0:ℝ)) (x-2, y-0) = 0) → ((x-2) * (15) + (y-0) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + p.2) ((2:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 4 + p.2) ((2:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + p.2) ((2:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (0:ℝ))) (x - 2, y - 0) = (x-2) * (15)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + p.2) ((2:ℝ), (0:ℝ))) (x - 2, y - 0) = (y-0) * (1)  := by
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
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (0:ℝ)) (x - 2, y - 0) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-665) + (y-3) * (84) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (x-(-5)) * (-665)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => 2 * x ^ 4 + 5 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 5 * p.2 ^ 2) ((-5:ℝ), (3:ℝ))) (x - (-5), y - 3) = (y-3) * (84)  := by
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (3:ℝ)) (x - (-5), y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - p.1 + 4 * p.2 ^ 2 - c) ((0:ℝ), (0:ℝ)) (x-0, y-0) = 0) → ((x-0) * (-1) + (y-0) * (0) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 - p.1) ((0:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 - p.1 + 4 * p.2 ^ 2) ((0:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 - p.1) ((0:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 - p.1) ((0:ℝ), (0:ℝ))) (x - 0, y - 0) = (x-0) * (-1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 - p.1) = (fun x => x ^ 4 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((0:ℝ), (0:ℝ))) (x - 0, y - 0) = (y-0) * (0)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (0:ℝ)) (x - 0, y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 - 4 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (133) - (y-0) * (-1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((3:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2 - p.2) ((3:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 - 4 * p.2 ^ 3 - p.2 ^ 2 + p.2) ((3:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((3:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2 - p.2) ((3:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (x-3) * (133)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) = (fun x => 5 * x ^ 3 - x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2 ^ 2 - p.2) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (y-0) * (-1)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + p.2 ^ 2 - p.2) = (fun x => 4 * x ^ 3 + x ^ 2 - x) ∘ (fun p => p.2) := rfl
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (0:ℝ)) (x - 3, y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - p.2 ^ 3 - c) ((-2:ℝ), (-2:ℝ)) (x-(-2), y-(-2)) = 0) → ((x-(-2)) * (48) - (y-(-2)) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - p.2 ^ 3) ((-2:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ))) (x - (-2), y - (-2)) = (x-(-2)) * (48)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3) = (fun x => 4 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ))) (x - (-2), y - (-2)) = (y-(-2)) * (12)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (-2:ℝ)) (x - (-2), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3 - c) ((4:ℝ), (3:ℝ)) (x-4, y-3) = 0) → ((x-4) * (133) - (y-3) * (54) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ))) (x - 4, y - 3) = (x-4) * (133)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) = (fun x => x ^ 4 - 2 * x ^ 3 - 4 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
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
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ))) (x - 4, y - 3) = (y-3) * (54)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (3:ℝ)) (x - 4, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3 - c) ((-4:ℝ), (1:ℝ)) (x-(-4), y-1) = 0) → ((x-(-4)) * (-1221) - (y-1) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1) ((-4:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3) ((-4:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1) ((-4:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1) ((-4:ℝ), (1:ℝ))) (x - (-4), y - 1) = (x-(-4)) * (-1221)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1) = (fun x => 4 * x ^ 4 - 5 * x ^ 3 - 5 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (1:ℝ))) (x - (-4), y - 1) = (y-1) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (1:ℝ)) (x - (-4), y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 2 + p.2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (1) - (y-(-2)) * (-5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((-3:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - p.2) ((-3:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 - p.2 ^ 2 + p.2) ((-3:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((-3:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((-3:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (x-(-3)) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - p.2) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (y-(-2)) * (-5)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-2:ℝ)) (x - (-3), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 - 2 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (355) - (y-(-5)) * (-1090) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((6:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) ((6:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 - 2 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2) ((6:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((6:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) ((6:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (x-6) * (355)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 3 + 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (y-(-5)) * (-1090)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - p.2 ^ 3 + 2 * p.2 ^ 2 + 5 * p.2) = (fun x => 2 * x ^ 4 - x ^ 3 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-5:ℝ)) (x - 6, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 - c) ((5:ℝ), (-1:ℝ)) (x-5, y-(-1)) = 0) → ((x-5) * (27) + (y-(-1)) * (-2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) ((5:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2) ((5:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2) ((5:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) ((5:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2) ((5:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 3 * p.1) ((5:ℝ), (-1:ℝ))) (x - 5, y - (-1)) = (x-5) * (27)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2) ((5:ℝ), (-1:ℝ))) (x - 5, y - (-1)) = (y-(-1)) * (-2)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (-1:ℝ)) (x - 5, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 3 - c) ((-6:ℝ), (6:ℝ)) (x-(-6), y-6) = 0) → ((x-(-6)) * (448) + (y-6) * (324) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((-6:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3) ((-6:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 3) ((-6:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((-6:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3) ((-6:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) ((-6:ℝ), (6:ℝ))) (x - (-6), y - 6) = (x-(-6)) * (448)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1) = (fun x => 4 * x ^ 3 - x ^ 2 + 4 * x) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3) ((-6:ℝ), (6:ℝ))) (x - (-6), y - 6) = (y-6) * (324)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3) = (fun x => 3 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (6:ℝ)) (x - (-6), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) ((-4:ℝ), (6:ℝ)) (x-(-4), y-6) = 0) → ((x-(-4)) * (4) + (y-6) * (89) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1) ((-4:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) ((-4:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) ((-4:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1) ((-4:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) ((-4:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1) ((-4:ℝ), (6:ℝ))) (x - (-4), y - 6) = (x-(-4)) * (4)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1) = (fun x => 4 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) ((-4:ℝ), (6:ℝ))) (x - (-4), y - 6) = (y-6) * (89)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 3 - 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (6:ℝ)) (x - (-4), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (5) + (y-(-2)) * (-85) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-1:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) ((-1:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) ((-1:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-1:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) ((-1:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (x-(-1)) * (5)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - p.1 ^ 2) = (fun x => x ^ 3 - x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (y-(-2)) * (-85)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) = (fun x => 2 * x ^ 4 - x ^ 3 + x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-2:ℝ)) (x - (-1), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3 - c) ((-4:ℝ), (-1:ℝ)) (x-(-4), y-(-1)) = 0) → ((x-(-4)) * (-1101) + (y-(-1)) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-4:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3) ((-4:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-4:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-4:ℝ), (-1:ℝ))) (x - (-4), y - (-1)) = (x-(-4)) * (-1101)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) = (fun x => 5 * x ^ 4 + 3 * x ^ 3 - 5 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3) ((-4:ℝ), (-1:ℝ))) (x - (-4), y - (-1)) = (y-(-1)) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (-1:ℝ)) (x - (-4), y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact differentiableAt_snd.pow _
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (4:ℝ)) (x-(-1), y-4) = 0) → ((x-(-1)) * (-8) - (y-4) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2) ((-1:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2) ((-1:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 4 * p.2) ((-1:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2) ((-1:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2) ((-1:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2) ((-1:ℝ), (4:ℝ))) (x - (-1), y - 4) = (x-(-1)) * (-8)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2) ((-1:ℝ), (4:ℝ))) (x - (-1), y - 4) = (y-4) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2) = (fun x => 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (4:ℝ)) (x - (-1), y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (240) + (y-3) * (229) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((6:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((6:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((6:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((6:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((6:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (x-6) * (240)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 2 * p.1 ^ 2) = (fun x => 2 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (y-3) * (229)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2) = (fun x => 2 * x ^ 4 + x ^ 3 - 3 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (3:ℝ)) (x - 6, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - p.1 ^ 2 - p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((4:ℝ), (0:ℝ)) (x-4, y-0) = 0) → ((x-4) * (88) - (y-0) * (-1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - p.1 ^ 2) ((4:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((4:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - p.1 ^ 2 - p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((4:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - p.1 ^ 2) ((4:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((4:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - p.1 ^ 2) ((4:ℝ), (0:ℝ))) (x - 4, y - 0) = (x-4) * (88)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - p.1 ^ 2) = (fun x => 2 * x ^ 3 - x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((4:ℝ), (0:ℝ))) (x - 4, y - 0) = (y-0) * (-1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 - p.2) = (fun x => x ^ 4 + 2 * x ^ 3 - x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (0:ℝ)) (x - 4, y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.2 - c) ((-1:ℝ), (2:ℝ)) (x-(-1), y-2) = 0) → ((x-(-1)) * (-18) + (y-2) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((-1:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2) ((-1:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.2) ((-1:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((-1:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2) ((-1:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) ((-1:ℝ), (2:ℝ))) (x - (-1), y - 2) = (x-(-1)) * (-18)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2) = (fun x => 2 * x ^ 4 - 2 * x ^ 3 + 2 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 4 * p.2) ((-1:ℝ), (2:ℝ))) (x - (-1), y - 2) = (y-2) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2) = (fun x => 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (2:ℝ)) (x - (-1), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 5 * p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ((4:ℝ), (2:ℝ)) (x-4, y-2) = 0) → ((x-4) * (55) - (y-2) * (185) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) ((4:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) ((4:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 5 * p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 - 5 * p.2) ((4:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) ((4:ℝ), (2:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) ((4:ℝ), (2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) ((4:ℝ), (2:ℝ))) (x - 4, y - 2) = (x-4) * (55)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1) = (fun x => 2 * x ^ 3 - 5 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) ((4:ℝ), (2:ℝ))) (x - 4, y - 2) = (y-2) * (185)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 + 2 * p.2 ^ 3 - p.2 ^ 2 + 5 * p.2) = (fun x => 5 * x ^ 4 + 2 * x ^ 3 - x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (2:ℝ)) (x - 4, y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 2 * p.1 + 3 * p.2 ^ 4 - c) ((-6:ℝ), (1:ℝ)) (x-(-6), y-1) = 0) → ((x-(-6)) * (-1730) + (y-1) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1) ((-6:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4) ((-6:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 2 * p.1 + 3 * p.2 ^ 4) ((-6:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1) ((-6:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4) ((-6:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 2 * p.1) ((-6:ℝ), (1:ℝ))) (x - (-6), y - 1) = (x-(-6)) * (-1730)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 2 * p.1) = (fun x => 2 * x ^ 4 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4) ((-6:ℝ), (1:ℝ))) (x - (-6), y - 1) = (y-1) * (12)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4) = (fun x => 3 * x ^ 4) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (1:ℝ)) (x - (-6), y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 ^ 2 + 4 * p.2 ^ 2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (-126) + (y-6) * (48) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 2) ((-3:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((-3:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 3 * p.1 ^ 2 + 4 * p.2 ^ 2) ((-3:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 2) ((-3:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((-3:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 2) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (x-(-3)) * (-126)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 2) = (fun x => x ^ 4 + 3 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (y-6) * (48)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (6:ℝ)) (x - (-3), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2 - c) ((3:ℝ), (-4:ℝ)) (x-3, y-(-4)) = 0) → ((x-3) * (20) + (y-(-4)) * (-37) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((3:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2) ((3:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2) ((3:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((3:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2) ((3:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((3:ℝ), (-4:ℝ))) (x - 3, y - (-4)) = (x-3) * (20)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - 4 * p.1) = (fun x => 4 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2) ((3:ℝ), (-4:ℝ))) (x - 3, y - (-4)) = (y-(-4)) * (-37)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2) = (fun x => x ^ 4 + 4 * x ^ 3 - 3 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (-4:ℝ)) (x - 3, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((-2:ℝ), (-3:ℝ)) (x-(-2), y-(-3)) = 0) → ((x-(-2)) * (2) + (y-(-3)) * (-171) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((-2:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2) ((-2:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2) ((-2:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((-2:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2) ((-2:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((-2:ℝ), (-3:ℝ))) (x - (-2), y - (-3)) = (x-(-2)) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2) ((-2:ℝ), (-3:ℝ))) (x - (-2), y - (-3)) = (y-(-3)) * (-171)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2) = (fun x => x ^ 4 - 3 * x ^ 3 - 3 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (-3:ℝ)) (x - (-2), y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2 - c) ((-5:ℝ), (5:ℝ)) (x-(-5), y-5) = 0) → ((x-(-5)) * (-8) + (y-5) * (1705) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2) ((-5:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2) ((-5:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2) ((-5:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (5:ℝ))) (x - (-5), y - 5) = (x-(-5)) * (-8)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2) ((-5:ℝ), (5:ℝ))) (x - (-5), y - 5) = (y-5) * (1705)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2) = (fun x => 3 * x ^ 4 + 3 * x ^ 3 - 2 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (5:ℝ)) (x - (-5), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1 - 5 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (18) - (y-3) * (103) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1) ((2:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((2:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1 - 5 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) ((2:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1) ((2:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((2:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (x-2) * (18)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1) = (fun x => x ^ 3 + 2 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (y-3) * (103)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 5 * p.2 ^ 2 - 2 * p.2) = (fun x => 5 * x ^ 3 - 5 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (3:ℝ)) (x - 2, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 2 * p.1 + 5 * p.2 ^ 2 - p.2 - c) ((4:ℝ), (-3:ℝ)) (x-4, y-(-3)) = 0) → ((x-4) * (22) + (y-(-3)) * (-31) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((4:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 2 * p.1 + 5 * p.2 ^ 2 - p.2) ((4:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((4:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-3:ℝ))) (x - 4, y - (-3)) = (x-4) * (22)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - p.2) ((4:ℝ), (-3:ℝ))) (x - 4, y - (-3)) = (y-(-3)) * (-31)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-3:ℝ)) (x - 4, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 2 * p.2 ^ 2 + p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (2) - (y-(-1)) * (-5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((4:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 - 2 * p.2 ^ 2 + p.2) ((4:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((4:ℝ), (-1:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ), (-1:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (x-4) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (y-(-1)) * (-5)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-1:ℝ)) (x - 4, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 - c) ((4:ℝ), (-4:ℝ)) (x-4, y-(-4)) = 0) → ((x-4) * (253) + (y-(-4)) * (-24) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((4:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2) ((4:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2) ((4:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((4:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2) ((4:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) ((4:ℝ), (-4:ℝ))) (x - 4, y - (-4)) = (x-4) * (253)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1) = (fun x => 5 * x ^ 3 + 2 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2) ((4:ℝ), (-4:ℝ))) (x - 4, y - (-4)) = (y-(-4)) * (-24)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2) = (fun x => 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-4:ℝ)) (x - 4, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 ^ 2 - 4 * p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (0) - (y-5) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + p.1 ^ 2) ((0:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2) ((0:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + p.1 ^ 2 - 4 * p.2) ((0:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + p.1 ^ 2) ((0:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2) ((0:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + p.1 ^ 2) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + p.1 ^ 2) = (fun x => x ^ 3 + x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (y-5) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2) = (fun x => 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (5:ℝ)) (x - 0, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) ((0:ℝ), (4:ℝ)) (x-0, y-4) = 0) → ((x-0) * (-5) + (y-4) * (1069) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((0:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((0:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (4:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((0:ℝ), (4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (4:ℝ))) (x - 0, y - 4) = (x-0) * (-5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1) = (fun x => 2 * x ^ 3 + 3 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((0:ℝ), (4:ℝ))) (x - 0, y - 4) = (y-4) * (1069)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 5 * x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (4:ℝ)) (x - 0, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c) ((-5:ℝ), (6:ℝ)) (x-(-5), y-6) = 0) → ((x-(-5)) * (-329) - (y-6) * (65) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2) ((-5:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (6:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (6:ℝ))) (x - (-5), y - 6) = (x-(-5)) * (-329)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 4 + 3 * x ^ 3 + 5 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 5 * p.2) ((-5:ℝ), (6:ℝ))) (x - (-5), y - 6) = (y-6) * (65)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2 + 5 * p.2) = (fun x => 5 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (6:ℝ)) (x - (-5), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (38) + (y-(-1)) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2) ((4:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2) ((4:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2) ((4:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (x-4) * (38)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (y-(-1)) * (12)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2) = (fun x => 2 * x ^ 3 - 4 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-1:ℝ)) (x - 4, y - (-1)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 2 + 3 * p.2 - c) ((-1:ℝ), (0:ℝ)) (x-(-1), y-0) = 0) → ((x-(-1)) * (12) + (y-0) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) ((-1:ℝ), (0:ℝ))) (x - (-1), y - 0) = (x-(-1)) * (12)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1) = (fun x => x ^ 3 - 2 * x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + 3 * p.2) ((-1:ℝ), (0:ℝ))) (x - (-1), y - 0) = (y-0) * (3)  := by
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (0:ℝ)) (x - (-1), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - p.2 - c) ((1:ℝ), (-6:ℝ)) (x-1, y-(-6)) = 0) → ((x-1) * (2) - (y-(-6)) * (1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((1:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2) ((1:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 - p.2) ((1:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((1:ℝ), (-6:ℝ)) -
      fderiv ℝ (fun p => p.2) ((1:ℝ), (-6:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((1:ℝ), (-6:ℝ))) (x - 1, y - (-6)) = (x-1) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2) ((1:ℝ), (-6:ℝ))) (x - 1, y - (-6)) = (y-(-6)) * (1)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2) = (fun x => x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-6:ℝ)) (x - 1, y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact differentiableAt_snd
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1 - 2 * p.2 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (-2:ℝ)) (x-(-4), y-(-2)) = 0) → ((x-(-4)) * (-535) - (y-(-2)) * (-10) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1) ((-4:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1 - 2 * p.2 ^ 2 + 2 * p.2) ((-4:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1) ((-4:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1) ((-4:ℝ), (-2:ℝ))) (x - (-4), y - (-2)) = (x-(-4)) * (-535)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1) = (fun x => 2 * x ^ 4 + 3 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - 2 * p.2) ((-4:ℝ), (-2:ℝ))) (x - (-4), y - (-2)) = (y-(-2)) * (-10)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (-2:ℝ)) (x - (-4), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1 + p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (254) + (y-3) * (75) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1) ((3:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2) ((3:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1 + p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2) ((3:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1) ((3:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2) ((3:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (x-3) * (254)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1) = (fun x => x ^ 4 + 5 * x ^ 3 + x ^ 2 + 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (y-3) * (75)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2) = (fun x => x ^ 4 - x ^ 3 - x ^ 2) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (3:ℝ)) (x - 3, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_snd.pow _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (-3:ℝ)) (x-(-5), y-(-3)) = 0) → ((x-(-5)) * (-54) + (y-(-3)) * (-2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 4 * p.1) ((-5:ℝ), (-3:ℝ))) (x - (-5), y - (-3)) = (x-(-5)) * (-54)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-3:ℝ))) (x - (-5), y - (-3)) = (y-(-3)) * (-2)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-3:ℝ)) (x - (-5), y - (-3)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 2 + 2 * p.2 - c) ((-5:ℝ), (4:ℝ)) (x-(-5), y-4) = 0) → ((x-(-5)) * (-29) + (y-4) * (18) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + p.1) ((-5:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) ((-5:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 2 + 2 * p.2) ((-5:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) ((-5:ℝ), (4:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) ((-5:ℝ), (4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + p.1) ((-5:ℝ), (4:ℝ))) (x - (-5), y - 4) = (x-(-5)) * (-29)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 + 2 * p.2) ((-5:ℝ), (4:ℝ))) (x - (-5), y - 4) = (y-4) * (18)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (4:ℝ)) (x - (-5), y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1 - p.2 ^ 2 - 2 * p.2 - c) ((-1:ℝ), (5:ℝ)) (x-(-1), y-5) = 0) → ((x-(-1)) * (-22) - (y-5) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1) ((-1:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-1:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1 - p.2 ^ 2 - 2 * p.2) ((-1:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1) ((-1:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-1:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1) ((-1:ℝ), (5:ℝ))) (x - (-1), y - 5) = (x-(-1)) * (-22)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1) = (fun x => 5 * x ^ 4 + x ^ 3 + 2 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-1:ℝ), (5:ℝ))) (x - (-1), y - 5) = (y-5) * (12)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (5:ℝ)) (x - (-1), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((5:ℝ), (5:ℝ)) (x-5, y-5) = 0) → ((x-5) * (150) - (y-5) * (405) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3) ((5:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2) ((5:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 5 * p.2 ^ 3 - 3 * p.2 ^ 2) ((5:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3) ((5:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2) ((5:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3) ((5:ℝ), (5:ℝ))) (x - 5, y - 5) = (x-5) * (150)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 3 * p.2 ^ 2) ((5:ℝ), (5:ℝ))) (x - 5, y - 5) = (y-5) * (405)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + 3 * p.2 ^ 2) = (fun x => 5 * x ^ 3 + 3 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (5:ℝ)) (x - 5, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 - 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (-12) + (y-(-2)) * (43) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1) ((-1:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2) ((-1:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 - 5 * p.2) ((-1:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1) ((-1:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2) ((-1:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (x-(-1)) * (-12)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1) = (fun x => x ^ 4 + 2 * x ^ 2 - 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 5 * p.2) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (y-(-2)) * (43)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 5 * p.2) = (fun x => 4 * x ^ 3 - 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-2:ℝ)) (x - (-1), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 + p.2 ^ 2 + 5 * p.2 - c) ((2:ℝ), (-1:ℝ)) (x-2, y-(-1)) = 0) → ((x-2) * (25) + (y-(-1)) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((2:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((2:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 5 * p.1 + p.2 ^ 2 + 5 * p.2) ((2:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((2:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((2:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((2:ℝ), (-1:ℝ))) (x - 2, y - (-1)) = (x-2) * (25)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 5 * p.2) ((2:ℝ), (-1:ℝ))) (x - 2, y - (-1)) = (y-(-1)) * (3)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-1:ℝ)) (x - 2, y - (-1)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 3 * p.2 - c) ((4:ℝ), (5:ℝ)) (x-4, y-5) = 0) → ((x-4) * (86) + (y-5) * (7) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 3 * p.2) ((4:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 3 * p.2) ((4:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 - 3 * p.2) ((4:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1) ((4:ℝ), (5:ℝ))) (x - 4, y - 5) = (x-4) * (86)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1) = (fun x => x ^ 3 + 5 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 3 * p.2) ((4:ℝ), (5:ℝ))) (x - 4, y - 5) = (y-5) * (7)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - 3 * p.2) = (fun x => x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (5:ℝ)) (x - 4, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2 - c) ((-6:ℝ), (2:ℝ)) (x-(-6), y-2) = 0) → ((x-(-6)) * (1) + (y-2) * (17) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((-6:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) ((-6:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 + p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) ((-6:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((-6:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) ((-6:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((-6:ℝ), (2:ℝ))) (x - (-6), y - 2) = (x-(-6)) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) ((-6:ℝ), (2:ℝ))) (x - (-6), y - 2) = (y-2) * (17)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2) = (fun x => x ^ 3 + 2 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (2:ℝ)) (x - (-6), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (1:ℝ)) (x-0, y-1) = 0) → ((x-0) * (-4) + (y-1) * (9) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 4 * p.1) ((0:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 2 + p.2) ((0:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) ((0:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 4 * p.1) ((0:ℝ), (1:ℝ))) (x - 0, y - 1) = (x-0) * (-4)  := by
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (1:ℝ))) (x - 0, y - 1) = (y-1) * (9)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (1:ℝ)) (x - 0, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (44) - (y-1) * (6) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2) ((2:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + p.2) ((2:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2) ((2:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2) ((2:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + p.2) ((2:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 - 4 * p.1 ^ 2) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (x-2) * (44)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 4 * p.1 ^ 2) = (fun x => 5 * x ^ 3 - 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + p.2) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (y-1) * (6)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + p.2) = (fun x => 3 * x ^ 3 - 2 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (1:ℝ)) (x - 2, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 4 * p.2 ^ 3 + p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (192) + (y-(-1)) * (13) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3) ((4:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + p.2) ((4:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 4 * p.2 ^ 3 + p.2) ((4:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3) ((4:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2) ((4:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (x-4) * (192)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3) = (fun x => 4 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + p.2) ((4:ℝ), (-1:ℝ))) (x - 4, y - (-1)) = (y-(-1)) * (13)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + p.2) = (fun x => 4 * x ^ 3 + x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-1:ℝ)) (x - 4, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * p.2 - c) ((-3:ℝ), (-3:ℝ)) (x-(-3), y-(-3)) = 0) → ((x-(-3)) * (-240) + (y-(-3)) * (-15) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 2) ((-3:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-3:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * p.2) ((-3:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 2) ((-3:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-3:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 + 4 * p.1 ^ 2) ((-3:ℝ), (-3:ℝ))) (x - (-3), y - (-3)) = (x-(-3)) * (-240)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 + 4 * p.1 ^ 2) = (fun x => 2 * x ^ 4 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-3:ℝ), (-3:ℝ))) (x - (-3), y - (-3)) = (y-(-3)) * (-15)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 3 * p.2) = (fun x => 3 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-3:ℝ)) (x - (-3), y - (-3)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (17) + (y-(-3)) * (-24) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((2:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((2:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((2:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 + p.1) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (x-2) * (17)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (y-(-3)) * (-24)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-3:ℝ)) (x - 2, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) (x-3, y-1) = 0) → ((x-3) * (1) - (y-1) * (13) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((3:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((3:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2) ((3:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((3:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((3:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((3:ℝ), (1:ℝ))) (x - 3, y - 1) = (x-3) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((3:ℝ), (1:ℝ))) (x - 3, y - 1) = (y-1) * (13)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 4 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (1:ℝ)) (x - 3, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (4) - (y-3) * (432) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((3:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4) ((3:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4) ((3:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((3:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4) ((3:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (x-3) * (4)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) = (fun x => x ^ 3 - 4 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (y-3) * (432)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4) = (fun x => 4 * x ^ 4) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (3:ℝ)) (x - 3, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - p.1 ^ 2 + 4 * p.2 ^ 3 + 4 * p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (426) + (y-0) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 2) ((3:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 + 4 * p.2) ((3:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 - p.1 ^ 2 + 4 * p.2 ^ 3 + 4 * p.2) ((3:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 2) ((3:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 + 4 * p.2) ((3:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 - p.1 ^ 2) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (x-3) * (426)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - p.1 ^ 2) = (fun x => 4 * x ^ 4 - x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 + 4 * p.2) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (y-0) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 + 4 * p.2) = (fun x => 4 * x ^ 3 + 4 * x) ∘ (fun p => p.2) := rfl
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (0:ℝ)) (x - 3, y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) ((-3:ℝ), (-1:ℝ)) (x-(-3), y-(-1)) = 0) → ((x-(-3)) * (-9) + (y-(-1)) * (23) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((-3:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((-3:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((-3:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((-3:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((-3:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - 3 * p.1) ((-3:ℝ), (-1:ℝ))) (x - (-3), y - (-1)) = (x-(-3)) * (-9)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) ((-3:ℝ), (-1:ℝ))) (x - (-3), y - (-1)) = (y-(-1)) * (23)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2) = (fun x => 4 * x ^ 3 - 3 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-1:ℝ)) (x - (-3), y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - c) ((-6:ℝ), (5:ℝ)) (x-(-6), y-5) = 0) → ((x-(-6)) * (-36) + (y-5) * (260) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2) ((-6:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2) ((-6:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 4 * p.2 ^ 3 - 4 * p.2 ^ 2) ((-6:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2) ((-6:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2) ((-6:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2) ((-6:ℝ), (5:ℝ))) (x - (-6), y - 5) = (x-(-6)) * (-36)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2) = (fun x => 3 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2) ((-6:ℝ), (5:ℝ))) (x - (-6), y - 5) = (y-5) * (260)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 4 * p.2 ^ 2) = (fun x => 4 * x ^ 3 - 4 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (5:ℝ)) (x - (-6), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + 3 * p.2 - c) ((-3:ℝ), (-3:ℝ)) (x-(-3), y-(-3)) = 0) → ((x-(-3)) * (2) + (y-(-3)) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((-3:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2) ((-3:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 + 3 * p.2) ((-3:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((-3:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2) ((-3:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((-3:ℝ), (-3:ℝ))) (x - (-3), y - (-3)) = (x-(-3)) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2) ((-3:ℝ), (-3:ℝ))) (x - (-3), y - (-3)) = (y-(-3)) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2) = (fun x => 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-3:ℝ)) (x - (-3), y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) ((-3:ℝ), (-6:ℝ)) (x-(-3), y-(-6)) = 0) → ((x-(-3)) * (27) + (y-(-6)) * (-10) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3) ((-3:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-3:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + p.2 ^ 2 + 2 * p.2) ((-3:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3) ((-3:ℝ), (-6:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-3:ℝ), (-6:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3) ((-3:ℝ), (-6:ℝ))) (x - (-3), y - (-6)) = (x-(-3)) * (27)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + 2 * p.2) ((-3:ℝ), (-6:ℝ))) (x - (-3), y - (-6)) = (y-(-6)) * (-10)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-6:ℝ)) (x - (-3), y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst.pow _
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((1:ℝ), (5:ℝ)) (x-1, y-5) = 0) → ((x-1) * (3) + (y-5) * (885) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) ((1:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((1:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((1:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) ((1:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((1:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 5 * p.1) ((1:ℝ), (5:ℝ))) (x - 1, y - 5) = (x-1) * (3)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((1:ℝ), (5:ℝ))) (x - 1, y - 5) = (y-5) * (885)  := by
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (5:ℝ)) (x - 1, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (38) - (y-(-5)) * (133) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((6:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((6:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 + 2 * p.1) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (x-6) * (38)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (y-(-5)) * (133)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 2 * p.2 ^ 2 + 3 * p.2) = (fun x => 2 * x ^ 3 + 2 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-5:ℝ)) (x - 6, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 0) → ((x-5) * (30) + (y-(-4)) * (-116) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2) ((5:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2) ((5:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2) ((5:ℝ), (-4:ℝ))) (x - 5, y - (-4)) = (x-5) * (30)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 2) = (fun x => 3 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-4:ℝ))) (x - 5, y - (-4)) = (y-(-4)) * (-116)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) = (fun x => x ^ 4 + 3 * x ^ 3 - 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (-4:ℝ)) (x - 5, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (540) + (y-(-2)) * (57) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3) ((6:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((6:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((6:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3) ((6:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((6:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (x-6) * (540)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3) = (fun x => 5 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((6:ℝ), (-2:ℝ))) (x - 6, y - (-2)) = (y-(-2)) * (57)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) = (fun x => 5 * x ^ 3 + x ^ 2 + x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-2:ℝ)) (x - 6, y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 2 * p.2 ^ 3 - 3 * p.2 - c) ((-1:ℝ), (0:ℝ)) (x-(-1), y-0) = 0) → ((x-(-1)) * (-2) - (y-0) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2) ((-1:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - 2 * p.2 ^ 3 - 3 * p.2) ((-1:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2) ((-1:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2) ((-1:ℝ), (0:ℝ))) (x - (-1), y - 0) = (x-(-1)) * (-2)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), (0:ℝ))) (x - (-1), y - 0) = (y-0) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3 + 3 * p.2) = (fun x => 2 * x ^ 3 + 3 * x) ∘ (fun p => p.2) := rfl
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (0:ℝ)) (x - (-1), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst.pow _
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 - 2 * p.2 - c) ((-2:ℝ), (5:ℝ)) (x-(-2), y-5) = 0) → ((x-(-2)) * (3) + (y-5) * (8) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((-2:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 2 * p.2) ((-2:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 + p.2 ^ 2 - 2 * p.2) ((-2:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((-2:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 - 2 * p.2) ((-2:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((-2:ℝ), (5:ℝ))) (x - (-2), y - 5) = (x-(-2)) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 2 * p.2) ((-2:ℝ), (5:ℝ))) (x - (-2), y - 5) = (y-5) * (8)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (5:ℝ)) (x - (-2), y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 4 * p.2 ^ 4 - 3 * p.2 ^ 2 + 2 * p.2 - c) ((3:ℝ), (4:ℝ)) (x-3, y-4) = 0) → ((x-3) * (2) - (y-4) * (1046) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((3:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 + 3 * p.2 ^ 2 - 2 * p.2) ((3:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 - 4 * p.2 ^ 4 - 3 * p.2 ^ 2 + 2 * p.2) ((3:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((3:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 + 3 * p.2 ^ 2 - 2 * p.2) ((3:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((3:ℝ), (4:ℝ))) (x - 3, y - 4) = (x-3) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 + 3 * p.2 ^ 2 - 2 * p.2) ((3:ℝ), (4:ℝ))) (x - 3, y - 4) = (y-4) * (1046)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 + 3 * p.2 ^ 2 - 2 * p.2) = (fun x => 4 * x ^ 4 + 3 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (4:ℝ)) (x - 3, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (-4:ℝ)) (x-0, y-(-4)) = 0) → ((x-0) * (0) + (y-(-4)) * (177) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) ((0:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) ((0:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-4:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) ((0:ℝ), (-4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2) ((0:ℝ), (-4:ℝ))) (x - 0, y - (-4)) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) ((0:ℝ), (-4:ℝ))) (x - 0, y - (-4)) = (y-(-4)) * (177)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2) = (fun x => 3 * x ^ 3 - 4 * x ^ 2 + x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (-4:ℝ)) (x - 0, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 - 5 * p.2 - c) ((0:ℝ), (-1:ℝ)) (x-0, y-(-1)) = 0) → ((x-0) * (-5) - (y-(-1)) * (14) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2) ((0:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 - 5 * p.2) ((0:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (-1:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2) ((0:ℝ), (-1:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1) ((0:ℝ), (-1:ℝ))) (x - 0, y - (-1)) = (x-0) * (-5)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1) = (fun x => 3 * x ^ 3 + 5 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 + 5 * p.2) ((0:ℝ), (-1:ℝ))) (x - 0, y - (-1)) = (y-(-1)) * (14)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 + 5 * p.2) = (fun x => 3 * x ^ 3 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (-1:ℝ)) (x - 0, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 4 * p.2 ^ 2 - c) ((4:ℝ), (-5:ℝ)) (x-4, y-(-5)) = 0) → ((x-4) * (3) - (y-(-5)) * (-40) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((4:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((4:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 - 4 * p.2 ^ 2) ((4:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((4:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((4:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((4:ℝ), (-5:ℝ))) (x - 4, y - (-5)) = (x-4) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((4:ℝ), (-5:ℝ))) (x - 4, y - (-5)) = (y-(-5)) * (-40)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (-5:ℝ)) (x - 4, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 4 * p.2 ^ 3 - c) ((-3:ℝ), (-6:ℝ)) (x-(-3), y-(-6)) = 0) → ((x-(-3)) * (33) - (y-(-6)) * (432) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-3:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3) ((-3:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - p.1 ^ 2 - 4 * p.2 ^ 3) ((-3:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-3:ℝ), (-6:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3) ((-3:ℝ), (-6:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2) ((-3:ℝ), (-6:ℝ))) (x - (-3), y - (-6)) = (x-(-3)) * (33)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - p.1 ^ 2) = (fun x => x ^ 3 - x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3) ((-3:ℝ), (-6:ℝ))) (x - (-3), y - (-6)) = (y-(-6)) * (432)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3) = (fun x => 4 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-6:ℝ)) (x - (-3), y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2 - c) ((-5:ℝ), (-4:ℝ)) (x-(-5), y-(-4)) = 0) → ((x-(-5)) * (-35) - (y-(-4)) * (164) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2) ((-5:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-4:ℝ))) (x - (-5), y - (-4)) = (x-(-5)) * (-35)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2) ((-5:ℝ), (-4:ℝ))) (x - (-5), y - (-4)) = (y-(-4)) * (164)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2) = (fun x => 3 * x ^ 3 - 2 * x ^ 2 + 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-4:ℝ)) (x - (-5), y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2 - c) ((-1:ℝ), (4:ℝ)) (x-(-1), y-4) = 0) → ((x-(-1)) * (-3) + (y-4) * (286) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1) ((-1:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2) ((-1:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2) ((-1:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1) ((-1:ℝ), (4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2) ((-1:ℝ), (4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1) ((-1:ℝ), (4:ℝ))) (x - (-1), y - 4) = (x-(-1)) * (-3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1) = (fun x => x ^ 4 + 2 * x ^ 3 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2) ((-1:ℝ), (4:ℝ))) (x - (-1), y - 4) = (y-4) * (286)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2) = (fun x => x ^ 4 + 4 * x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (4:ℝ)) (x - (-1), y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (45) + (y-(-5)) * (-2582) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) ((6:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) ((6:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (x-6) * (45)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1) = (fun x => x ^ 3 - 5 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
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
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (y-(-5)) * (-2582)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) = (fun x => 5 * x ^ 4 - x ^ 3 + x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-5:ℝ)) (x - 6, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (2) + (y-5) * (41) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((0:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + 4 * p.2 ^ 2 + p.2) ((0:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((0:ℝ), (5:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (x-0) * (2)  := by
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((0:ℝ), (5:ℝ))) (x - 0, y - 5) = (y-5) * (41)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (5:ℝ)) (x - 0, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 - 5 * p.2 ^ 2 - c) ((-5:ℝ), (1:ℝ)) (x-(-5), y-1) = 0) → ((x-(-5)) * (-11) - (y-1) * (10) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 - p.1) ((-5:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 - p.1 - 5 * p.2 ^ 2) ((-5:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-5:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-5:ℝ), (1:ℝ))) (x - (-5), y - 1) = (x-(-5)) * (-11)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 - p.1) = (fun x => x ^ 2 - x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2) ((-5:ℝ), (1:ℝ))) (x - (-5), y - 1) = (y-1) * (10)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (1:ℝ)) (x - (-5), y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 3 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 3 * p.2 - c) ((6:ℝ), (6:ℝ)) (x-6, y-6) = 0) → ((x-6) * (15) - (y-6) * (3177) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 3 * p.1) ((6:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 3 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 3 * p.2) ((6:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) ((6:ℝ), (6:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 3 * p.1) ((6:ℝ), (6:ℝ))) (x - 6, y - 6) = (x-6) * (15)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 3 * p.2) ((6:ℝ), (6:ℝ))) (x - 6, y - 6) = (y-6) * (3177)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 2 * p.2 ^ 3 - 5 * p.2 ^ 2 - 3 * p.2) = (fun x => 4 * x ^ 4 - 2 * x ^ 3 - 5 * x ^ 2 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (6:ℝ)) (x - 6, y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 3 * p.2 ^ 2 + p.2 - c) ((2:ℝ), (5:ℝ)) (x-2, y-5) = 0) → ((x-2) * (2) - (y-5) * (29) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((2:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 - p.2) ((2:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 - 3 * p.2 ^ 2 + p.2) ((2:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((2:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) ((2:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((2:ℝ), (5:ℝ))) (x - 2, y - 5) = (x-2) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 - p.2) ((2:ℝ), (5:ℝ))) (x - 2, y - 5) = (y-5) * (29)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (5:ℝ)) (x - 2, y - 5) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2 - c) ((5:ℝ), (-5:ℝ)) (x-5, y-(-5)) = 0) → ((x-5) * (18) + (y-(-5)) * (-815) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((5:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) ((5:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) ((5:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((5:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) ((5:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((5:ℝ), (-5:ℝ))) (x - 5, y - (-5)) = (x-5) * (18)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 2 * p.1) = (fun x => 2 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) ((5:ℝ), (-5:ℝ))) (x - 5, y - (-5)) = (y-(-5)) * (-815)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2) = (fun x => 2 * x ^ 4 + 2 * x ^ 3 - 4 * x ^ 2 - 5 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (-5:ℝ)) (x - 5, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) (x-3, y-1) = 0) → ((x-3) * (3) - (y-1) * (5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((3:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2) ((3:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 - 5 * p.2) ((3:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((3:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2) ((3:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((3:ℝ), (1:ℝ))) (x - 3, y - 1) = (x-3) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2) ((3:ℝ), (1:ℝ))) (x - 3, y - 1) = (y-1) * (5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2) = (fun x => 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (1:ℝ)) (x - 3, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + 3 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (11) - (y-1) * (12) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2 - 2 * p.2) ((2:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 + 3 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2 + 2 * p.2) ((2:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (1:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2 - 2 * p.2) ((2:ℝ), (1:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 + 3 * p.1) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (x-2) * (11)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 + 3 * p.1) = (fun x => 2 * x ^ 2 + 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + p.2 ^ 2 - 2 * p.2) ((2:ℝ), (1:ℝ))) (x - 2, y - 1) = (y-1) * (12)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + p.2 ^ 2 - 2 * p.2) = (fun x => 3 * x ^ 4 + x ^ 2 - 2 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (1:ℝ)) (x - 2, y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2 - c) ((-2:ℝ), (1:ℝ)) (x-(-2), y-1) = 0) → ((x-(-2)) * (-19) + (y-1) * (23) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) ((-2:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) ((-2:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2) ((-2:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) ((-2:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) ((-2:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 3 * p.1) ((-2:ℝ), (1:ℝ))) (x - (-2), y - 1) = (x-(-2)) * (-19)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + 4 * p.2 ^ 2) ((-2:ℝ), (1:ℝ))) (x - (-2), y - 1) = (y-1) * (23)  := by
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (1:ℝ)) (x - (-2), y - 1) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) ((-6:ℝ), (5:ℝ)) (x-(-6), y-5) = 0) → ((x-(-6)) * (-37) - (y-5) * (33) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - p.1) ((-6:ℝ), (5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-6:ℝ), (5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2) ((-6:ℝ), (5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 2 - p.1) ((-6:ℝ), (5:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-6:ℝ), (5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 2 - p.1) ((-6:ℝ), (5:ℝ))) (x - (-6), y - 5) = (x-(-6)) * (-37)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 2 + 3 * p.2) ((-6:ℝ), (5:ℝ))) (x - (-6), y - 5) = (y-5) * (33)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 2 + 3 * p.2) = (fun x => 3 * x ^ 2 + 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-6:ℝ), (5:ℝ)) (x - (-6), y - 5) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 - c) ((3:ℝ), (-4:ℝ)) (x-3, y-(-4)) = 0) → ((x-3) * (35) - (y-(-4)) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((3:ℝ), (-4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2) ((3:ℝ), (-4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2) ((3:ℝ), (-4:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((3:ℝ), (-4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2) ((3:ℝ), (-4:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + 5 * p.1) ((3:ℝ), (-4:ℝ))) (x - 3, y - (-4)) = (x-3) * (35)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2) ((3:ℝ), (-4:ℝ))) (x - 3, y - (-4)) = (y-(-4)) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2) = (fun x => 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (-4:ℝ)) (x - 3, y - (-4)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - p.2 ^ 3 - 3 * p.2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (81) - (y-(-2)) * (15) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3) ((-3:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 3 + 3 * p.2) ((-3:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 - p.2 ^ 3 - 3 * p.2) ((-3:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3) ((-3:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2) ((-3:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (x-(-3)) * (81)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3) = (fun x => 3 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + 3 * p.2) ((-3:ℝ), (-2:ℝ))) (x - (-3), y - (-2)) = (y-(-2)) * (15)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 3 + 3 * p.2) = (fun x => x ^ 3 + 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-2:ℝ)) (x - (-3), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 - 3 * p.2 - c) ((-3:ℝ), (-1:ℝ)) (x-(-3), y-(-1)) = 0) → ((x-(-3)) * (106) + (y-(-1)) * (-7) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1) ((-3:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2) ((-3:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 - 3 * p.2) ((-3:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1) ((-3:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2) ((-3:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1) ((-3:ℝ), (-1:ℝ))) (x - (-3), y - (-1)) = (x-(-3)) * (106)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1) = (fun x => 5 * x ^ 3 + 5 * x ^ 2 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2) ((-3:ℝ), (-1:ℝ))) (x - (-3), y - (-1)) = (y-(-1)) * (-7)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2) = (fun x => x ^ 4 - 3 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-1:ℝ)) (x - (-3), y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.2 - c) ((-3:ℝ), (0:ℝ)) (x-(-3), y-0) = 0) → ((x-(-3)) * (30) + (y-0) * (5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-3:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2) ((-3:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.2) ((-3:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-3:ℝ), (0:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2) ((-3:ℝ), (0:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 4 * p.1 ^ 2) ((-3:ℝ), (0:ℝ))) (x - (-3), y - 0) = (x-(-3)) * (30)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 4 * p.1 ^ 2) = (fun x => 2 * x ^ 3 + 4 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2) ((-3:ℝ), (0:ℝ))) (x - (-3), y - 0) = (y-0) * (5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2) = (fun x => 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (0:ℝ)) (x - (-3), y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 5 * p.1 + 2 * p.2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (-1) + (y-6) * (2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 5 * p.1) ((-3:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2) ((-3:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 5 * p.1 + 2 * p.2) ((-3:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 5 * p.1) ((-3:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2) ((-3:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 5 * p.1) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (x-(-3)) * (-1)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2) ((-3:ℝ), (6:ℝ))) (x - (-3), y - 6) = (y-6) * (2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2) = (fun x => 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (6:ℝ)) (x - (-3), y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 4 * p.1 + 4 * p.2 - c) ((1:ℝ), (-6:ℝ)) (x-1, y-(-6)) = 0) → ((x-1) * (13) + (y-(-6)) * (4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1) ((1:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2) ((1:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 4 * p.1 + 4 * p.2) ((1:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1) ((1:ℝ), (-6:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2) ((1:ℝ), (-6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 4 * p.1) ((1:ℝ), (-6:ℝ))) (x - 1, y - (-6)) = (x-1) * (13)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 4 * p.1) = (fun x => 3 * x ^ 3 + 4 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2) ((1:ℝ), (-6:ℝ))) (x - 1, y - (-6)) = (y-(-6)) * (4)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2) = (fun x => 4 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((1:ℝ), (-6:ℝ)) (x - 1, y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (528) + (y-3) * (135) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3) ((3:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3) ((3:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 3) ((3:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (x-3) * (528)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1) = (fun x => 4 * x ^ 4 + 3 * x ^ 3 + 3 * x ^ 2 - 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3) ((3:ℝ), (3:ℝ))) (x - 3, y - 3) = (y-3) * (135)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3) = (fun x => 5 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (3:ℝ)) (x - 3, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 - 5 * p.2 - c) ((-5:ℝ), (-5:ℝ)) (x-(-5), y-(-5)) = 0) → ((x-(-5)) * (-1330) - (y-(-5)) * (5) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2) ((-5:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 - 5 * p.2) ((-5:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2) ((-5:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) ((-5:ℝ), (-5:ℝ))) (x - (-5), y - (-5)) = (x-(-5)) * (-1330)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1) = (fun x => 2 * x ^ 4 - 5 * x ^ 3 - 5 * x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2) ((-5:ℝ), (-5:ℝ))) (x - (-5), y - (-5)) = (y-(-5)) * (5)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2) = (fun x => 5 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (-5:ℝ)) (x - (-5), y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + 3 * p.2 - c) ((-4:ℝ), (2:ℝ)) (x-(-4), y-2) = 0) → ((x-(-4)) * (-39) + (y-2) * (3) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-4:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2) ((-4:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + p.1 + 3 * p.2) ((-4:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-4:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => 3 * p.2) ((-4:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-4:ℝ), (2:ℝ))) (x - (-4), y - 2) = (x-(-4)) * (-39)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2) ((-4:ℝ), (2:ℝ))) (x - (-4), y - 2) = (y-2) * (3)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2) = (fun x => 3 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (2:ℝ)) (x - (-4), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 5 * p.2 ^ 2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (3) - (y-(-5)) * (-50) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1) ((6:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2) ((6:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 - 5 * p.2 ^ 2) ((6:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1) ((6:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 2) ((6:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (x-6) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1) = (fun x => 3 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2) ((6:ℝ), (-5:ℝ))) (x - 6, y - (-5)) = (y-(-5)) * (-50)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (-5:ℝ)) (x - 6, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + 5 * p.2 ^ 2 - c) ((2:ℝ), (6:ℝ)) (x-2, y-6) = 0) → ((x-2) * (1) + (y-6) * (60) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((2:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2) ((2:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 + 5 * p.2 ^ 2) ((2:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((2:ℝ), (6:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2) ((2:ℝ), (6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((2:ℝ), (6:ℝ))) (x - 2, y - 6) = (x-2) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2) ((2:ℝ), (6:ℝ))) (x - 2, y - 6) = (y-6) * (60)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 2) = (fun x => 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (6:ℝ)) (x - 2, y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (differentiableAt_fst) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 4 * p.2 ^ 2 + p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (28) + (y-3) * (25) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((2:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 4 * p.2 ^ 2 + p.2) ((2:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((2:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (x-2) * (28)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 5 * p.1 ^ 2) = (fun x => 4 * x ^ 3 - 5 * x ^ 2) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2 + p.2) ((2:ℝ), (3:ℝ))) (x - 2, y - 3) = (y-3) * (25)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (3:ℝ)) (x - 2, y - 3) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((0:ℝ), (6:ℝ)) (x-0, y-6) = 0) → ((x-0) * (0) - (y-6) * (2903) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((0:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2) ((0:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (6:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((0:ℝ), (6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3) ((0:ℝ), (6:ℝ))) (x - 0, y - 6) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2 - p.2) ((0:ℝ), (6:ℝ))) (x - 0, y - 6) = (y-6) * (2903)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - p.2 ^ 2 - p.2) = (fun x => 4 * x ^ 4 - 5 * x ^ 3 - x ^ 2 - x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (6:ℝ)) (x - 0, y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + p.2 ^ 2 + p.2 - c) ((3:ℝ), (-1:ℝ)) (x-3, y-(-1)) = 0) → ((x-3) * (8) + (y-(-1)) * (-1) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((3:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) ((3:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 2 + 2 * p.1 + p.2 ^ 2 + p.2) ((3:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((3:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) ((3:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 2 + 2 * p.1) ((3:ℝ), (-1:ℝ))) (x - 3, y - (-1)) = (x-3) * (8)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) ((3:ℝ), (-1:ℝ))) (x - 3, y - (-1)) = (y-(-1)) * (-1)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (-1:ℝ)) (x - 3, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 4 - 5 * p.2 ^ 2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) = 0) → ((x-5) * (19) + (y-4) * (216) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 5 * p.2 ^ 2) ((5:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - p.1 + p.2 ^ 4 - 5 * p.2 ^ 2) ((5:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - 5 * p.2 ^ 2) ((5:ℝ), (4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ))) (x - 5, y - 4) = (x-5) * (19)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - p.1) = (fun x => 2 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 5 * p.2 ^ 2) ((5:ℝ), (4:ℝ))) (x - 5, y - 4) = (y-4) * (216)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 5 * p.2 ^ 2) = (fun x => x ^ 4 - 5 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (4:ℝ)) (x - 5, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.1 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2 - c) ((4:ℝ), (4:ℝ)) (x-4, y-4) = 0) → ((x-4) * (31) - (y-4) * (162) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - p.1) ((4:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) ((4:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 2 - p.1 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2) ((4:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 2 - p.1) ((4:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) ((4:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 2 - p.1) ((4:ℝ), (4:ℝ))) (x - 4, y - 4) = (x-4) * (31)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) ((4:ℝ), (4:ℝ))) (x - 4, y - 4) = (y-4) * (162)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 4 * p.2 ^ 2 + 2 * p.2) = (fun x => 4 * x ^ 3 - 4 * x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((4:ℝ), (4:ℝ)) (x - 4, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.2 ^ 3 - p.2 - c) ((5:ℝ), (3:ℝ)) (x-5, y-3) = 0) → ((x-5) * (300) - (y-3) * (136) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3) ((5:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 + p.2) ((5:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 5 * p.2 ^ 3 - p.2) ((5:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3) ((5:ℝ), (3:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2) ((5:ℝ), (3:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3) ((5:ℝ), (3:ℝ))) (x - 5, y - 3) = (x-5) * (300)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3) = (fun x => 4 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 + p.2) ((5:ℝ), (3:ℝ))) (x - 5, y - 3) = (y-3) * (136)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 + p.2) = (fun x => 5 * x ^ 3 + x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (3:ℝ)) (x - 5, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - p.2 ^ 4 - 3 * p.2 ^ 2 - c) ((3:ℝ), (-6:ℝ)) (x-3, y-(-6)) = 0) → ((x-3) * (2) - (y-(-6)) * (-900) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((3:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 2) ((3:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 - p.2 ^ 4 - 3 * p.2 ^ 2) ((3:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((3:ℝ), (-6:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 2) ((3:ℝ), (-6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((3:ℝ), (-6:ℝ))) (x - 3, y - (-6)) = (x-3) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 2) ((3:ℝ), (-6:ℝ))) (x - 3, y - (-6)) = (y-(-6)) * (-900)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 3 * p.2 ^ 2) = (fun x => x ^ 4 + 3 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
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
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (-6:ℝ)) (x - 3, y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 + 4 * p.2 - c) ((5:ℝ), (-5:ℝ)) (x-5, y-(-5)) = 0) → ((x-5) * (76) - (y-(-5)) * (296) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 + p.1) ((5:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 + 4 * p.2) ((5:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 + p.1) ((5:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 + p.1) ((5:ℝ), (-5:ℝ))) (x - 5, y - (-5)) = (x-5) * (76)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 + p.1) = (fun x => x ^ 3 + x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((5:ℝ), (-5:ℝ))) (x - 5, y - (-5)) = (y-(-5)) * (296)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 3 - 4 * p.2) = (fun x => 4 * x ^ 3 - 4 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (-5:ℝ)) (x - 5, y - (-5)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 2 + 4 * p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (1) - (y-0) * (-4) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((3:ℝ), (0:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((3:ℝ), (0:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 - p.2 ^ 2 + 4 * p.2) ((3:ℝ), (0:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((3:ℝ), (0:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((3:ℝ), (0:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (x-3) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((3:ℝ), (0:ℝ))) (x - 3, y - 0) = (y-0) * (-4)  := by
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
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (0:ℝ)) (x - 3, y - 0) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_fst) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 4 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (358) + (y-3) * (2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1) ((6:ℝ), (3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((6:ℝ), (3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 4 * p.2) ((6:ℝ), (3:ℝ))
      = 
      fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1) ((6:ℝ), (3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((6:ℝ), (3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (x-6) * (358)  := by
    have hp1comp : (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1) = (fun x => 3 * x ^ 3 + 3 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 - 4 * p.2) ((6:ℝ), (3:ℝ))) (x - 6, y - 3) = (y-3) * (2)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((6:ℝ), (3:ℝ)) (x - 6, y - 3) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 2 - 5 * p.2 - c) ((2:ℝ), (-1:ℝ)) (x-2, y-(-1)) = 0) → ((x-2) * (3) + (y-(-1)) * (-15) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3 - p.1 ^ 2 - 5 * p.1) ((2:ℝ), (-1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) ((2:ℝ), (-1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 2 - 5 * p.2) ((2:ℝ), (-1:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2 - 5 * p.1) ((2:ℝ), (-1:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) ((2:ℝ), (-1:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3 - p.1 ^ 2 - 5 * p.1) ((2:ℝ), (-1:ℝ))) (x - 2, y - (-1)) = (x-2) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3 - p.1 ^ 2 - 5 * p.1) = (fun x => x ^ 3 - x ^ 2 - 5 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
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
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 - 5 * p.2) ((2:ℝ), (-1:ℝ))) (x - 2, y - (-1)) = (y-(-1)) * (-15)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-1:ℝ)) (x - 2, y - (-1)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_fst.pow _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (108) + (y-(-5)) * (2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3) ((-3:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2) ((-3:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 + 2 * p.2) ((-3:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-3:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2) ((-3:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (x-(-3)) * (108)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3) = (fun x => 4 * x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2) ((-3:ℝ), (-5:ℝ))) (x - (-3), y - (-5)) = (y-(-5)) * (2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2) = (fun x => 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-3:ℝ), (-5:ℝ)) (x - (-3), y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) ((3:ℝ), (6:ℝ)) (x-3, y-6) = 0) → ((x-3) * (59) - (y-6) * (516) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 + 5 * p.1) ((3:ℝ), (6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2) ((3:ℝ), (6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 + 2 * p.2 ^ 2) ((3:ℝ), (6:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 3 + 5 * p.1) ((3:ℝ), (6:ℝ)) -
      fderiv ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2) ((3:ℝ), (6:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 3 + 5 * p.1) ((3:ℝ), (6:ℝ))) (x - 3, y - 6) = (x-3) * (59)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 3 + 5 * p.1) = (fun x => 2 * x ^ 3 + 5 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 3 - 2 * p.2 ^ 2) ((3:ℝ), (6:ℝ))) (x - 3, y - 6) = (y-6) * (516)  := by
    have hp2comp : (fun p : ℝ × ℝ => 5 * p.2 ^ 3 - 2 * p.2 ^ 2) = (fun x => 5 * x ^ 3 - 2 * x ^ 2) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (6:ℝ)) (x - 3, y - 6) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - 5 * p.2 ^ 3 - 5 * p.2 - c) ((-2:ℝ), (-5:ℝ)) (x-(-2), y-(-5)) = 0) → ((x-(-2)) * (-10) - (y-(-5)) * (-1120) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((-2:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 5 * p.2) ((-2:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - 5 * p.2 ^ 3 - 5 * p.2) ((-2:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((-2:ℝ), (-5:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 5 * p.2) ((-2:ℝ), (-5:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - 2 * p.1) ((-2:ℝ), (-5:ℝ))) (x - (-2), y - (-5)) = (x-(-2)) * (-10)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - 2 * p.1) = (fun x => 2 * x ^ 2 - 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 5 * p.2) ((-2:ℝ), (-5:ℝ))) (x - (-2), y - (-5)) = (y-(-5)) * (-1120)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 + 5 * p.2 ^ 3 + 5 * p.2) = (fun x => 3 * x ^ 4 + 5 * x ^ 3 + 5 * x) ∘ (fun p => p.2) := rfl
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
    norm_num
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

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (-5:ℝ)) (x - (-2), y - (-5)) = 0 := by
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

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 2 * p.2 ^ 3 - c) ((2:ℝ), (-6:ℝ)) (x-2, y-(-6)) = 0) → ((x-2) * (112) + (y-(-6)) * (216) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((2:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3) ((2:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 2 * p.2 ^ 3) ((2:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((2:ℝ), (-6:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 3) ((2:ℝ), (-6:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) ((2:ℝ), (-6:ℝ))) (x - 2, y - (-6)) = (x-2) * (112)  := by
    have hp1comp : (fun p : ℝ × ℝ => 5 * p.1 ^ 4 - 4 * p.1 ^ 3) = (fun x => 5 * x ^ 4 - 4 * x ^ 3) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3) ((2:ℝ), (-6:ℝ))) (x - 2, y - (-6)) = (y-(-6)) * (216)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-6:ℝ)) (x - 2, y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (1) + (y-(-3)) * (-193) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1) ((2:ℝ), (-3:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) ((2:ℝ), (-3:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) ((2:ℝ), (-3:ℝ))
      = 
      fderiv ℝ (fun p => p.1) ((2:ℝ), (-3:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) ((2:ℝ), (-3:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (x-2) * (1)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1) = (fun x => x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_id
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) ((2:ℝ), (-3:ℝ))) (x - 2, y - (-3)) = (y-(-3)) * (-193)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2) = (fun x => x ^ 4 - 3 * x ^ 3 + x ^ 2 + 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((2:ℝ), (-3:ℝ)) (x - 2, y - (-3)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (-9) + (y-(-2)) * (-35) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((-1:ℝ), (-2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((-1:ℝ), (-2:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((-1:ℝ), (-2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 + p.1) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (x-(-1)) * (-9)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) ((-1:ℝ), (-2:ℝ))) (x - (-1), y - (-2)) = (y-(-2)) * (-35)  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2) = (fun x => x ^ 4 + 2 * x ^ 2 + 5 * x) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
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
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-2:ℝ)) (x - (-1), y - (-2)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (DifferentiableAt.add (differentiableAt_snd.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 2 - p.2 - c) ((3:ℝ), (-5:ℝ)) (x-3, y-(-5)) = 0) → ((x-3) * (27) + (y-(-5)) * (-21) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (-5:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((3:ℝ), (-5:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      5 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 2 - p.2) ((3:ℝ), (-5:ℝ))
      = 
      fderiv ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (-5:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((3:ℝ), (-5:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 5 * p.1 ^ 2 - 3 * p.1) ((3:ℝ), (-5:ℝ))) (x - 3, y - (-5)) = (x-3) * (27)  := by
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((3:ℝ), (-5:ℝ))) (x - 3, y - (-5)) = (y-(-5)) * (-21)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((3:ℝ), (-5:ℝ)) (x - 3, y - (-5)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) = 0) → ((x-5) * (19) + (y-4) * (9) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => p.2 ^ 2 + p.2) ((5:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2) ((5:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ)) +
      fderiv ℝ (fun p => p.2 ^ 2 + p.2) ((5:ℝ), (4:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2 - p.1) ((5:ℝ), (4:ℝ))) (x - 5, y - 4) = (x-5) * (19)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2 - p.1) = (fun x => 2 * x ^ 2 - x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => p.2 ^ 2 + p.2) ((5:ℝ), (4:ℝ))) (x - 5, y - 4) = (y-4) * (9)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((5:ℝ), (4:ℝ)) (x - 5, y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)
  exact DifferentiableAt.add (differentiableAt_snd.pow _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (differentiableAt_fst)) (differentiableAt_snd.pow _)) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.2 ^ 3 - c) ((0:ℝ), (2:ℝ)) (x-0, y-2) = 0) → ((x-0) * (0) - (y-2) * (24) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2) ((0:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3) ((0:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 ^ 2 - 2 * p.2 ^ 3) ((0:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1 ^ 2) ((0:ℝ), (2:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 3) ((0:ℝ), (2:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1 ^ 2) ((0:ℝ), (2:ℝ))) (x - 0, y - 2) = (x-0) * (0)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1 ^ 2) = (fun x => 2 * x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2 ^ 3) ((0:ℝ), (2:ℝ))) (x - 0, y - 2) = (y-2) * (24)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2 ^ 3) = (fun x => 2 * x ^ 3) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((0:ℝ), (2:ℝ)) (x - 0, y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + p.2 - c) ((-5:ℝ), (2:ℝ)) (x-(-5), y-2) = 0) → ((x-(-5)) * (352) + (y-2) * (21) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (2:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2 + p.2) ((-5:ℝ), (2:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + p.2) ((-5:ℝ), (2:ℝ))
      = 
      fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (2:ℝ)) +
      fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) ((-5:ℝ), (2:ℝ)) := by
    rw [←fderiv_add]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1) ((-5:ℝ), (2:ℝ))) (x - (-5), y - 2) = (x-(-5)) * (352)  := by
    have hp1comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1) = (fun x => 4 * x ^ 3 - 5 * x ^ 2 + 2 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
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

  have h2 : (fderiv ℝ (fun p => 5 * p.2 ^ 2 + p.2) ((-5:ℝ), (2:ℝ))) (x - (-5), y - 2) = (y-2) * (21)  := by
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
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-5:ℝ), (2:ℝ)) (x - (-5), y - 2) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.2 ^ 2 - c) ((-1:ℝ), (-6:ℝ)) (x-(-1), y-(-6)) = 0) → ((x-(-1)) * (3) - (y-(-6)) * (-48) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 3) ((-1:ℝ), (-6:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 4 * p.2 ^ 2) ((-1:ℝ), (-6:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 3 - 4 * p.2 ^ 2) ((-1:ℝ), (-6:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 3) ((-1:ℝ), (-6:ℝ)) -
      fderiv ℝ (fun p => 4 * p.2 ^ 2) ((-1:ℝ), (-6:ℝ)) := by
    rw [←fderiv_sub]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 3) ((-1:ℝ), (-6:ℝ))) (x - (-1), y - (-6)) = (x-(-1)) * (3)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 3) = (fun x => x ^ 3) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    exact differentiableAt_id
    exact differentiableAt_pow _
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 4 * p.2 ^ 2) ((-1:ℝ), (-6:ℝ))) (x - (-1), y - (-6)) = (y-(-6)) * (-48)  := by
    have hp2comp : (fun p : ℝ × ℝ => 4 * p.2 ^ 2) = (fun x => 4 * x ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-1:ℝ), (-6:ℝ)) (x - (-1), y - (-6)) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact differentiableAt_fst.pow _
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 - c) ((-2:ℝ), (4:ℝ)) (x-(-2), y-4) = 0) → ((x-(-2)) * (-29) - (y-4) * (728) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => p.1 ^ 4 + 3 * p.1) ((-2:ℝ), (4:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2) ((-2:ℝ), (4:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      p.1 ^ 4 + 3 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2) ((-2:ℝ), (4:ℝ))
      = 
      fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1) ((-2:ℝ), (4:ℝ)) -
      fderiv ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2) ((-2:ℝ), (4:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    ext p
    ring
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  have h1 : (fderiv ℝ (fun p => p.1 ^ 4 + 3 * p.1) ((-2:ℝ), (4:ℝ))) (x - (-2), y - 4) = (x-(-2)) * (-29)  := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1) = (fun x => x ^ 4 + 3 * x) ∘ (fun p => p.1) := rfl
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
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 3 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2) ((-2:ℝ), (4:ℝ))) (x - (-2), y - 4) = (y-4) * (728)  := by
    have hp2comp : (fun p : ℝ × ℝ => 3 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2) = (fun x => 3 * x ^ 4 - x ^ 3 + x ^ 2) ∘ (fun p => p.2) := rfl
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-2:ℝ), (4:ℝ)) (x - (-2), y - 4) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))
  exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)
  
  exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_fst.pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd.pow _))) (differentiableAt_snd.pow _)) (differentiableAt_snd.pow _)

  exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + 2 * p.2 - c) ((-4:ℝ), (1:ℝ)) (x-(-4), y-1) = 0) → ((x-(-4)) * (2) + (y-1) * (2) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => 2 * p.1) ((-4:ℝ), (1:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => 2 * p.2) ((-4:ℝ), (1:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      2 * p.1 + 2 * p.2) ((-4:ℝ), (1:ℝ))
      = 
      fderiv ℝ (fun p => 2 * p.1) ((-4:ℝ), (1:ℝ)) +
      fderiv ℝ (fun p => 2 * p.2) ((-4:ℝ), (1:ℝ)) := by
    rw [←fderiv_add]
    
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  have h1 : (fderiv ℝ (fun p => 2 * p.1) ((-4:ℝ), (1:ℝ))) (x - (-4), y - 1) = (x-(-4)) * (2)  := by
    have hp1comp : (fun p : ℝ × ℝ => 2 * p.1) = (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => 2 * p.2) ((-4:ℝ), (1:ℝ))) (x - (-4), y - 1) = (y-1) * (2)  := by
    have hp2comp : (fun p : ℝ × ℝ => 2 * p.2) = (fun x => 2 * x) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => (c:ℝ)) ((-4:ℝ), (1:ℝ)) (x - (-4), y - 1) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)
  exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd)
  
  exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_snd))

  exact differentiableAt_const _
