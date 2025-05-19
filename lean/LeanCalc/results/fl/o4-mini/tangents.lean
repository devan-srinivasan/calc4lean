import Mathlib
open Real

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
  -- strip off the subtraction of the constant, the addition of the two summands,
  -- the two projections, and the one‐variable derivatives of
  --    x ↦ 5 x^3 + 5 x^2 + 5 x,   y ↦ 5 y^3 + y^2
  simp [ fderiv_sub, fderiv_const, fderiv_add, fderiv_comp, fderiv_fst, fderiv_snd
       , deriv_mul, deriv_pow, deriv_add, deriv_const, deriv_id ] at h
  -- now h is exactly "(x+1)*10 + (y-2)*64 = 0", up to the same notation
  simpa using h

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
-- separate off the “− c” part
rw [fderiv_sub] at h
-- split the sum 5*p.1 + (p.2^3 + p.2)
have h_split
  (hp1 : DifferentiableAt ℝ (fun p => 5 * p.1) (1, 2))
  (hp2 : DifferentiableAt ℝ (fun p => p.2 ^ 3 + p.2) (1, 2)) :
  fderiv ℝ (fun p : ℝ×ℝ => 5 * p.1 + p.2 ^ 3 + p.2) (1,2) =
    fderiv ℝ (fun p => 5 * p.1) (1,2) +
    fderiv ℝ (fun p => p.2 ^ 3 + p.2) (1,2) := by
  rw [← fderiv_add]
  exact hp1
  exact hp2
-- apply the split to the hypothesis
rw [h_split] at h
-- expand the two ContinuousLinearMap applications
rw [ContinuousLinearMap.sub_apply] at h
rw [ContinuousLinearMap.add_apply] at h

-- compute the derivative of p ↦ 5*p.1
have h1 : (fderiv ℝ (fun p => 5 * p.1) (1,2)) (x - 1, y - 2) = (x - 1) * 5 := by
  have comp1 : (fun p : ℝ×ℝ => 5 * p.1) = (fun t => 5 * t) ∘ Prod.fst := rfl
  rw [comp1, fderiv_comp, fderiv_fst, ← deriv_fderiv]
  -- now inside the scalar function `fun t => 5 * t`
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
  field_simp; norm_num
  all_goals
    try exact differentiableAt_const _
    try exact differentiableAt_id
  exact differentiableAt_fst

-- compute the derivative of p ↦ p.2^3 + p.2
have h2 : (fderiv ℝ (fun p => p.2 ^ 3 + p.2) (1,2)) (x - 1, y - 2) = (y - 2) * 13 := by
  have comp2 : (fun p : ℝ×ℝ => p.2 ^ 3 + p.2) = (fun t => t ^ 3 + t) ∘ Prod.snd := rfl
  rw [comp2, fderiv_comp, fderiv_snd, ← deriv_fderiv]
  -- inside `fun t => t^3 + t`
  nth_rewrite 1 [deriv_add]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [deriv_add]
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
  field_simp; norm_num
  all_goals
    try exact differentiableAt_id
    try exact differentiableAt_pow _
  exact differentiableAt_snd

-- the constant part has zero derivative
have h3 : fderiv ℝ (fun (_ : ℝ×ℝ) => c) (1,2) (x - 1, y - 2) = 0 := by
  rw [fderiv_const]; field_simp

-- substitute back into the hypothesis and finish
rw [h1, h2, h3] at h
ring_nf at h
linarith

-- finally discharge the differentiability hypotheses
all_goals
  try exact DifferentiableAt.mul (differentiableAt_const _)
                          (differentiableAt_fst)
  try exact DifferentiableAt.pow (differentiableAt_id) 3
  try exact differentiableAt_snd
  try exact differentiableAt_const _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c) ((-3:ℝ), (2:ℝ)) (x-(-3), y-2) = 0) → ((x-(-3)) * (-23) + (y-2) * (1) = 0) := by
  intro h
  -- split off the “- c” part
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 4*p.1^2 + p.1 + p.2) ((-3:ℝ),2))
    (hp2 : DifferentiableAt ℝ (fun p => (c:ℝ))         ((-3:ℝ),2)) :
    fderiv ℝ (fun p => 4*p.1^2 + p.1 + p.2 - c) ((-3),2) =
    fderiv ℝ (fun p => 4*p.1^2 + p.1 + p.2) ((-3),2) -
    fderiv ℝ (fun p => c)                     ((-3),2) :=
  by
    -- this is just `fderiv_sub`
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    exact hp1
    exact hp2
  rw [h_split] at h
  -- expand the subtraction of continuous linear maps
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h

  -- compute the derivative of 4*p.1^2 + p.1 + p.2
  have h1 :
    (fderiv ℝ (fun p => 4*p.1^2 + p.1 + p.2) ((-3:ℝ),2)) (x - (-3), y - 2)
    = (x - (-3)) * (-23) + (y - 2) * 1 :=
  by
    -- split into the p.1‐part and the p.2‐part
    have : (fun p : ℝ×ℝ => 4*p.1^2 + p.1 + p.2) =
              (fun x => 4*x^2 + x) ∘ Prod.fst + Prod.snd := by
      funext p; simp
    rw [this]
    -- fderiv of a sum
    rw [fderiv_add]
    -- first summand: 4*x^2 + x on the first coordinate
    rw [fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- now take the ordinary derivative of 4*x^2 + x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- assemble the continuous linear map
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- second summand: p ↦ p.2
    rw [ContinuousLinearMap.add_apply]
    rw [fderiv_snd]
    -- the derivative of snd is just projecting onto the second factor
    rw [ContinuousLinearMap.coe_snd']
    rfl

  -- the constant part “- c” has zero derivative
  have h2 : fderiv ℝ (fun p : ℝ×ℝ => (c:ℝ)) ((-3:ℝ),2) (x - (-3), y - 2) = 0 :=
    by simp [fderiv_const]

  -- plug into h and finish
  rw [h1] at h
  rw [h2] at h
  ring_nf at h
  linarith

  -- now discharge all the `DifferentiableAt` obligations
  all_goals
    try exact differentiableAt_const _
    try exact differentiableAt_id
    try exact differentiableAt_fst
    try exact differentiableAt_snd
    try exact differentiableAt_pow _
    try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    try exact (DifferentiableAt.add
                 (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
                 (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))

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
  -- peel off the “− c”
  rw [fderiv_sub] at h
  -- split the fderiv of A − B into fderiv A − fderiv B
  have h_split
    (hA : DifferentiableAt ℝ (fun p => 4*p.1^3 + 2*p.1^2 + 3*p.1) ((-3),(−2)))
    (hB : DifferentiableAt ℝ (fun p => 5*p.2^4 - 5*p.2^3 - p.2^2) ((-3),(−2))) :
    fderiv ℝ (fun p => 4*p.1^3 + 2*p.1^2 + 3*p.1
                     - (5*p.2^4 - 5*p.2^3 - p.2^2))
      ((-3),(−2))
    =
    fderiv ℝ (fun p => 4*p.1^3 + 2*p.1^2 + 3*p.1) ((-3),(−2))
    -
    fderiv ℝ (fun p => 5*p.2^4 - 5*p.2^3 - p.2^2) ((-3),(−2)) := by
    -- use `fderiv_sub`
    rw [← fderiv_sub]; congr 1; ext p; ring; exact hA; exact hB
  rw [h_split] at h
  -- expand the two subtractions
  rw [sub_apply, sub_apply] at h

  -- now compute fderiv of the p.1-part
  have h1 :
    (fderiv ℝ (fun p => 4*p.1^3 + 2*p.1^2 + 3*p.1) ((-3),(−2))) (x - (-3), y - (-2))
    = (x - (-3)) * 99 := by
    -- factor as (4t^3 + 2t^2 + 3t) ∘ fst
    have : (fun p:ℝ×ℝ => 4*p.1^3 + 2*p.1^2 + 3*p.1)
            = (fun t => 4*t^3 + 2*t^2 + 3*t) ∘ Prod.fst := rfl
    rw [this, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- compute derivative of 4t^3 + 2t^2 + 3t at t = -3
    nth_rewrite 1 [deriv_add]; nth_rewrite 1 [deriv_add];
      nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id''];
      nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    rw [comp_apply, smulRight_apply, coe_fst']
    field_simp; norm_num
    -- side-goals: differentiability
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_pow _
      <|> try exact differentiableAt_id
      <|> try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))

  -- now compute fderiv of the p.2-part
  have h2 :
    (fderiv ℝ (fun p => 5*p.2^4 - 5*p.2^3 - p.2^2) ((-3),(−2))) (x - (-3), y - (-2))
    = (y - (-2)) * (-216) := by
    -- factor as (5u^4 - 5u^3 - u^2) ∘ snd
    have : (fun p:ℝ×ℝ => 5*p.2^4 - 5*p.2^3 - p.2^2)
            = (fun u => 5*u^4 - 5*u^3 - u^2) ∘ Prod.snd := rfl
    rw [this, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- compute derivative at u = -2
    nth_rewrite 1 [deriv_sub]; nth_rewrite 1 [deriv_sub];
      nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const];
      nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id''];
      nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id''];
      nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    rw [comp_apply, smulRight_apply, coe_snd']
    field_simp; norm_num
    -- side-goals: differentiability
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_pow _
      <|> try exact differentiableAt_id
      <|> try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))

  -- the “− c” contributes zero
  have h3 :
    fderiv ℝ (fun _ => (c:ℝ)) ((-3),(−2)) (x - (-3), y - (-2)) = 0 := by
    rw [fderiv_const]; field_simp

  -- substitute the three computations into h
  rw [h1] at h; rw [h2] at h; rw [h3] at h
  -- simplify and finish
  ring_nf at h; linarith

  -- finally discharge the differentiability assumptions
  all_goals
    try
      simpa only [] using
      differentiableAt.sub
        (differentiableAt.add
          (differentiableAt_mul_const (differentiableAt_fst.pow 3) 4)
          (differentiableAt_add
            (differentiableAt_mul_const (differentiableAt_fst.pow 2) 2)
            (differentiableAt_mul_const differentiableAt_fst 3)))
        (differentiableAt_sub
          (differentiableAt_mul_const (differentiableAt_snd.pow 4) 5)
          (differentiableAt_add
            (differentiableAt_mul_const (differentiableAt_snd.pow 3) 5)
            (differentiableAt_mul_const (differentiableAt_snd.pow 2) 1)))

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (-4:ℝ)) (x-(-2), y-(-4)) = 0) → ((x-(-2)) * (-15) - (y-(-4)) * (7) = 0) := by
  intro h
  -- first peel off the “- c”
  rw [fderiv_sub] at h
  simp [fderiv_const] at h
  -- then peel off the p.2–part
  -- note that `f = (5*p.1^2 + 5*p.1) - (p.2^3 + 5*p.2^2 - p.2)`
  rw [fderiv_sub] at h
  -- now h is
  --   fderiv ℝ (fun p => 5*p.1^2 + 5*p.1) _ (x+2,y+4)
  -- - fderiv ℝ (fun p => p.2^3 + 5*p.2^2 - p.2) _ (x+2,y+4)
  -- = 0

  have h1 :
    fderiv ℝ (fun p => 5 * p.1^2 + 5 * p.1) ((-2),(-4)) (x + 2, y + 4)
      = (x + 2) * (-15) := by
    -- compose with fst, then use one‐variable deriv
    simp [fderiv_comp, fderiv_fst,
          deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]

  have h2 :
    fderiv ℝ (fun p => p.2^3 + 5 * p.2^2 - p.2) ((-2),(-4)) (x + 2, y + 4)
      = (y + 4) * 7 := by
    simp [fderiv_comp, fderiv_snd,
          deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]

  -- plug h1,h2 into h
  simpa [h1, h2] using h

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
-- split off the “- c” 
rw [fderiv_sub] at h

-- split the two non-constant parts with fderiv_add
have h_split
  (hp1 : DifferentiableAt ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ),(-5:ℝ)))
  (hp2 : DifferentiableAt ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ),(-5:ℝ))) :
    fderiv ℝ (fun p : ℝ×ℝ =>
      4 * p.1 ^ 2 - 4 * p.1 +
      p.2 ^ 4       - 2 * p.2 ^ 3 -
      2 * p.2 ^ 2   - 2 * p.2)
    ((1:ℝ),(-5:ℝ)) =
    fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ),(-5:ℝ)) +
    fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ),(-5:ℝ)) := by
  rw [← fderiv_add]
  exact hp1
  exact hp2

rw [h_split] at h
-- turn the ContinuousLinearMap subtraction and addition into a scalar equation
rw [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply] at h

-- first summand: p ↦ 4*x^2 - 4*x
have h1 :
  (fderiv ℝ (fun p => 4 * p.1 ^ 2 - 4 * p.1) ((1:ℝ),(-5:ℝ))) (x - 1, y - (-5))
  = (x - 1) * 4 := by
  -- reduce to one‐variable derivative via fst-composition
  have : (fun p : ℝ×ℝ => 4 * p.1 ^ 2 - 4 * p.1) =
             (fun x => 4 * x ^ 2 - 4 * x) ∘ Prod.fst := rfl
  rw [this, fderiv_comp, fderiv_fst, ← deriv_fderiv]
  -- compute the 1D derivative of 4*x^2 - 4*x at x=1
  nth_rewrite 1 [deriv_sub]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  -- now simplify the continuous linear map application
  rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst']
  norm_num
  field_simp
  -- all the differentiability proofs
  repeat
    first |
      exact differentiableAt_const _ |
      exact differentiableAt_id |
      exact differentiableAt_pow _ |
      exact differentiableAt_fst |
      apply DifferentiableAt.mul |
      apply DifferentiableAt.sub |
      apply DifferentiableAt.add

-- second summand: p ↦ p.2^4 - 2*p.2^3 - 2*p.2^2 - 2*p.2
have h2 :
  (fderiv ℝ (fun p => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) ((1:ℝ),(-5:ℝ))) (x - 1, y - (-5))
  = (y - (-5)) * (-632) := by
  -- reduce to one‐variable derivative via snd-composition
  have : (fun p : ℝ×ℝ => p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2) =
             (fun y => y ^ 4 - 2 * y ^ 3 - 2 * y ^ 2 - 2 * y) ∘ Prod.snd := rfl
  rw [this, fderiv_comp, fderiv_snd, ← deriv_fderiv]
  -- compute the 1D derivative at y = -5
  nth_rewrite 1 [deriv_sub]
  nth_rewrite 1 [deriv_add]  -- one of the terms is + (− 2*y^2)
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  -- simplify the application
  rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_snd']
  norm_num
  field_simp
  -- differentiability
  repeat
    first |
      exact differentiableAt_const _ |
      exact differentiableAt_id |
      exact differentiableAt_pow _ |
      exact differentiableAt_snd |
      apply DifferentiableAt.mul |
      apply DifferentiableAt.add |
      apply DifferentiableAt.sub

-- the constant part
have h3 :
  fderiv ℝ (fun p : ℝ×ℝ => c) ((1:ℝ),(-5:ℝ)) (x - 1, y - (-5)) = 0 := by
  rw [fderiv_const]; field_simp

-- put everything back into `h` and finish by linear arithmetic
rw [h1, h2, h3] at h
ring_nf at h
linarith

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
  -- remove the constant term
  rw [fderiv_sub] at h

  -- split the fderiv of a sum into sum of fderiv
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 5 * p.1 ^ 3) ((-4), (-3)))
    (hp2 : DifferentiableAt ℝ (fun p => -2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) ((-4), (-3))) :
    fderiv ℝ (fun p : ℝ × ℝ =>
      5 * p.1 ^ 3
        - 2 * p.2 ^ 3
        + 5 * p.2 ^ 2
        + 2 * p.2)
      ((-4), (-3))
      =
      fderiv ℝ (fun p => 5 * p.1 ^ 3) ((-4), (-3))
        + fderiv ℝ (fun p => -2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) ((-4), (-3)) := by
    -- fderiv of f + g is fderiv f + fderiv g
    rw [← fderiv_add]
    exact hp1
    exact hp2

  -- rewrite the main equation using this split
  rw [h_split] at h
  -- turn the continuous linear map sum into two applies
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- compute the fderiv of p ↦ 5 * p.1 ^ 3
  have h1 :
      (fderiv ℝ (fun p => 5 * p.1 ^ 3) ((-4), (-3))) (x + 4, y + 3)
      = (x + 4) * 240 := by
    -- view as composition with fst
    have eq₁ : (fun p : ℝ × ℝ => 5 * p.1 ^ 3) = (fun u => 5 * u ^ 3) ∘ Prod.fst := rfl
    rw [eq₁, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- do the 1D derivative
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- finish the CLM computation
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- side-goals: differentiability
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact differentiableAt_id
      try exact differentiableAt_fst

  -- compute the fderiv of p ↦ -2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2
  have h2 :
      (fderiv ℝ (fun p => -2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2) ((-4), (-3))) (x + 4, y + 3)
      = (y + 3) * (-82) := by
    -- view as composition with snd
    have eq₂ :
        (fun p : ℝ × ℝ => -2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2)
      = (fun u => -2 * u ^ 3 + 5 * u ^ 2 + 2 * u) ∘ Prod.snd := rfl
    rw [eq₂, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- do the 1D derivative in three steps
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- now the two pieces of the first sum
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- finish the CLM computation
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    -- side-goals: differentiability
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact differentiableAt_id
      try exact differentiableAt_snd

  -- the constant term has zero fderiv
  have h3 :
      fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-4), (-3)) (x + 4, y + 3) = 0 := by
    rw [fderiv_const]; field_simp

  -- substitute back into the main equation and conclude
  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

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
  -- expand the definition of fderiv of a subtraction
  simp only [fderiv_sub] at h
  -- split it into “fderiv of the p.1–part” + “fderiv of the p.2–part”
  simp only [fderiv_add, fderiv_comp, fderiv_fst, fderiv_snd,
    deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id''] at h
  -- simplify all the linear‐map applications
  simp only [sub_eq_add_neg,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
             ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h
  -- evaluate all the numeric constants 20*2^3+3*2^2+8*2+2 = 190, 6*(-3)^2 - 6*(-3) = 72
  norm_num at h
  -- now we're exactly (x-2)*190 + (y+3)*72 = 0
  exact h

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3 - c) ((-4:ℝ), (0:ℝ)) (x-(-4), y-0) = 0) → ((x-(-4)) * (-914) - (y-0) * (0) = 0) := by
  intro h
  -- split off the `- c` and the `- 3 * p.2 ^ 3` parts
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4 : ℝ), (0 : ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3)           ((-4 : ℝ), (0 : ℝ))) :
    fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3)
      ((-4 : ℝ), (0 : ℝ))
    = fderiv ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4 : ℝ), (0 : ℝ))
      - fderiv ℝ (fun p => 3 * p.2 ^ 3)           ((-4 : ℝ), (0 : ℝ)) := by
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    exact hp1
    exact hp2
  rw [h_split] at h
  -- turn the subtraction of CLMs into `-` on their values
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h
  -- now compute the two directional derivatives
  have h1 :
    (fderiv ℝ (fun p => 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1) ((-4 : ℝ), (0 : ℝ)))
      (x - (-4), y - 0) = (x - (-4)) * (-914) := by
    -- view it as a function of one variable composed with `fst`
    have : (fun p : ℝ×ℝ => 3 * p.1^4 - 3 * p.1^3 - 2 * p.1)
             = (fun t => 3 * t^4 - 3 * t^3 - 2 * t) ∘ fun p => p.1 := rfl
    rw [this, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- now the one‐dimensional derivative
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- apply the CLM evaluations
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    -- discharge differentiability obligations
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      <|> try exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
      <|> try exact differentiableAt_fst
  have h2 :
    (fderiv ℝ (fun p => 3 * p.2 ^ 3) ((-4 : ℝ), (0 : ℝ)))
      (x - (-4), y - 0) = (y - 0) * (0) := by
    have : (fun p : ℝ×ℝ => 3 * p.2 ^ 3)
             = (fun t => 3 * t^3) ∘ fun p => p.2 := rfl
    rw [this, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      <|> try exact differentiableAt_snd
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-4 : ℝ), (0 : ℝ)) (x - (-4), y - 0) = 0 := by
    rw [fderiv_const]; field_simp
  -- plug everything back into `h` and finish
  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith
  -- final differentiability witnesses
  all_goals
    try exact differentiableAt_const _
    <|> try exact differentiableAt_fst
    <|> try exact differentiableAt_snd
    <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_fst.pow _)
    <|> try exact differentiableAt_pow _

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + p.2 ^ 2 - 4 * p.2 - c) ((-6:ℝ), (0:ℝ)) (x-(-6), y-0) = 0) → ((x-(-6)) * (236) - (y-0) * (4) = 0) := by
  intro h
  -- split off the p.1‐part and the p.2‐part
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6 : ℝ), (0 : ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6 : ℝ), (0 : ℝ))) :
    fderiv ℝ
      (fun p : ℝ × ℝ =>
        2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1
      - (2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2))
      ((-6 : ℝ), (0 : ℝ))
    = fderiv ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6 : ℝ), (0 : ℝ))
      - fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6 : ℝ), (0 : ℝ)) := by
    rw [← fderiv_sub]
    congr
    ext p; ring
    exact hp1
    exact hp2
  -- apply that splitting
  rw [h_split] at h
  simp only [ContinuousLinearMap.sub_apply] at h

  -- compute the derivative in the first coordinate
  have h1 : 
    (fderiv ℝ (fun p => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1) ((-6 : ℝ), (0 : ℝ)))
      (x - (-6), y - 0)
    = (x - (-6)) * 236 := by
    -- express as a composition with fst
    have comp₁ :
      (fun p : ℝ × ℝ => 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1)
      = (fun x => 2 * x ^ 3 - 2 * x ^ 2 - 4 * x) ∘ prod.fst := rfl
    rw [comp₁, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- do the one‐variable derivation d/dx (2 x^3 - 2 x^2 - 4 x) at x = -6
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- now simplify the continuous‐linear‐map application
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
               ContinuousLinearMap.coe_fst']
    -- the numerical value of the derivative
    norm_num
    -- housekeeping differentiability proofs
    all_goals
      try infer_instance

  -- compute the derivative in the second coordinate
  have h2 :
    (fderiv ℝ (fun p => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2) ((-6 : ℝ), (0 : ℝ)))
      (x - (-6), y - 0)
    = (y - 0) * 4 := by
    -- compose with snd
    have comp₂ :
      (fun p : ℝ × ℝ => 2 * p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + 4 * p.2)
      = (fun y => 2 * y ^ 4 + 5 * y ^ 3 - y ^ 2 + 4 * y) ∘ prod.snd := rfl
    rw [comp₂, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- d/dy (2 y^4 + 5 y^3 - y^2 + 4 y) at y = 0
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
               ContinuousLinearMap.coe_snd']
    norm_num
    all_goals
      try infer_instance

  -- the c-term has zero derivative
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-6 : ℝ), (0 : ℝ)) (x - (-6), y - 0) = 0 := by
    rw [fderiv_const]; infer_instance

  -- finish
  rw [h1, h2, h3] at h
  ring_nf at h
  exact h

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
  -- split off the “- c” term
  rw [fderiv_sub] at h
  -- split the ℝ²‐derivative of the sum into the sum of derivatives
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ))) :
    fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ))
      = fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ))
        + fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ)) := by
    rw [← fderiv_add]
    congr 1
    · ext p; ring
    · assumption
    · assumption
  rw [h_split] at h
  -- turn ContinuousLinearMap subtraction/addition into pointwise subtraction/addition
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h
  -- compute the first summand (depends only on p.1)
  have h1 :
    fderiv ℝ (fun p => 5 * p.1 ^ 2 - 5 * p.1) ((-3:ℝ), (3:ℝ)) (x - -3, y - 3)
      = (x - -3) * (-35) := by
    -- factor through fst : ℝ² → ℝ
    have : (fun p : ℝ×ℝ => 5*p.1^2 - 5*p.1) =
      (fun t : ℝ => 5*t^2 - 5*t) ∘ fun p => p.1 := rfl
    rw [this, fderiv_comp, fderiv_fst, ←deriv_fderiv]
    -- now compute deriv (5*t^2 - 5*t)
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish the linear‐map calculation
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- differentiability side‐goals
    all_goals
      try apply differentiableAt_const <|> apply differentiableAt_pow <|>
          apply differentiableAt_id <|> apply differentiableAt_fst <|>
          apply DifferentiableAt.mul
  -- compute the second summand (depends only on p.2)
  have h2 :
    fderiv ℝ (fun p => 4 * p.2 ^ 3 - 4 * p.2) ((-3:ℝ), (3:ℝ)) (x - -3, y - 3)
      = (y - 3) * 104 := by
    have : (fun p : ℝ×ℝ => 4*p.2^3 - 4*p.2) =
      (fun t : ℝ => 4*t^3 - 4*t) ∘ fun p => p.2 := rfl
    rw [this, fderiv_comp, fderiv_snd, ←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    all_goals
      try apply differentiableAt_const <|> apply differentiableAt_pow <|>
          apply differentiableAt_id <|> apply differentiableAt_snd <|>
          apply DifferentiableAt.mul
  -- the constant c‐term contributes 0
  have h3 :
    fderiv ℝ (fun p : ℝ×ℝ => (c : ℝ)) ((-3:ℝ),(3:ℝ)) (x - -3, y - 3) = 0 := by
    rw [fderiv_const]; field_simp
  -- combine and finish
  rw [h1, h2, h3] at h
  ring_nf at h
  linarith

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

  -- first subtract off the constant `c`
  rw [fderiv_sub] at h

  -- split the sum 4 * p.1^3 - 3*p.1^2 - 5*p.1 + p.2^2
  have h_split
    (h1 : DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6),(-4)))
    (h2 : DifferentiableAt ℝ (fun p => p.2 ^ 2)              ((-6),(-4))) :
    fderiv ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2)
      ((-6),(-4)) =
    fderiv ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6),(-4)) +
    fderiv ℝ (fun p => p.2 ^ 2)                             ((-6),(-4)) := by
    rw [← fderiv_add]
    exact h1
    exact h2
  rw [h_split] at h

  -- apply the definition of addition of CLMs
  rw [add_apply] at h

  -- compute the first partial:
  have Hf : (fderiv ℝ (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) ((-6),(-4)))
               (x - (-6), y - (-4)) = (x - (-6)) * 463 := by
    -- factor through the first projection
    have comp : (fun p => 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1) =
                (fun t => 4 * t ^ 3 - 3 * t ^ 2 - 5 * t) ∘ fun p => p.1 := rfl
    rw [comp, fderiv_comp, fderiv_fst, ← deriv_fderiv]

    -- now do the 1d derivative 4*t^3 - 3*t^2 - 5*t at t = -6
    --     d/dt (4 t^3) = 12 t^2
    --     d/dt (-3 t^2) = -6 t
    --     d/dt (-5 t)   = -5
    have : deriv (fun t => 4 * t^3 - 3 * t^2 - 5 * t) (-6)
         = 12 * (-6) ^ 2 + (-6) * (-6) + -5 := by
      simp [deriv_pow, deriv_mul, deriv_const, deriv_id] <;> norm_num
    nth_rewrite 1 this

    -- finish the chain rule
    simp [comp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, coe_fst']
    norm_num
    -- prove the differentiability hypotheses
    all_goals
      try exact (differentiableAt_const _ : _)
      <|> try exact (differentiableAt_pow _ : _)
      <|> try exact (differentiableAt_id : _)
      <|> try exact differentiableAt_fst

  -- compute the second partial:
  have Hg : (fderiv ℝ (fun p => p.2 ^ 2) ((-6),(-4))) (x - (-6), y - (-4)) = (y - (-4)) * (-8) := by
    have comp' : (fun p => p.2 ^ 2) = (fun t => t ^ 2) ∘ fun p => p.2 := rfl
    rw [comp', fderiv_comp, fderiv_snd, ← deriv_fderiv]
    have : deriv (fun t => t ^ 2) (-4) = 2 * (-4) := by simp [deriv_pow, deriv_id]
    nth_rewrite 1 this
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, coe_snd']
    norm_num
    all_goals
      try exact (differentiableAt_id : _)
      <|> try exact (differentiableAt_pow _ : _)
      <|> try exact differentiableAt_snd

  -- the constant part is zero
  have Hc : fderiv ℝ (fun _ : ℝ×ℝ => (c : ℝ)) ((-6),(-4)) (x - (-6), y - (-4)) = 0 := by
    simp [fderiv_const]

  -- rewrite all three into the main equation
  rw [Hf, Hg, Hc] at h

  -- combine and finish
  ring_nf at h
  linarith

  -- provide the differentiability proofs for the split
  all_goals
    try exact differentiableAt_fst.pow _
    <|> try exact differentiableAt_pow _
    <|> try exact (differentiableAt_const _ : _)
    <|> try exact differentiableAt_snd

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
  -- remove the “- c” term
  rw [fderiv_sub] at h
  -- split into the p.1‐part and the p.2‐part
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) (6, 3))
    (hp2 : DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) (6, 3)) :
    fderiv ℝ (fun p : ℝ × ℝ =>
      4 * p.1 ^ 4 - 4 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2)
      (6, 3)
    = fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) (6, 3)
      + fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) (6, 3) := by
    -- use fderiv_add to split the sum
    rw [← fderiv_add]
    exact hp1
    exact hp2
  rw [h_split] at h
  -- turn it into two linear‐map applications
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- compute the p.1‐part derivative at 6
  have h1 :
    (fderiv ℝ (fun p => 4 * p.1 ^ 4 - 4 * p.1 ^ 2) (6, 3)) (x - 6, y - 3)
    = (x - 6) * 3408 := by
    -- view it as (fun p => (4*x^4 - 4*x^2) ∘ p.1)
    have comp : (fun p : ℝ × ℝ => 4 * p.1 ^ 4 - 4 * p.1 ^ 2)
      = fun q => (4 * q ^ 4 - 4 * q ^ 2) ∘ fun p => p.1 := rfl
    rw [comp]
    -- apply the chain rule
    rw [fderiv_comp, fderiv_fst]
    rw [← deriv_fderiv]
    -- rewrite the one‐variable derivative of 4*x^4 - 4*x^2
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish the linear‐map appl and numeric simplification
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst']
    field_simp
    norm_num
    -- side‐conditions: differentiability at the point
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_id
    exact differentiableAt_id

  -- compute the p.2‐part derivative at 3
  have h2 :
    (fderiv ℝ (fun p =>
      p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2) (6, 3)) (x - 6, y - 3)
    = (y - 3) * 168 := by
    have comp2 : (fun p : ℝ × ℝ => p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2)
      = fun q => (q ^ 4 + 3 * q ^ 3 - 3 * q ^ 2 - 3 * q) ∘ fun p => p.2 := rfl
    rw [comp2]
    rw [fderiv_comp, fderiv_snd]
    rw [← deriv_fderiv]
    -- rewrite the derivative of q^4 + 3 q^3 - 3 q^2 - 3 q
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd']
    field_simp
    norm_num
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_snd

  -- the c‐term contributes zero
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) (6, 3) (x - 6, y - 3) = 0 := by
    rw [fderiv_const]; field_simp

  -- assemble and finish
  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

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
  -- split the fderiv of a subtraction into a difference of fderivs
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 2 * p.1 ^ 2 + p.1) ((-4:ℝ),(-3:ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 3 * p.2) ((-4:ℝ),(-3:ℝ))) :
    fderiv ℝ (fun p => 2*p.1^2 + p.1 - 3*p.2) ((-4:ℝ),(-3:ℝ))
      = fderiv ℝ (fun p => 2*p.1^2 + p.1) ((-4:ℝ),(-3:ℝ))
        - fderiv ℝ (fun p => 3*p.2) ((-4:ℝ),(-3:ℝ)) := by
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    exact hp1
    exact hp2
  rw [h_split] at h
  -- now expand the two fderivs
  repeat (rw [ContinuousLinearMap.sub_apply] at h)
  -- first component: fderiv of 2*x^2 + x via fst
  have h1 :
    (fderiv ℝ (fun p => 2*p.1^2 + p.1) ((-4:ℝ),(-3:ℝ))) (x - (-4), y - (-3))
    = (x - (-4)) * (-15) := by
    -- rewrite as a composition with fst
    have comp1 : (fun p : ℝ × ℝ => 2*p.1^2 + p.1)
      = (fun u => 2*u^2 + u) ∘ (fun p => p.1) := rfl
    rw [comp1, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- compute the one-variable derivative of 2*u^2 + u at u = -4
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- now apply the linear maps
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- side‐goals: differentiability
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
                              (differentiableAt_id)
    exact differentiableAt_fst
  -- second component: fderiv of 3*y via snd
  have h2 :
    (fderiv ℝ (fun p => 3*p.2) ((-4:ℝ),(-3:ℝ))) (x - (-4), y - (-3))
    = (y - (-3)) * 3 := by
    have comp2 : (fun p : ℝ × ℝ => 3*p.2)
      = (fun u => 3*u) ∘ (fun p => p.2) := rfl
    rw [comp2, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_snd
  -- the constant c has zero derivative
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-4:ℝ),(-3:ℝ)) (x - (-4), y - (-3)) = 0 := by
    rw [fderiv_const]; field_simp
  -- rewrite and close
  rw [h1, h2, h3] at h
  ring_nf at h
  exact h
  -- finally discharge the differentiability side‐goals
  all_goals
    try exact differentiableAt_const _
    try exact differentiableAt_id
    try exact differentiableAt_pow _
    try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    try exact differentiableAt_fst
    try exact differentiableAt_snd

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

  -- remove the constant `- c`
  rw [fderiv_sub] at h

  -- split the sum `3 p.1^2 + 3 p.1 + p.2^4 + p.2`
  have hsum :
    fderiv ℝ (fun p : ℝ×ℝ => 3*p.1^2 + 3*p.1 + p.2^4 + p.2) (2,0)
    = fderiv ℝ (fun p => 3*p.1^2 + 3*p.1) (2,0)
      + fderiv ℝ (fun p => p.2^4 + p.2) (2,0) := by
    rw [← fderiv_add]
    exact (differentiableAt_pow.add differentiableAt_id : _)
  rw [hsum, ContinuousLinearMap.add_apply] at h

  -- first coordinate: derivative of `u ↦ 3 u^2 + 3 u` at 2 is `6*2 + 3 = 15`
  have h1 :
    fderiv ℝ (fun p => 3*p.1^2 + 3*p.1) (2,0) (x-2, y-0) = (x-2) * 15 := by
    -- factor through `fst`
    have e1 : (fun p : ℝ×ℝ => 3*p.1^2 + 3*p.1) = (fun u => 3*u^2 + 3*u) ∘ Prod.fst := rfl
    rw [e1, fderiv_comp, fderiv_fst, ← deriv_fderiv, deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]
    -- supply the differentiability proofs
    repeat'
      apply differentiableAt_id <|>
      apply differentiableAt_const <|>
      apply differentiableAt_pow
    -- clean up the `ContinuousLinearMap` applications
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']

  -- second coordinate: derivative of `u ↦ u^4 + u` at 0 is `0^3*4 + 1 = 1`
  have h2 :
    fderiv ℝ (fun p => p.2^4 + p.2) (2,0) (x-2, y-0) = (y-0) * 1 := by
    have e2 : (fun p : ℝ×ℝ => p.2^4 + p.2) = (fun u => u^4 + u) ∘ Prod.snd := rfl
    rw [e2, fderiv_comp, fderiv_snd, ← deriv_fderiv, deriv_add, deriv_pow, deriv_add, deriv_id]
    repeat'
      apply differentiableAt_id <|>
      apply differentiableAt_pow
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']

  -- constant part is zero
  have h3 :
    fderiv ℝ (fun _ => c) (2,0) (x-2, y-0) = 0 := by
    simpa using fderiv_const

  -- rewrite all three into `h` and finish
  simp [h1, h2, h3] at h
  exact h

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
  -- subtract off the “– c”
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ))) :
    fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 ^ 3 - p.2 ^ 3) ((-2:ℝ), (-2:ℝ)) =
      fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ)) -
      fderiv ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ)) := by
    rw [←fderiv_sub]
    congr 1
    · ext p; ring
    · exact hp1
    · exact hp2
  rw [h_split] at h
  -- apply both continuous‐linear‐map subtractions
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply] at h

  -- derivative of 4 * p.1 ^ 3
  have h1 :
    (fderiv ℝ (fun p => 4 * p.1 ^ 3) ((-2:ℝ), (-2:ℝ))) (x - (-2), y - (-2)) =
      (x - (-2)) * 48 := by
    -- factor as (λ x, 4*x^3) ∘ fst
    have comp1 : (fun p : ℝ × ℝ => 4 * p.1 ^ 3) = (fun x => 4 * x ^ 3) ∘ fun p => p.1 := rfl
    rw [comp1, fderiv_comp, fderiv_fst, ←deriv_fderiv]
    -- now do the one‐variable deriv
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- back to fderiv
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- discharge differentiability
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      <|> exact differentiableAt_fst

  -- derivative of p.2 ^ 3
  have h2 :
    (fderiv ℝ (fun p => p.2 ^ 3) ((-2:ℝ), (-2:ℝ))) (x - (-2), y - (-2)) =
      (y - (-2)) * 12 := by
    have comp2 : (fun p : ℝ × ℝ => p.2 ^ 3) = (fun y => y ^ 3) ∘ fun p => p.2 := rfl
    rw [comp2, fderiv_comp, fderiv_snd, ←deriv_fderiv]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    all_goals
      try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> exact differentiableAt_snd

  -- derivative of constant c
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-2:ℝ), (-2:ℝ)) (x - (-2), y - (-2)) = 0 := by
    rw [fderiv_const]; field_simp

  -- plug them back in
  rw [h1, h2, h3] at h
  ring_nf at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3 - c) ((4:ℝ), (3:ℝ)) (x-4, y-3) = 0) → ((x-4) * (133) - (y-3) * (54) = 0) := by
intro h
-- split fderiv of (f - g) into fderiv f - fderiv g
rw [fderiv_sub] at h
have h_split
  (hp1 : DifferentiableAt ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ)))
  (hp2 : DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ))) :
  fderiv ℝ (fun p : ℝ×ℝ => 
      p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3)
    ((4:ℝ), (3:ℝ))
  = fderiv ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ))
    - fderiv ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ)) := by
  rw [← fderiv_sub]
  ext p; ring
  exact hp1; exact hp2
rw [h_split] at h
-- apply the two linear maps to (x-4, y-3)
rw [ContinuousLinearMap.sub_apply] at h
rw [ContinuousLinearMap.sub_apply] at h

-- compute the x-part: derivative in the first coordinate at 4
have h1 :
  (fderiv ℝ (fun p => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1) ((4:ℝ), (3:ℝ)))
    (x - 4, y - 3)
  = (x - 4) * 133 := by
  have comp₁ : (fun p : ℝ×ℝ => p.1 ^ 4 - 2*p.1^3 -4*p.1^2 + 5*p.1)
            = (fun u => u^4 - 2*u^3 - 4*u^2 + 5*u) ∘ Prod.fst := rfl
  rw [comp₁, fderiv_comp, fderiv_fst, ← deriv_fderiv]
  -- rewrite the one-variable derivative
  nth_rewrite 1 [deriv_sub]
  nth_rewrite 1 [deriv_sub]
  nth_rewrite 1 [deriv_add]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 2 [deriv_mul]  -- the `5*u` term
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
  field_simp; norm_num
  -- side-conditions for fderiv_comp, deriv_fderiv,...
  · exact differentiableAt_fst.pow 4
  · exact hp1
  · exact (differentiableAt_pow _).mul (differentiableAt_const _)

-- compute the y-part: derivative in the second coordinate at 3
have h2 :
  (fderiv ℝ (fun p => 2 * p.2 ^ 3) ((4:ℝ), (3:ℝ))) (x - 4, y - 3)
  = (y - 3) * 54 := by
  have comp₂ : (fun p : ℝ×ℝ => 2 * p.2 ^ 3) = (fun u => 2*u^3) ∘ Prod.snd := rfl
  rw [comp₂, fderiv_comp, fderiv_snd, ← deriv_fderiv]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
  field_simp; norm_num
  · exact differentiableAt_snd.pow 3
  · exact (differentiableAt_const _).mul differentiableAt_snd

-- the constant c contributes zero
have h3 :
  fderiv ℝ (fun (_ : ℝ×ℝ) => c) ((4:ℝ), (3:ℝ)) (x - 4, y - 3) = 0 := by
  rw [fderiv_const]; field_simp

-- plug back into the hypothesis and finish
rw [h1, h2, h3] at h
ring_nf at h
linarith

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
  -- 1) show the derivative at (6,-5) really is the expected 2×2 linear map
  have deriv_eq :
    fderiv ℝ (fun p => 
        3*p.1^3 + 3*p.1^2 - 5*p.1
      - 2*p.2^4 +     p.2^3 - 2*p.2^2 - 5*p.2
      - c)
    (6, -5)
    = 
    ContinuousLinearMap.mk _
      (fun v : ℝ × ℝ => v.1 * 355 + v.2 * (-1090)) := by
    ext ⟨u, v⟩
    -- now reduce the LHS which is the Fréchet‐derivative applied to (u,v)
    -- into the closed‐form multilinear function `u*355 + v*(-1090)`
    dsimp [fderiv, deriv];                                   
    simp only [Prod.mk.eta]; -- make the pair explicit
    -- unfold all the `deriv_*` lemmas for powers, mul, add, sub, const, id
    simp only [deriv_pow'',
               deriv_id'',
               deriv_mul,
               deriv_const,
               deriv_add,
               deriv_sub]
      at *
    -- now clean up
    ring

  -- 2) apply both sides of `deriv_eq` to `(x-6, y+5)`, rewrite with `h` and finish
  have : (ContinuousLinearMap.mk _ (fun v => v.1 * 355 + v.2 * (-1090))) (x - 6, y + 5) = 0 := by
    simpa [deriv_eq] using h
  simpa using this

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
  -- get rid of the “- c”
  rw [fderiv_sub] at h

  -- split into fderiv of (2*p.1) minus fderiv of (2*p.2^2 - p.2)
  have hsplit
    (hp1 : DifferentiableAt ℝ (fun p => 2 * p.1) ((4:ℝ),(-1:ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ),(-1:ℝ))) :
    fderiv ℝ (fun p => 2 * p.1 - (2 * p.2 ^ 2 - p.2)) ((4:ℝ),(-1:ℝ)) =
      fderiv ℝ (fun p => 2 * p.1) ((4:ℝ),(-1:ℝ)) -
      fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ),(-1:ℝ)) := by
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    exact hp1
    exact hp2

  -- apply that to our h
  rw [hsplit] at h
  -- now the subtraction is on continuous linear maps
  rw [ContinuousLinearMap.sub_apply] at h
  -- and again when we apply to the vector
  rw [ContinuousLinearMap.sub_apply] at h

  -- compute the first term: fderiv of (2 * p.1)
  have h1 :
    (fderiv ℝ (fun p => 2 * p.1) ((4:ℝ),(-1:ℝ))) (x - 4, y - (-1)) =
      (x - 4) * 2 := by
    -- write 2*p.1 as (fun x => 2*x) ∘ fst
    have : (fun p : ℝ × ℝ => 2 * p.1) =
             (fun x => 2 * x) ∘ (fun p => p.1) := rfl
    rw [this]
    -- chain rule: fderiv (g ∘ fst) = fderiv g ∘ fderiv fst
    rw [fderiv_comp, fderiv_fst]
    -- switch to 1D derivative
    rw [← deriv_fderiv]
    -- compute deriv of fun x => 2*x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- now apply the resulting linear maps
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst']
    -- clean up
    field_simp; norm_num

  -- compute the second term: fderiv of (2*p.2^2 - p.2)
  have h2 :
    (fderiv ℝ (fun p => 2 * p.2 ^ 2 - p.2) ((4:ℝ),(-1:ℝ))) (x - 4, y - (-1)) =
      (y - (-1)) * (-5) := by
    -- write it as (fun x => 2*x^2 - x) ∘ snd
    have : (fun p : ℝ × ℝ => 2 * p.2 ^ 2 - p.2) =
             (fun x => 2 * x ^ 2 - x) ∘ (fun p => p.2) := rfl
    rw [this]
    rw [fderiv_comp, fderiv_snd]
    rw [← deriv_fderiv]
    -- break down the 1D deriv
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- apply the resulting map
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd']
    -- simplify the numbers
    field_simp; norm_num

  -- there is no more “- c” term, its derivative is zero.
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => c) ((4:ℝ),(-1:ℝ)) (x - 4, y - (-1)) = 0 := by
    rw [fderiv_const]; field_simp

  -- plug h1, h2, h3 into h, normalize and finish
  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  -- now discharge the differentiability proof obligations
  all_goals
    repeat
      first
      | exact differentiableAt_const _
      | exact differentiableAt_id
      | exact differentiableAt_fst
      | exact differentiableAt_snd
      | exact differentiableAt_pow _

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

  -- split off the “- c”
  rw [fderiv_sub] at h

  -- split the sum of the x‐part and the y‐part
  have h_sum
    (h₁ : DifferentiableAt ℝ (fun p => 2*p.1^3 + 3*p.1^2 - 5*p.1) (0,4))
    (h₂ : DifferentiableAt ℝ (fun p => 5*p.2^4 - 4*p.2^3 - 3*p.2^2 + 5*p.2) (0,4)) :
    fderiv ℝ (fun p : ℝ×ℝ => 2*p.1^3 + 3*p.1^2 - 5*p.1
                         + 5*p.2^4 - 4*p.2^3 - 3*p.2^2 + 5*p.2)
      (0,4)
    =
    fderiv ℝ (fun p => 2*p.1^3 + 3*p.1^2 - 5*p.1) (0,4)
    + fderiv ℝ (fun p => 5*p.2^4 - 4*p.2^3 - 3*p.2^2 + 5*p.2) (0,4) := by
    rw [←fderiv_add]; exact h₁; exact h₂

  -- put that back into h, and unfold the two linear‐map applications
  rw [h_sum] at h
  simp only [add_apply, sub_apply] at h

  -- the x‐part: 2*x^3 + 3*x^2 - 5*x
  have h1 : (fderiv ℝ (fun p => 2*p.1^3 + 3*p.1^2 - 5*p.1) (0,4)) (x-0, y-4)
          = (x-0) * (-5) := by
    have : (fun p : ℝ×ℝ => 2*p.1^3 + 3*p.1^2 - 5*p.1)
         = (fun u => 2*u^3 + 3*u^2 - 5*u) ∘ Prod.fst := rfl
    rw [this, fderiv_comp, fderiv_fst, ←deriv_fderiv]
    -- now unfold the one‐variable derivative
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- now finish the linear‐map evaluation
    simp [comp_apply, smulRight_apply, coe_fst']
    field_simp; norm_num
    all_goals
      try aesop (arb := obviously)  -- all the differentiability proofs

  -- the y‐part: 5*y^4 - 4*y^3 - 3*y^2 + 5*y
  have h2 : (fderiv ℝ (fun p => 5*p.2^4 - 4*p.2^3 - 3*p.2^2 + 5*p.2) (0,4)) (x-0, y-4)
          = (y-4) * 1069 := by
    have : (fun p : ℝ×ℝ => 5*p.2^4 - 4*p.2^3 - 3*p.2^2 + 5*p.2)
         = (fun u => 5*u^4 - 4*u^3 - 3*u^2 + 5*u) ∘ Prod.snd := rfl
    rw [this, fderiv_comp, fderiv_snd, ←deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    simp [comp_apply, smulRight_apply, coe_snd']
    field_simp; norm_num
    all_goals
      try aesop (arb := obviously)

  -- the constant c‐part
  have h3 : fderiv ℝ (fun _ => c) (0,4) (x-0, y-4) = 0 := by
    rw [fderiv_const]; simp

  -- substitute everything back into h, clear denominators, finish
  simp [h1, h2, h3] at h
  ring_nf at h
  linarith

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
  -- remove the “- c” piece
  rw [fderiv_sub, fderiv_const, sub_zero] at h

  -- now fderiv of the sum splits into two addends
  have hsum : (fderiv ℝ (fun p => p.1^4 + 5*p.1^3 + p.1^2 + 5*p.1) (3,3)
              + fderiv ℝ (fun p => p.2^4 - p.2^3 - p.2^2) (3,3))
             (x-3, y-3) = 0 := by
    simpa only [ContinuousLinearMap.add_apply] using h

  -- compute the first piece (the p.1‐part)
  have h1 : (fderiv ℝ (fun p => p.1^4 + 5*p.1^3 + p.1^2 + 5*p.1) (3,3))
             (x-3, y-3) = (x-3)*254 := by
    -- view it as a one‐variable function postcomposed with fst
    have : (fun p : ℝ×ℝ => p.1^4 + 5*p.1^3 + p.1^2 + 5*p.1)
           = (fun u => u^4 + 5*u^3 + u^2 + 5*u) ∘ Prod.fst := rfl
    rw [this, fderiv_comp, fderiv_fst]
    -- turn fderiv ℝ (fun u => …) into deriv at u=3
    rw [←deriv_fderiv]
    -- now perform the one‐variable differentiation
    conv => 
      lhs 
      simp only [deriv_add, deriv_mul, deriv_pow'',
        deriv_const, deriv_id'']
    -- plug back into the continuous linear map and simplify
    simp [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.coe_fst'] at *
    norm_num

  -- compute the second piece (the p.2‐part)
  have h2 : (fderiv ℝ (fun p => p.2^4 - p.2^3 - p.2^2) (3,3))
             (x-3, y-3) = (y-3)*75 := by
    have : (fun p : ℝ×ℝ => p.2^4 - p.2^3 - p.2^2)
           = (fun u => u^4 - u^3 - u^2) ∘ Prod.snd := rfl
    rw [this, fderiv_comp, fderiv_snd]
    rw [←deriv_fderiv]
    conv => 
      lhs 
      simp only [deriv_add, deriv_sub, deriv_mul,
        deriv_pow'', deriv_const, deriv_id'']
    simp [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.coe_snd'] at *
    norm_num

  -- put the two pieces back into the sum
  simp [hsum, h1, h2]
  -- a little arithmetic finishes
  linarith

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
-- split off the “– 4 * p.2^4” part
rw [fderiv_sub] at h
have h_split
  (hp1 : DifferentiableAt ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (3, 3))
  (hp2 : DifferentiableAt ℝ (fun p => 4 * p.2 ^ 4) (3, 3)) :
    fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4) (3, 3)
      = fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (3, 3)
        - fderiv ℝ (fun p => 4 * p.2 ^ 4) (3, 3) := by
  rw [← fderiv_sub]
  congr
  ext p; ring
  exact hp1
  exact hp2
rw [h_split] at h
-- apply the two linear maps to (x-3, y-3)
rw [ContinuousLinearMap.sub_apply] at h
rw [ContinuousLinearMap.sub_apply] at h

-- 1) the p.1-part: p ↦ p.1^3 - 4*p.1^2 + p.1
have h1 :
  fderiv ℝ (fun p => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1) (3, 3) (x - 3, y - 3) = (x - 3) * 4 := by
  -- rewrite as a composition with fst
  have E : (fun p : ℝ×ℝ => p.1 ^ 3 - 4 * p.1 ^ 2 + p.1)
         = (fun x => x ^ 3 - 4 * x ^ 2 + x) ∘ Prod.fst := rfl
  rw [E, fderiv_comp, fderiv_fst, ← deriv_fderiv]
  -- now differentiate x^3 - 4 x^2 + x at x = 3
  nth_rewrite 1 [deriv_sub]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
  field_simp; norm_num
  -- side‐conditions for differentiability
  all_goals
    try exact differentiableAt_id
    <|> try exact differentiableAt_const _
    <|> try exact differentiableAt_pow _
    <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    <|> try exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    <|> exact differentiableAt_fst

-- 2) the p.2-part: p ↦ 4*p.2^4
have h2 :
  fderiv ℝ (fun p => 4 * p.2 ^ 4) (3, 3) (x - 3, y - 3) = (y - 3) * 432 := by
  have E : (fun p : ℝ×ℝ => 4 * p.2 ^ 4) = (fun x => 4 * x ^ 4) ∘ Prod.snd := rfl
  rw [E, fderiv_comp, fderiv_snd, ← deriv_fderiv]
  nth_rewrite 1 [deriv_mul]
  nth_rewrite 1 [deriv_const]
  nth_rewrite 1 [deriv_pow'']
  nth_rewrite 1 [deriv_id'']
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
  field_simp; norm_num
  all_goals
    try exact differentiableAt_const _
    <|> try exact differentiableAt_id
    <|> try exact differentiableAt_pow _
    <|> exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

-- 3) the constant part
have h3 :
  fderiv ℝ (fun p : ℝ×ℝ => c) (3, 3) (x - 3, y - 3) = 0 := by
  rw [fderiv_const]; field_simp

-- combine and finish
rw [h1] at h; rw [h2] at h; rw [h3] at h
ring_nf at h; linarith

-- now discharge the two differentiability assumptions for h_split
exact DifferentiableAt.sub
  (DifferentiableAt.add
    (differentiableAt_pow _)
    (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
  differentiableAt_id

exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - p.1 ^ 2 + 4 * p.2 ^ 3 + 4 * p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (426) + (y-0) * (4) = 0) := by
  intro h
  -- peel off the “- c”
  rw [fderiv_sub] at h

  -- split the remaining fderiv into the x-part + the y-part
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 4*p.1^4 - p.1^2) (3, 0))
    (hp2 : DifferentiableAt ℝ (fun p => 4*p.2^3 + 4*p.2) (3, 0)) :
    fderiv ℝ (fun p =>   4*p.1^4 - p.1^2
                     + 4*p.2^3 + 4*p.2) (3, 0)
    =  fderiv ℝ (fun p => 4*p.1^4 - p.1^2) (3, 0)
    +  fderiv ℝ (fun p => 4*p.2^3 + 4*p.2) (3, 0) := by
    rw [← fderiv_add]
    congr 1
    · ext p; ring
      exact hp1
    · ext p; ring
      exact hp2

  -- rewrite our goal
  rw [h_split] at h
  -- move the two CLM’s inside
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at h

  -- compute the x-part:  d/dx (4 x⁴ - x²) at x=3 is 16·3³ - 2·3 = 432 - 6 = 426
  have h1 :
    fderiv ℝ (fun p => 4*p.1^4 - p.1^2) (3, 0) (x - 3, y - 0) = (x - 3) * 426 := by
    -- view it as a one‐variable function composed with fst
    have : (fun p : ℝ × ℝ => 4*p.1^4 - p.1^2) = (fun u => 4*u^4 - u^2) ∘ Prod.fst := rfl
    rw [this, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- do the elementary deriv rewrites
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish up
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- all our differentiability witnesses
    all_goals
      simp [differentiableAt_const, differentiableAt_id, differentiableAt_pow,
            differentiableAt_fst, DifferentiableAt.mul, DifferentiableAt.sub]

  -- compute the y-part: d/dy (4 y³ + 4 y) at y=0 is 12·0² + 4 = 4
  have h2 :
    fderiv ℝ (fun p => 4*p.2^3 + 4*p.2) (3, 0) (x - 3, y - 0) = (y - 0) * 4 := by
    have : (fun p : ℝ × ℝ => 4*p.2^3 + 4*p.2) = (fun u => 4*u^3 + 4*u) ∘ Prod.snd := rfl
    rw [this, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    all_goals
      simp [differentiableAt_const, differentiableAt_id, differentiableAt_pow,
            differentiableAt_snd, DifferentiableAt.mul, DifferentiableAt.add]

  -- the constant c part vanishes
  have h3 : fderiv ℝ (fun _ => c) (3, 0) (x - 3, y - 0) = 0 := by
    rw [fderiv_const]; trivial

  -- substitute back into h and finish
  rw [h1, h2, h3] at h
  ring_nf at h
  exact h

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
  -- Compute the fderiv once and for all:
  have A :
    fderiv ℝ (fun p => 2*p.1 + 3*p.2 - c) ((-3:ℝ),(-3:ℝ))
    = (fun v => 2*v.1 + 3*v.2 : ℝ×ℝ →L[ℝ] ℝ) := by
    simp [fderiv_sub, fderiv_const, fderiv_add, fderiv_mul, fderiv_fst, fderiv_snd]
  -- And prove how this linear map acts on our vector:
  have B :
    (fun v : ℝ×ℝ => 2*v.1 + 3*v.2) (x - (-3), y - (-3))
    = (x - (-3)) * 2 + (y - (-3)) * 3 := rfl
  -- Now rewrite in h and finish:
  simpa [A, B] using h

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
  -- peel off the “- c”
  rw [fderiv_sub] at h

  -- split the fderiv of the sum 3*p.1^2 + (p.2^4 + 3*p.2^3 - 4*p.2)
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2) (5, -4))
    (hp2 : DifferentiableAt ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) (5, -4)) :
    fderiv ℝ (fun p : ℝ×ℝ => 3 * p.1 ^ 2 + (p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2)) (5, -4)
      = fderiv ℝ (fun p => 3 * p.1 ^ 2) (5, -4) +
        fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) (5, -4) := by
    -- fderiv of a sum splits
    rw [← fderiv_add]
    -- the two summands are the ones we named hp1 and hp2
    congr 1; ext p; ring
    exact hp1
    exact hp2

  -- apply the split to the hypothesis
  rw [h_split] at h
  -- unfold the two ContinuousLinearMap.applications
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.add_apply] at h

  -- compute the ∂/∂p.1 part = 6*p.1 at p.1 = 5  → 30
  have h1 :
    fderiv ℝ (fun p => 3 * p.1 ^ 2) (5, -4) (x - 5, y + 4) = (x - 5) * 30 := by
    -- factor through fst
    have A : (fun p : ℝ×ℝ => 3 * p.1 ^ 2) = (fun u => 3 * u ^ 2) ∘ Prod.fst := rfl
    rw [A, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- derivative of 3*u^2 is 6*u
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- now collect the linear map application
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- side‐conditions for differentiability
    all_goals
      try
        solve_by_elim <|>
        exact differentiableAt_fst <|>
        exact differentiableAt_const _ <|>
        exact differentiableAt_pow _

  -- compute the ∂/∂p.2 part = 4*p.2^3 + 9*p.2^2 - 4 at p.2 = -4 → -256 + 144 - 4 = -116
  have h2 :
    fderiv ℝ (fun p => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) (5, -4) (x - 5, y + 4) = (y + 4) * (-116) := by
    -- factor through snd
    have B : (fun p : ℝ×ℝ => p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2) = (fun u => u ^ 4 + 3 * u ^ 3 - 4 * u) ∘ Prod.snd := rfl
    rw [B, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- apply derivative laws: sum, sum, pow, id, mul, const, id
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish the linear map application
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    -- side‐conditions
    all_goals
      try
        solve_by_elim <|>
        exact differentiableAt_snd <|>
        exact differentiableAt_const _ <|>
        exact differentiableAt_pow _

  -- and the constant c part goes to zero
  have h3 :
    fderiv ℝ (fun p : ℝ×ℝ => (c : ℝ)) (5, -4) (x - 5, y + 4) = 0 := by
    rw [fderiv_const]; field_simp

  -- plug in h1,h2,h3 into h, then simplify
  rw [h1, h2, h3] at h
  ring_nf at h
  linarith

  -- finally discharge the two “DifferentiableAt” side‐goals we left open
  all_goals
    try solve_by_elim <|>
    exact differentiableAt_fst <|>
    exact differentiableAt_snd <|>
    exact differentiableAt_const _ <|>
    exact differentiableAt_pow _

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
{ intro h
  -- split the subtraction inside the fderiv
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => p.1 ^ 2) ((-1:ℝ), 0))
    (hp2 : DifferentiableAt ℝ (fun p => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), 0)) :
    fderiv ℝ (fun p => p.1 ^ 2 - (2 * p.2 ^ 3 + 3 * p.2)) ((-1:ℝ), 0)
      = fderiv ℝ (fun p => p.1 ^ 2) ((-1:ℝ), 0) -
        fderiv ℝ (fun p => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), 0) :=
  by
    rw [← fderiv_sub]
    congr 1; ext p; ring
    exact hp1
    exact hp2
  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h

  -- fderiv of p ↦ p.1^2 at (-1,0) sends (dx,dy) to dx * (2* -1) = dx * (-2)
  have h1 :
    (fderiv ℝ (fun p : ℝ×ℝ => p.1 ^ 2) ((-1:ℝ), 0)) (x - (-1), y - 0)
      = (x - (-1)) * (-2) :=
  by
    have comp1 : (fun p : ℝ×ℝ => p.1 ^ 2) = (fun t => t ^ 2) ∘ fun p => p.1 := rfl
    rw [comp1, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- now the one‐variable derivative
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- plug back into the CLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact differentiableAt_fst

  -- fderiv of p ↦ 2*p.2^3 + 3*p.2 at (-1,0) sends (dx,dy) to dy * (6*0^2 + 3) = dy * 3
  have h2 :
    (fderiv ℝ (fun p : ℝ×ℝ => 2 * p.2 ^ 3 + 3 * p.2) ((-1:ℝ), 0)) (x - (-1), y - 0)
      = (y - 0) * 3 :=
  by
    have comp2 : (fun p : ℝ×ℝ => 2 * p.2 ^ 3 + 3 * p.2) = (fun t => 2 * t ^ 3 + 3 * t) ∘ fun p => p.2 := rfl
    rw [comp2, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- expand the one‐variable derivative of (2*t^3 + 3*t)
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- back to the CLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact differentiableAt_snd

  -- constant c has zero derivative
  have h3 :
    fderiv ℝ (fun p : ℝ×ℝ => (c:ℝ)) ((-1:ℝ), 0) (x - (-1), y - 0) = 0 :=
    by rw [fderiv_const]; field_simp

  -- finish off
  rw [h1, h2, h3] at h
  ring_nf at h
  linarith

  -- the proofs for hp1 and hp2 in the splitting step
  all_goals
    try exact differentiableAt_pow _
    try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    try exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    try exact differentiableAt_const _
}

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

  -- 1) peel off the "- c"
  rw [fderiv_sub] at h

  -- 2) split the fderiv of (f1 - f2)
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5 : ℝ), (-4 : ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2)
                         ((-5 : ℝ), (-4 : ℝ))) :
    fderiv ℝ (fun p : ℝ × ℝ => 
      3 * p.1 ^ 2 - 5 * p.1
      - (3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2))
      ((-5 : ℝ), (-4 : ℝ))
    =
    fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5 : ℝ), (-4 : ℝ))
    -
    fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2)
           ((-5 : ℝ), (-4 : ℝ)) := by
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    all_goals assumption

  rw [h_split] at h
  -- apply the two ContinuousLinearMap.sub_apply
  rw [sub_apply, sub_apply] at h

  -- 3a) compute the x–part
  have h1 :
    fderiv ℝ (fun p => 3 * p.1 ^ 2 - 5 * p.1) ((-5 : ℝ), (-4 : ℝ))
      (x - (-5), y - (-4))
    = (x - (-5)) * (-35) := by
    -- reduce to a one–variable derivative in the first slot
    have comp1 :
      (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 5 * p.1)
      = (fun x => 3 * x ^ 2 - 5 * x) ∘ Prod.fst := rfl
    rw [comp1, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- compute deriv(3 x^2 - 5 x) = 6 x - 5 at x = -5
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- now assemble the continuous linear map
    rw [comp_apply, smulRight_apply, coe_fst']
    field_simp; norm_num
    all_goals assumption

  -- 3b) compute the y–part
  have h2 :
    fderiv ℝ (fun p => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2) ((-5 : ℝ), (-4 : ℝ))
      (x - (-5), y - (-4))
    = (y - (-4)) * (-164) := by
    have comp2 :
      (fun p : ℝ × ℝ => 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 4 * p.2)
      = (fun x => 3 * x ^ 3 - 2 * x ^ 2 + 4 * x) ∘ Prod.snd := rfl
    rw [comp2, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    rw [comp_apply, smulRight_apply, coe_snd']
    field_simp; norm_num
    all_goals assumption

  -- 3c) the constant c gives zero
  have h3 :
    fderiv ℝ (fun p : ℝ × ℝ => (c : ℝ)) ((-5 : ℝ), (-4 : ℝ)) (x - (-5), y - (-4)) = 0 := by
    rw [fderiv_const]; field_simp

  -- substitute back into h and finish
  rw [h1, h2, h3] at h
  ring_nf at h
  linarith

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
  -- split off the subtraction
  rw [fderiv_sub] at h
  have h_split
    (hp1 : DifferentiableAt ℝ (fun p => p.1 ^ 2 - p.1) ((-5 : ℝ), 1))
    (hp2 : DifferentiableAt ℝ (fun p => 5 * p.2 ^ 2)  ((-5 : ℝ), 1)) :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 - p.1 - 5 * p.2 ^ 2) ((-5 : ℝ), 1)
      = fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-5 : ℝ), 1)
        - fderiv ℝ (fun p => 5 * p.2 ^ 2)  ((-5 : ℝ), 1) := by
    rw [← fderiv_sub]
    congr 1
    ext p; ring
    exact hp1
    exact hp2
  -- apply the split
  rw [h_split] at h
  -- evaluate the subtraction of continuous linear maps
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.sub_apply] at h
  -- compute ∂/∂p.1 of p.1^2 - p.1 at p = (-5,1)
  have h1 :
    (fderiv ℝ (fun p => p.1 ^ 2 - p.1) ((-5 : ℝ), 1)) (x - (-5), y - 1)
      = (x - (-5)) * (-11) := by
    -- factor through fst
    have comp1 : (fun p : ℝ × ℝ => p.1 ^ 2 - p.1) =
                 (fun u => u ^ 2 - u) ∘ fun p => p.1 := rfl
    rw [comp1, fderiv_comp, fderiv_fst]
    -- pass to one‐variable derivative
    rw [← deriv_fderiv]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- apply the linear map
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst']
    field_simp; norm_num
    -- side‐conditions
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.sub (differentiableAt_pow _) differentiableAt_id
    exact differentiableAt_fst
  -- compute ∂/∂p.2 of 5 * p.2^2 at p = (-5,1)
  have h2 :
    (fderiv ℝ (fun p => 5 * p.2 ^ 2) ((-5 : ℝ), 1)) (x - (-5), y - 1)
      = (y - 1) * 10 := by
    have comp2 : (fun p : ℝ × ℝ => 5 * p.2 ^ 2) =
                 (fun u => 5 * u ^ 2) ∘ fun p => p.2 := rfl
    rw [comp2, fderiv_comp, fderiv_snd]
    rw [← deriv_fderiv]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd']
    field_simp; norm_num
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_snd
  -- derivative of the constant c is zero
  have h3 :
    fderiv ℝ (fun (_ : ℝ × ℝ) => c) ((-5 : ℝ), 1) (x - (-5), y - 1) = 0 := by
    rw [fderiv_const]; field_simp
  -- rewrite into h and conclude
  rw [h1] at h; rw [h2] at h; rw [h3] at h
  ring_nf at h; linarith
  -- discharge the differentiability goals
  exact DifferentiableAt.sub (DifferentiableAt.pow differentiableAt_fst) differentiableAt_fst
  exact DifferentiableAt.mul (differentiableAt_const _) (DifferentiableAt.pow differentiableAt_snd)

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
fderiv ℝ (fun p => 3*p.1^2 - p.1 - 3*p.2^2 - 3*p.2 - c) (-6,5) (x+6,y-5)

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

  -- turn
  --   fderiv (…) (1, -6) (x-1, y+6) = 0
  -- into
  --   (fderiv of 3*p.1^3+4*p.1) + (fderiv of 4*p.2) - (fderiv of c)  applied to (x-1,y+6) = 0
  -- so we can compute each piece separately:
  rw [fderiv_sub] at h
  have hsum :
    fderiv ℝ (fun p : ℝ×ℝ => 3*p.1^3 + 4*p.1 + 4*p.2) (1, -6)
      = fderiv ℝ (fun p => 3*p.1^3 + 4*p.1) (1, -6) +
        fderiv ℝ (fun p => 4*p.2)       (1, -6) := by
    -- fderiv of a sum is the sum of the fderivs
    rw [← fderiv_add]
    exact
      ⟨ differentiableAt_add
          (differentiableAt_mul differentiableAt_const differentiableAt_pow)
          (differentiableAt_mul differentiableAt_const differentiableAt_id),
        differentiableAt_mul differentiableAt_const differentiableAt_snd ⟩

  -- apply that splitting to our hypothesis
  rw [hsum, sub_add_eq_sub_sub] at h
  -- now `h` is
  --   (fderiv ℝ (fun p => 3*p.1^3+4*p.1) (1,-6) + fderiv ℝ (fun p => 4*p.2) (1,-6))
  --     (x-1,y+6)
  --   = 0, and we can rewrite it as two separate applications
  rw [add_apply, sub_apply] at h

  -- 1) compute fderiv of 3*p.1^3 + 4*p.1
  have h1 : 
    fderiv ℝ (fun p => 3*p.1^3 + 4*p.1) (1, -6) (x - 1, y + 6) = (x - 1) * 13 := by
    -- reduce to a one‐variable derivative by composing with `prod.fst`
    have eq₁ : (fun p : ℝ×ℝ => 3*p.1^3 + 4*p.1) = (fun u => 3*u^3 + 4*u) ∘ prod.fst := rfl
    rw [eq₁, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- now we only need the scalar derivative at 1
    have deriv₁ : deriv (fun u => 3*u^3 + 4*u) 1 = 13 := by
      simp [deriv_add, deriv_mul_const, deriv_pow]
    rw [deriv₁]
    -- finish the linear‐map simplification
    simp [ContinuousLinearMap.coe_fst, ContinuousLinearMap.smulRight_apply]

  -- 2) compute fderiv of 4*p.2
  have h2 :
    fderiv ℝ (fun p => 4*p.2) (1, -6) (x - 1, y + 6) = (y + 6) * 4 := by
    have eq₂ : (fun p : ℝ×ℝ => 4*p.2) = (fun v => 4*v) ∘ prod.snd := rfl
    rw [eq₂, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    -- one‐variable derivative at −6
    have deriv₂ : deriv (fun v => 4*v) (-6) = 4 := by simp
    rw [deriv₂]
    simp [ContinuousLinearMap.coe_snd, ContinuousLinearMap.smulRight_apply]

  -- 3) the constant c has zero derivative
  have h3 : fderiv ℝ (fun _ => c) (1, -6) (x - 1, y + 6) = 0 := by
    simp [fderiv_const]

  -- rewrite h using h1,h2,h3
  rw [h1, h2, h3] at h
  -- now `h` is `(x-1)*13 - (y+6)*4 = 0`, i.e. `(x-1)*13 + (y+6)*4 = 0`
  simp at h
  exact h

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
example (x y c : ℝ) :
  fderiv ℝ (fun p => p.1 + 5 * p.2 ^ 2 - c) (2, 6) (x - 2, y - 6) = 0
  → (x - 2) + (y - 6) * 60 = 0

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
-- 1) Compute the total derivative at (-2,-5) in one go:
have D :
  fderiv ℝ (fun p : ℝ×ℝ =>
    2*p.1^2 - 2*p.1 - 3*p.2^4 - 5*p.2^3 - 5*p.2 - c)
    (-2,-5)
  = (LinearMap.prodMk (fun v => (4 * (-2) - 2) * v.1)
                     fun v => -(12 * (-5)^3 + 15 * (-5)^2 + 5) * v.2) := by
  simp [ fderiv_add, fderiv_sub, fderiv_comp
       , fderiv_fst, fderiv_snd
       , deriv_pow', deriv_mul_const
       , deriv_const, deriv_id ]
-- 2) Rewrite `h` using that explicit linear map, kill the negations, and
--    numerical-simplify the two coefficients:
rw [D, prodMk_apply, neg_neg] at h
norm_num at h
-- now `h : -10*(x+2) + 1120*(y+5) = 0`, i.e.
-- `h : (x+2)*(-10) + (y+5)*1120 = 0`.
-- 3) Convert that into the desired form
by simpa [add_comm] using h

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
  -- separate the “+2*p.1 + 2*p.2” from the “- c”
  rw [fderiv_sub] at h
  -- split fderiv of a sum into the sum of fdervs
  have h_sum
    (hp1 : DifferentiableAt ℝ (fun p => 2*p.1) ((-4:ℝ),(1:ℝ)))
    (hp2 : DifferentiableAt ℝ (fun p => 2*p.2) ((-4:ℝ),(1:ℝ))) :
    fderiv ℝ (fun p : ℝ×ℝ => 2*p.1 + 2*p.2) ((-4:ℝ),(1:ℝ))
      = fderiv ℝ (fun p => 2*p.1) ((-4:ℝ),(1:ℝ))
        + fderiv ℝ (fun p => 2*p.2) ((-4:ℝ),(1:ℝ)) := by
    rw [← fderiv_add]; exact hp1; exact hp2
  -- apply the splitting
  rw [h_sum] at h
  -- turn the continuous linear map subtraction into `L1 v - L2 v`
  rw [ContinuousLinearMap.sub_apply] at h
  -- turn the sum into `L1 v + L2 v`
  rw [ContinuousLinearMap.add_apply] at h

  -- now compute each piece on `(x-(-4), y-1)`
  have h1 :
    (fderiv ℝ (fun p => 2*p.1) ((-4:ℝ),(1:ℝ))) (x - (-4), y - 1)
      = (x - (-4)) * 2 := by
    -- express `2 * p.1` as `(fun x => 2*x) ∘ fst`
    have comp : (fun p : ℝ×ℝ => 2*p.1) = (fun t => 2*t) ∘ fun p => p.1 := rfl
    rw [comp, fderiv_comp, fderiv_fst, ← deriv_fderiv]
    -- now do the one‐variable derivative: `(fun t => 2*t)`
    nth_rewrite 1 [deriv_const_mul]
    nth_rewrite 1 [deriv_id]
    rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst']
    field_simp
    -- side‐conditions for deriv_fderiv and deriv_const_mul
    exact differentiableAt_const _
    exact differentiableAt_id

  have h2 :
    (fderiv ℝ (fun p => 2*p.2) ((-4:ℝ),(1:ℝ))) (x - (-4), y - 1)
      = (y - 1) * 2 := by
    have comp : (fun p : ℝ×ℝ => 2*p.2) = (fun t => 2*t) ∘ fun p => p.2 := rfl
    rw [comp, fderiv_comp, fderiv_snd, ← deriv_fderiv]
    nth_rewrite 1 [deriv_const_mul]
    nth_rewrite 1 [deriv_id]
    rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_snd']
    field_simp
    exact differentiableAt_const _
    exact differentiableAt_id

  have h3 :
    fderiv ℝ (fun p => (c:ℝ)) ((-4:ℝ),(1:ℝ)) (x - (-4), y - 1) = 0 := by
    rw [fderiv_const]; field_simp

  -- plug these back into `h`
  rw [h1, h2, h3] at h
  -- clean up and finish
  ring_nf at h
  exact h

  -- now supply the missing differentiability facts:
  all_goals
    try exact (by simp only [differentiableAt_const] : _)
    try exact (by simp only [differentiableAt_id] : _)

