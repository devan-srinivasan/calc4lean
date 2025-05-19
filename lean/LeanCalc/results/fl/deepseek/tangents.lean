import Mathlib
open Real

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 - p.2 ^ 3 - p.2 ^ 2 - 3 * p.2 - c) ((-1:ℝ), (6:ℝ)) (x-(-1), y-6) = 0) → ((x-(-1)) * (-4) - (y-6) * (123) = 0) := by
  intro h
  simp_all only [fderiv_const, Subtype.val_eq_coe, Prod.mk.inj_iff, sub_eq_zero, sub_self,
    fderiv_id'', fderiv_snd', fderiv_fst', fderiv_const', fderiv_add', fderiv_mul,
    fderiv_sub', fderiv_pow', sub_zero, zero_sub, mul_one, mul_zero, add_zero, zero_add,
    sub_neg_eq_add, add_comm, mul_comm, mul_assoc, mul_left_comm]
  linarith [h]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 2 - 4 * p.2 - c) ((4:ℝ), (4:ℝ)) (x-4, y-4) = 0) → ((x-4) * (28) - (y-4) * (20) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 2 - 4 * p.2 - 0) (4, 4) = 0 := by simpa using h
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 2 + 4 * p.1 - 2 * p.2 ^ 2 - 4 * p.2) (4, 4) = 0 := by simpa using h1
  have h3 : fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 - 2 * p.2 ^ 2) (4, 4) = 0 := by
    simpa using fderiv_snd (4, 4) ▸ h2
  have h4 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 2 * p.2 ^ 2) (4, 4) = 0 := by
    simpa using fderiv_fst (4, 4) ▸ h3
  have h5 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 2) (4, 4) = 0 := by
    simpa using fderiv_snd (4, 4) ▸ h4
  have h6 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2) (4, 4) = 0 := by
    simpa using fderiv_snd (4, 4) ▸ h5
  have h7 : fderiv ℝ (fun p : ℝ × ℝ => p.1) (4, 4) = 0 := by
    simpa using fderiv_snd (4, 4) ▸ h6
  simpa using fderiv_fst (4, 4) ▸ h7

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.2 ^ 2 - c) ((0:ℝ), (-1:ℝ)) (x-0, y-(-1)) = 0) → ((x-0) * (0) - (y-(-1)) * (-8) = 0) := by
  intro h
  have h' := h
  simp at h'
  have h'' : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 2 - 4 * p.2 ^ 2 - c) (0, -1) (0, 8) = 0 := by
    linarith
  have h''' := h''
  simp at h'''
  have h'''' : 5 * 0 ^ 2 - 4 * 8 ^ 2 - c = 5 * 0 ^ 2 - 4 * (-1) ^ 2 - c := by
    linarith
  simp at h''''
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) ((4:ℝ), (1:ℝ)) (x-4, y-1) = 0) → ((x-4) * (48) + (y-1) * (8) = 0) := by
  intro h
  simp [fderiv_eq_zero_iff_eq_const] at h
  have h1 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h2 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h3 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h4 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h5 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h6 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h7 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h8 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h9 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  have h10 : (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) = (fun p ↦ p.1 ^ 3 + 2 * p.2 ^ 4 - c) := rfl
  simp at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + p.1 + p.2 ^ 2 + 4 * p.2 - c) ((-4:ℝ), (5:ℝ)) (x-(-4), y-5) = 0) → ((x-(-4)) * (-767) + (y-5) * (14) = 0) := by
  intro h
  have h' : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 4 + p.1 + p.2 ^ 2 + 4 * p.2 - c) (-4, 5) = 0 := by
    simp_all
  have h'' : (x + 4) * (-767) + (y - 5) * 14 = 0 := by
    simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 4 + 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2 - c) ((-2:ℝ), (-6:ℝ)) (x-(-2), y-(-6)) = 0) → ((x-(-2)) * (1) + (y-(-6)) * (-568) = 0) := by
  intro h
  have h1 := h
  simp_all only [fderiv_add, fderiv_const, fderiv_id, fderiv_pow, fderiv_mul, fderiv_sub, fderiv_smul]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-30) - (y-3) * (88) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 2 - 3 * p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) ((-5, 3)) = fun p : ℝ × ℝ => 0 := by
    ext p
    simp [fderiv_const]
  rw [h1] at h
  simp at h
  ring_nf at h
  exact h

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((-1:ℝ), (2:ℝ)) (x-(-1), y-2) = 0) → ((x-(-1)) * (10) + (y-2) * (64) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  have h2 := h1
  simp [fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const] at h2
  have h3 := h2
  simp at h3
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.2 ^ 2 + p.2 - c) ((0:ℝ), (4:ℝ)) (x-0, y-4) = 0) → ((x-0) * (0) - (y-4) * (7) = 0) := by
  intro h
  have h₀ : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.2 ^ 2 + p.2 - c) ((0:ℝ), (4:ℝ)) =
    fun p ↦ (0 * p.1 - 0 * p.2, 8 * 0 - 2 * 4 + 1) := by
    sorry
  have h₁ : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.2 ^ 2 + p.2 - c) ((0:ℝ), (4:ℝ)) (x-0, y-4) =
    (x-0) * (0) - (y-4) * (7) := by
    sorry
  simpa [h₀, h₁] using h

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 - 4 * p.2 - c) ((1:ℝ), (-4:ℝ)) (x-1, y-(-4)) = 0) → ((x-1) * (5) - (y-(-4)) * (-1260) = 0) := by
  intro h
  simp only [fderiv_const, fderiv_fst, fderiv_snd, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_const_smul, fderiv_smul, fderiv_id, smul_eq_mul, mul_one] at h
  norm_num at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (-16) + (y-(-5)) * (5) = 0) := by
  intro h
  simp [fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (3:ℝ)) (x-(-4), y-3) = 0) → ((x-(-4)) * (8) + (y-3) * (2) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (3:ℝ)) = fun ⟨x, y⟩ ↦ ⟨(3 * (-4) ^ 2 + 10 * (-4)), 2⟩ := by
    ext1 ⟨x, y⟩
    simp [fderiv_eq_iff_eq_smul_one]
    aesop
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 + p.2 ^ 3 + p.2 - c) ((1:ℝ), (2:ℝ)) (x-1, y-2) = 0) → ((x-1) * (5) + (y-2) * (13) = 0) := by
  intro h
  have h' := congr_arg (fun x ↦ x - 0) h
  simp at h'
  have h'' := congr_arg (fun x ↦ x - 0) h'
  simp at h''
  have h''' := congr_arg (fun x ↦ x - 0) h''
  simp at h'''
  have h'''' := congr_arg (fun x ↦ x - 0) h'''
  simp at h''''
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c) ((-3:ℝ), (2:ℝ)) (x-(-3), y-2) = 0) → ((x-(-3)) * (-23) + (y-2) * (1) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c) ((-3), 2) =
      (fun p : ℝ × ℝ ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c).fderiv ((-3), 2) := rfl
  rw [h1] at h
  have h2 : fderiv ℝ (fun p : ℝ × ℝ ↦ 4 * p.1 ^ 2 + p.1 + p.2 - c) ((-3), 2) =
      fun p : ℝ × ℝ ↦ (4 * (2 * (-3)) + 1) • p.1 + (1 : ℝ) • p.2 := by
    rw [fderiv_sub_const c]
    rw [fderiv_add]
    rw [fderiv_add]
    simp
    rw [fderiv_mul_const_field]
    simp
    rw [fderiv_id']
    simp
  rw [h2] at h
  have h3 : (fun p : ℝ × ℝ ↦ (4 * (2 * (-3)) + 1) • p.1 + (1 : ℝ) • p.2) (x - (-3), y - 2) = 0 := by
    simp at h
    exact h
  simp at h3
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 3 - p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (-2:ℝ)) (x-(-5), y-(-2)) = 0) → ((x-(-5)) * (421) + (y-(-2)) * (20) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 3 - p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (-2:ℝ)) (x-(-5), y-(-2)) = 0 := h
  have h2 : (x - -5) * 421 + (y - -2) * 20 = 0 := by
    simp at h1
    ring_nf at h1
    linarith
  exact h2

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 + 5 * p.2 - c) ((-5:ℝ), (-4:ℝ)) (x-(-5), y-(-4)) = 0) → ((x-(-5)) * (3) + (y-(-4)) * (-3) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 + 5 * p.2 - c) ((-5:ℝ), (-4:ℝ)) = fun p ↦ (3 : ℝ) • p.1 + (2 : ℝ) • p.2 + (5 : ℝ) := by
    rw [fderiv_add, fderiv_const, fderiv_mul, fderiv_pow]
    · simp
    · simp
    · simp
    · simp
    · simp
  simp at h1
  have h2 : (x - -5) * 3 + (y - -4) * -3 = 0 := by
    simp
    linarith
  exact h2

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + p.2 - c) ((4:ℝ), (2:ℝ)) (x-4, y-2) = 0) → ((x-4) * (144) + (y-2) * (1) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 3 + p.2 - c) (4, 2) = fun p : ℝ × ℝ => 144 * p.1 + 1 * p.2 := by
    funext p
    rw [fderiv_sub_const]
    rw [fderiv_comp (f := fun x => x ^ 3) (g := fun x => 3 * x)]
    simp [fderiv_id, fderiv_const, fderiv_pow]
    ring
  simp_all [fderiv_const, fderiv_id, fderiv_sub_const]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (99) - (y-(-2)) * (-216) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.1 ^ 2 + 3 * p.1 - 5 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2) ((-3:ℝ), (-2:ℝ)) = fun p ↦ (99:ℝ) * p.1 - (-216:ℝ) * p.2 := by
    rw [fderiv_eq_iff_eq_of_real_smul_right] at h
    exact h
  have h2 : (fun p ↦ (99:ℝ) * p.1 - (-216:ℝ) * p.2) (x - (-3), y - (-2)) = 0 := by
    rw [←h1]
    simp [h]
  simp [h2]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (-4:ℝ)) (x-(-2), y-(-4)) = 0) → ((x-(-2)) * (-15) - (y-(-4)) * (7) = 0) := by
  intro h
  have h₁ :
    fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c))
      (-2, -4) = 0 := h
  have h₂ :
    (x - (-2)) * (-15) - (y - (-4)) * 7 = 0 := by
    rw [← sub_eq_zero] at h₁
    have h₃ : fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c))
      (-2, -4) = 0 := by
      exact h₁
    have h₄ :
      fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c))
        (-2, -4) = 0 := by
      exact h₃
    have h₅ :
      fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 2 + 5 * p.1 - p.2 ^ 3 - 5 * p.2 ^ 2 + p.2 - c))
        (-2, -4) = 0 := by
      exact h₄
    simp [h₅]
  exact h₂

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 - p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2 - c) ((-5:ℝ), (5:ℝ)) (x-(-5), y-5) = 0) → ((x-(-5)) * (-2417) - (y-5) * (1510) = 0) := by
  intro h
  simp [fderiv_const, fderiv_add, fderiv_mul, fderiv_comp, fderiv_pow, fderiv_id, fderiv_const,
    fderiv_sub, fderiv_neg, fderiv_smul, fderiv_zpow] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2 - c) ((1:ℝ), (-5:ℝ)) (x-1, y-(-5)) = 0) → ((x-1) * (4) + (y-(-5)) * (-632) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2 - c) ((1:ℝ), (-5:ℝ)) = 0 := by
    rw [h]
    simp
  have h2 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 2 * p.2 - c) ((1:ℝ), (-5:ℝ)) (x-1, y-(-5)) = 0 := by
    rw [h]
    simp
  have h3 : (x-1) * (4) + (y-(-5)) * (-632) = 0 := by
    apply HasFDerivAt.hasDerivAt
    apply HasFDerivAt.prod
    apply HasFDerivAt.const_mul
    apply HasFDerivAt.id
    apply HasFDerivAt.const_mul
    apply HasFDerivAt.pow
    apply HasFDerivAt.const_sub
    apply HasFDerivAt.pow
    apply HasFDerivAt.const_sub
    apply HasFDerivAt.pow
    apply HasFDerivAt.const_sub
    apply HasFDerivAt.id
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 4 * p.1 + 2 * p.2 ^ 2 - c) ((1:ℝ), (-1:ℝ)) (x-1, y-(-1)) = 0) → ((x-1) * (-11) + (y-(-1)) * (-4) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  have h2 := h1
  ring_nf at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 + 3 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 0) → ((x-5) * (20) - (y-(-4)) * (221) = 0) := by
  intro h
  have h₁ : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 + 3 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 0 := h
  have h₂ : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 + 3 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 20 * (x-5) - 221 * (y-(-4)) := by
    rw [fderiv_eq_iff_eq_of_line]
    rfl
  simp at h₂
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (-3:ℝ)) (x-(-4), y-(-3)) = 0) → ((x-(-4)) * (240) - (y-(-3)) * (82) = 0) := by
  intro h
  simp only [fderiv_const_sub, fderiv_const, sub_zero, zero_sub, fderiv_sub, fderiv_pow, fderiv_mul, fderiv_id, fderiv_const,
    fderiv_pow, fderiv_mul, fderiv_id, fderiv_const] at h
  simp only [mul_one, mul_neg, mul_assoc, mul_comm, mul_left_comm, sub_neg_eq_add,
    add_assoc, add_right_neg, add_zero] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (12) - (y-(-2)) * (28) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (-2:ℝ)) = fun p ↦ (12:ℝ) * p.1 - (28:ℝ) * p.2 := by
    apply fderiv_of_multilinear_to_euclidean
    intro x y
    simp
    ring
  have h2 : ((x-(-1)) * (12) - (y-(-2)) * (28) = 0) := by
    have h3 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - p.2 ^ 3 + 3 * p.2 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0 := by
      apply h
    have h4 : (fun p ↦ (12:ℝ) * p.1 - (28:ℝ) * p.2) (x-(-1), y-(-2)) = 0 := by
      apply h3
    simp at h4
    exact h4
  exact h2

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.2 - c) ((-5:ℝ), (-3:ℝ)) (x-(-5), y-(-3)) = 0) → ((x-(-5)) * (-10) - (y-(-3)) * (3) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 - 3 * p.2 - c) (-5, -3) = 0 := h
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 - 3 * p.2 - c) (-5, -3) (x - -5, y - -3) = 0 := by simp_all
  have h3 : (x - -5) * (fderiv ℝ (fun p : ℝ × ℝ => p.1) (-5, -3) (x - -5, y - -3)) - (y - -3) * (fderiv ℝ (fun p : ℝ × ℝ => p.2) (-5, -3) (x - -5, y - -3)) = 0 := by simp [h1, h2]
  have h4 : fderiv ℝ (fun p : ℝ × ℝ => p.1) (-5, -3) (x - -5, y - -3) = 1 := by simp
  have h5 : fderiv ℝ (fun p : ℝ × ℝ => p.2) (-5, -3) (x - -5, y - -3) = 0 := by simp
  simp [h4, h5] at h3
  assumption

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 + 3 * p.2 - c) ((1:ℝ), (1:ℝ)) (x-1, y-1) = 0) → ((x-1) * (15) + (y-1) * (3) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 + 3 * p.2 - c) ((1:ℝ), (1:ℝ)) = 0 := by
    rw [fderiv_eq_zero_iff_comp_hasFDerivAt] at h
    simpa using h
  have h2 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 + 3 * p.2 - c) ((1:ℝ), (1:ℝ)) (x-1, y-1) = 0 := by
    simpa using h1 (x-1, y-1)
  simpa [h2] using h

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 3 * p.1 ^ 3 + 2 * p.1 ^ 2 - 5 * p.1 - p.2 ^ 4 - c) ((-6:ℝ), (-4:ℝ)) (x-(-6), y-(-4)) = 0) → ((x-(-6)) * (-2081) - (y-(-4)) * (-256) = 0) := by
  intro h
  have h1 := h
  simp_all [fderiv_within_id, fderiv_within_const, fderiv_within_comp,
    fderiv_within_add, fderiv_within_mul, fderiv_within_neg, fderiv_within_pow]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 + p.2 ^ 3 - 3 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (4) + (y-(-2)) * (19) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  have h2 := fderiv_const (4 * x + y ^ 3 - 3 * y ^ 2 - 5 * y - c) ((6:ℝ), (-2:ℝ))
  have h3 := fderiv_const (4 * x + y ^ 3 - 3 * y ^ 2 - 5 * y - c) ((6:ℝ), (-2:ℝ))
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (5) + (y-6) * (1393) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) ((-3:ℝ), (6:ℝ)) = fun _ ↦ 0 := by
    ext1
    simp [fderiv] at h
    linarith
  simp [h1] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 2 - p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (63) + (y-(-2)) * (-5) = 0) := by
  intro h;
  simp only [fderiv_example] at h
  norm_num at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.1 + 2 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (190) + (y-(-3)) * (72) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  simp [fderiv_const] at h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 - 3 * p.1 ^ 3 - 2 * p.1 - 3 * p.2 ^ 3 - c) ((-4:ℝ), (0:ℝ)) (x-(-4), y-0) = 0) → ((x-(-4)) * (-914) - (y-0) * (0) = 0) := by
  intro h
  have h₁ := h
  simp_all [fderiv_const, fderiv_fpow, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_comp,
    fderiv_const_of_not_mem_nhds, fderiv_id, fderiv_neg, fderiv_add, fderiv_sub_left]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 2 * p.1 ^ 2 - 4 * p.1 - 2 * p.2 ^ 4 - 5 * p.2 ^ 3 + p.2 ^ 2 - 4 * p.2 - c) ((-6:ℝ), (0:ℝ)) (x-(-6), y-0) = 0) → ((x-(-6)) * (236) - (y-0) * (4) = 0) := by
  intro h
  simp [fderiv_within_univ] at h
  norm_num at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 + 4 * p.2 ^ 4 - 5 * p.2 ^ 3 - 2 * p.2 - c) ((-1:ℝ), (-1:ℝ)) (x-(-1), y-(-1)) = 0) → ((x-(-1)) * (-3) + (y-(-1)) * (-33) = 0) := by
  intro h; simp at h
  ring_nf at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 3 - 4 * p.2 - c) ((-3:ℝ), (3:ℝ)) (x-(-3), y-3) = 0) → ((x-(-3)) * (-35) + (y-3) * (104) = 0) := by
  intro h
  have h₁ : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 5 * p.1 + 4 * p.2 ^ 3 - 4 * p.2 - c) ((-3:ℝ), (3:ℝ)) (x-(-3), y-3) =
      (x-(-3)) * (-35) + (y-3) * (104) := by
    rw [fderiv_const_sub_apply] at h
    simp_all
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 2 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (16) - (y-(-3)) * (-12) = 0) := by
  intro h
  rw [fderiv_within_univ] at h
  simp [fderivWithin_univ] at h
  ring_nf at h ⊢
  norm_num at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.1 - 3 * p.2 ^ 3 - 4 * p.2 - c) ((-1:ℝ), (3:ℝ)) (x-(-1), y-3) = 0) → ((x-(-1)) * (10) - (y-3) * (85) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_fst, fderiv_snd, fderiv_const, fderiv_id] at h1
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 3 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 2 - c) ((-6:ℝ), (-4:ℝ)) (x-(-6), y-(-4)) = 0) → ((x-(-6)) * (463) + (y-(-4)) * (-8) = 0) := by
  intro h
  simp [fderiv_const] at h
  simp [fderiv_const]
  ring_nf at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + p.1 ^ 2 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2 - c) ((5:ℝ), (3:ℝ)) (x-5, y-3) = 0) → ((x-5) * (385) - (y-3) * (101) = 0) := by
  intro h
  have h1 : ∀ x y, fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + p.1 ^ 2 - 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + 4 * p.2 - (c:ℝ)) (5, 3) =
    (fun p ↦ (150 * p.1 ^ 2 + 10 * p.1 - 30 * p.2 ^ 2 - 8 * p.2 + 4, -90 * p.1 ^ 2 - 12 * p.1 + 24 * p.2 ^ 2 + 16 * p.2)) := by
    intro x y
    ext
    · simp [fderiv_add, fderiv_mul, fderiv_const, fderiv_zpow, fderiv_id, fderiv_neg, fderiv_sub,
        fderiv_pow, fderiv_comp, fderiv_of_const, fderiv_of_id, fderiv_of_neg, fderiv_of_sub]
      ring
    · simp [fderiv_add, fderiv_mul, fderiv_const, fderiv_zpow, fderiv_id, fderiv_neg, fderiv_sub,
        fderiv_pow, fderiv_comp, fderiv_of_const, fderiv_of_id, fderiv_of_neg, fderiv_of_sub]
      ring
  simp_all
  <;> simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 5 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c) ((1:ℝ), (2:ℝ)) (x-1, y-2) = 0) → ((x-1) * (3) - (y-2) * (25) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 5 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c) ((1:ℝ), (2:ℝ)) (x-1, y-2) = 0 := h
  rw [fderiv_eq_zero_of_not_differentiableAt] at h1
  <;> simp [h1]
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2 - c) ((-6:ℝ), (2:ℝ)) (x-(-6), y-2) = 0) → ((x-(-6)) * (-27) + (y-2) * (15) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2 - c) ((-6:ℝ), (2:ℝ)) = 0 := by
    apply h
  have h2 : (fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2 - c) =ᶠ[𝓝 ((-6:ℝ), (2:ℝ))] fun p ↦ 2 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 3 + p.2 ^ 2 - p.2 - c := by
    apply eventually_of_forall
    intro p
    rfl
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + 5 * p.2 ^ 2 - p.2 - c) ((1:ℝ), (-2:ℝ)) (x-1, y-(-2)) = 0) → ((x-1) * (3) + (y-(-2)) * (-21) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 + 5 * p.2 ^ 2 - p.2 - c) ((1:ℝ), (-2:ℝ)) = fun p ↦ 3 • p.1 + (-21) • p.2 := by
    funext
    simp [fderiv]
    ring
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 2 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (3) - (y-5) * (19) = 0) := by
  intro h
  have h1 := h
  simp at h1
  have h2 := h1
  ring_nf at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + p.1 ^ 2 + p.1 + p.2 - c) ((2:ℝ), (5:ℝ)) (x-2, y-5) = 0) → ((x-2) * (53) + (y-5) * (1) = 0) := by
  intro h
  simp only [fderiv_const, fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_sub] at h
  norm_num at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + p.1 ^ 2 + p.1 - p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (2:ℝ)) (x-(-2), y-2) = 0) → ((x-(-2)) * (-99) - (y-2) * (67) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 4 + p.1 ^ 2 + p.1 - p.2 ^ 4 - 2 * p.2 ^ 3 - 3 * p.2 ^ 2 + p.2 - c) ((-2:ℝ), (2:ℝ)) = fun p ↦ 0 := by
    rw [h]
    rfl
  have h2 : (fun p ↦ 0 : ℝ →L[ℝ] ℝ) (x - (-2), y - 2) = 0 := by simp
  simp [h1, h2] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (3) + (y-1) * (12) = 0) := by
  intro h
  simp_all [fderiv_const, fderiv_id, fderiv_add, fderiv_mul, fderiv_pow, fderiv_comp]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 4 * p.1 ^ 3 + 5 * p.2 ^ 3 - 3 * p.2 - c) ((-3:ℝ), (-4:ℝ)) (x-(-3), y-(-4)) = 0) → ((x-(-3)) * (0) + (y-(-4)) * (237) = 0) := by
  intro h
  simp_all only [fderiv_const, eq_self_iff_true, zero_add, zero_mul, zero_sub, mul_one, mul_zero,
    sub_zero, mul_comm, mul_left_comm, mul_assoc]
  norm_num
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + p.2 ^ 2 - 4 * p.2 - c) ((-2:ℝ), (0:ℝ)) (x-(-2), y-0) = 0) → ((x-(-2)) * (2) + (y-0) * (-4) = 0) := by
  intro h
  have h' := h
  simp_all [fderiv_const]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 5 * p.2 ^ 2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-2800) + (y-3) * (30) = 0) := by
  intro h
  have : fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 5 * p.2 ^ 2 - c)) (-5, 3) = fun _ => 0 := by
    rw [h]
    rfl
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 4 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - 3 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (3408) + (y-3) * (168) = 0) := by
  intro h
  have h' := h
  simp [fderiv, hasFDerivAt_iff_hasDerivAt, hasDerivAt_filter_iff_tendsto] at h'
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.2 ^ 2 + 2 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (-30) - (y-(-5)) * (-42) = 0) := by
  intro h
  have h2 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.2 ^ 2 + 2 * p.2 - c) ((-3:ℝ), (-5:ℝ)) = (fun p ↦ 0) := by
    rw [h]
    rfl
  simp_all
  -- The problem is that the `have h2` line is false, and thus the rest of the proof cannot be completed as intended.
  -- The goal is to show that the derivative of the function at the given point is zero, which implies the tangent line is horizontal.
  -- However, the provided derivative calculation does not correctly reflect the actual derivative of the function.
  -- The correct derivative should be calculated and verified.
  -- This is a placeholder for the actual derivative calculation, which needs to be corrected.
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (1:ℝ)) (x-(-5), y-1) = 0) → ((x-(-5)) * (-2390) + (y-1) * (10) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (1:ℝ)) (x-(-5), y-1) = 0 := by simpa using h
  have h2 : (x-(-5)) * (-2390) + (y-1) * (10) = 0 := by
    have h3 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (1:ℝ)) = fun _ ↦ 0 := by
      apply HasFDerivAt.fderiv
      apply HasFDerivAt.const_sub
      apply HasFDerivAt.add
      apply HasFDerivAt.add
      apply HasFDerivAt.add
      apply HasFDerivAt.add
      apply HasFDerivAt.mul_const
      apply HasFDerivAt.pow
      apply HasFDerivAt.mul_const
      apply HasFDerivAt.pow
      apply HasFDerivAt.mul_const
      apply HasFDerivAt.pow
      apply HasFDerivAt.mul_const
      apply HasFDerivAt.pow
    simp [h3] at h1
    linarith
  exact h2

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + p.1 - 3 * p.2 - c) ((-4:ℝ), (-3:ℝ)) (x-(-4), y-(-3)) = 0) → ((x-(-4)) * (-15) - (y-(-3)) * (3) = 0) := by
  intro h
  rw [fderiv_eq_zero_iff_eq] at h
  simp at h
  have h1 : (x - -4) * 2 + 1 = 0 := by linarith
  have h2 : (y - -3) * -3 - 3 = 0 := by linarith
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.1 - p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (1) - (y-3) * (1) = 0) := by
  intro h
  simp_all [fderiv, hasFDerivAt_filter]
  norm_num
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.2 ^ 2 + 2 * p.2 - c) ((0:ℝ), (-3:ℝ)) (x-0, y-(-3)) = 0) → ((x-0) * (0) - (y-(-3)) * (-32) = 0) := by
  intro h
  simp at h
  ring_nf at h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 3 * p.1 + p.2 ^ 4 + p.2 - c) ((2:ℝ), (0:ℝ)) (x-2, y-0) = 0) → ((x-2) * (15) + (y-0) * (1) = 0) := by
  intro h
  have h1 := h
  simp [fderiv, HasFDerivAt, HasDerivAt, deriv] at h1
  simp [h1]
  ring_nf
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 5 * p.1 ^ 3 + 4 * p.1 ^ 2 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 - c) ((-5:ℝ), (3:ℝ)) (x-(-5), y-3) = 0) → ((x-(-5)) * (-665) + (y-3) * (84) = 0) := by
  intro h
  simp [fderiv, HasFDerivAt, HasDerivAt, deriv] at h
  ring_nf at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - p.1 + 4 * p.2 ^ 2 - c) ((0:ℝ), (0:ℝ)) (x-0, y-0) = 0) → ((x-0) * (-1) + (y-0) * (0) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 - p.1 + 4 * p.2 ^ 2 - c) (0, 0) (x - 0, y - 0) = 0 := by simpa using h
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 - p.1 + 4 * p.2 ^ 2 - c) (0, 0) (x, y) = 0 := by simpa using h1
  have h3 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 - p.1 + 4 * p.2 ^ 2 - c) (0, 0) (x, y) = 0 := by simpa using h2
  have h4 : (x - 0) * (-1) + (y - 0) * (0) = 0 := by simpa using h3
  simpa using h4

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 - 4 * p.2 ^ 3 - p.2 ^ 2 + p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (133) - (y-0) * (-1) = 0) := by
  intro h
  simp_all only [Function.comp_apply, fderiv_const, fderiv_id, fderiv_comp, fderiv_mul,
    fderiv_add, fderiv_sub, fderiv_neg, mul_one, mul_zero, sub_zero, neg_zero, add_zero,
    sub_self, mul_neg, mul_one, neg_neg, zero_add, zero_sub, sub_neg_eq_add, neg_add_rev,
    neg_sub, neg_neg, neg_zero, sub_zero, neg_mul_eq_mul_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg, neg_neg,
    neg
example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - p.2 ^ 3 - c) ((-2:ℝ), (-2:ℝ)) (x-(-2), y-(-2)) = 0) → ((x-(-2)) * (48) - (y-(-2)) * (12) = 0) := by
  intro h
  simp only [fderiv_const, Pi.zero_apply, map_sub, sub_zero] at h
  have := congr_arg (fun z => z / 48) h
  simp only [zero_div, sub_zero, mul_comm] at this
  norm_num at this
  have := congr_arg (fun z => z / 12) h
  simp only [zero_div, sub_zero, mul_comm] at this
  norm_num at this
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3 - c) ((4:ℝ), (3:ℝ)) (x-4, y-3) = 0) → ((x-4) * (133) - (y-3) * (54) = 0) := by
  intro h
  have h₀ : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 - 2 * p.1 ^ 3 - 4 * p.1 ^ 2 + 5 * p.1 - 2 * p.2 ^ 3 - c) (4, 3) = fun p => 133 * p.1 - 54 * p.2 := by
    funext p
    simp only [fderiv_sub, fderiv_const, fderiv_pow, fderiv_mul, fderiv_id, fderiv_comp,
      fderiv_pow, fderiv_const, fderiv_id, fderiv_comp]
    simp only [mul_one, mul_zero, add_zero, zero_add, mul_neg, mul_one, neg_mul, neg_neg,
      mul_assoc, mul_comm, mul_left_comm]
    ring
  have h₁ : (x - 4) * 133 - (y - 3) * 54 = 0 := by
    simpa [h₀] using h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3 - c) ((-4:ℝ), (1:ℝ)) (x-(-4), y-1) = 0) → ((x-(-4)) * (-1221) - (y-1) * (3) = 0) := by
  intro h
  have h1 : ∀ x y : ℝ, fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3 - c) (x, y) = fun p ↦ 0 := by
    intro x y
    have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3 - c) (x, y) = 0 := by
      apply h
    exact h1
  have h2 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 + 3 * p.1 - p.2 ^ 3 - c) ((-4:ℝ), (1:ℝ)) = fun p ↦ 0 := by
    apply h1
  simp at h2
  simp [h2] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 2 + p.2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (1) - (y-(-2)) * (-5) = 0) := by
  intro h
  simp_all [fderiv_const, fderiv_add, fderiv_sub, fderiv_pow, fderiv_mul, fderiv_id]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 - 2 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (355) - (y-(-5)) * (-1090) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 - 2 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-5:ℝ)) = 0 := by
    apply h
  have h2 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 - 2 * p.2 ^ 4 + p.2 ^ 3 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0 := by
    rw [h1]
    rfl
  simp [fderiv_const, fderiv_fpow, fderiv_sub, fderiv_neg, fderiv_mul] at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 - c) ((5:ℝ), (-1:ℝ)) (x-5, y-(-1)) = 0) → ((x-5) * (27) + (y-(-1)) * (-2) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 - c) ((5:ℝ), (-1:ℝ)) = 0 := by
    sorry
  have h2 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 3 * p.1 + p.2 ^ 2 - c) ((5:ℝ), (-1:ℝ)) (x-5, y-(-1)) = 0 := by
    sorry
  have h3 : (x-5) * (27) + (y-(-1)) * (-2) = 0 := by
    sorry
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - p.1 ^ 2 + 4 * p.1 + 3 * p.2 ^ 3 - c) ((-6:ℝ), (6:ℝ)) (x-(-6), y-6) = 0) → ((x-(-6)) * (448) + (y-6) * (324) = 0) := by
  intro h
  rw [fderiv_const_coord] at h
  norm_num at h
  linarith
  <;> apply Differentiable.differentiableAt
  <;> apply Differentiable.comp
  <;> apply Differentiable.const_mul
  <;> apply Differentiable.pow
  <;> apply Differentiable.id
  <;> apply Differentiable.sub
  <;> apply Differentiable.add
  <;> apply Differentiable.const
  <;> apply Differentiable.const_sub
  <;> apply Differentiable.const_smul
  <;> apply Differentiable.smul
  <;> apply Differentiable.neg
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const
  <;> apply Differentiable.mul_const

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) ((-4:ℝ), (6:ℝ)) (x-(-4), y-6) = 0) → ((x-(-4)) * (4) + (y-6) * (89) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) (-4, 6) =
      ContinuousLinearMap.smulRight (4 : ℝ →L[ℝ] ℝ) (1 : ℝ) +
        ContinuousLinearMap.smulRight (fun p : ℝ × ℝ => p.2 ^ 2) (1 : ℝ) +
        ContinuousLinearMap.smulRight (fun p : ℝ × ℝ => 5 * p.2) (1 : ℝ) := by
    sorry
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 + p.2 ^ 3 - 2 * p.2 ^ 2 + 5 * p.2 - c) (-4, 6) (x - (-4), y - 6) =
      (4:ℝ) * (x - (-4)) + (89:ℝ) * (y - 6) := by
    sorry
  have h3 : (4:ℝ) * (x - (-4)) + (89:ℝ) * (y - 6) = 0 := by
    sorry
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (5) + (y-(-2)) * (-85) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) = 0 := by
    apply is_independent_linear_of_fderiv_eq_zero h
  have h2 : ∀ u v : ℝ,
    ((fun p : ℝ × ℝ ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ∘ fun t ↦ (t, -2))
    = fun t ↦ t ^ 3 - t ^ 2 + 2 * (-2) ^ 4 - (-2) ^ 3 + (-2) ^ 2 - 5 * (-2) - c := by
    intro u v
    simp [Function.comp]
  have h3 : ∀ u v : ℝ,
    ((fun p : ℝ × ℝ ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ∘ fun t ↦ (-1, t))
    = fun t ↦ (-1) ^ 3 - (-1) ^ 2 + 2 * t ^ 4 - t ^ 3 + t ^ 2 - 5 * t - c := by
    intro u v
    simp [Function.comp]
  have h4 : ∀ u v : ℝ,
    ((fun p : ℝ × ℝ ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ∘ fun t ↦ (t, -2))
    = fun t ↦ t ^ 3 - t ^ 2 + 2 * (-2) ^ 4 - (-2) ^ 3 + (-2) ^ 2 - 5 * (-2) - c := by
    intro u v
    simp [Function.comp]
  have h5 : ∀ u v : ℝ,
    ((fun p : ℝ × ℝ ↦ p.1 ^ 3 - p.1 ^ 2 + 2 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ∘ fun t ↦ (-1, t))
    = fun t ↦ (-1) ^ 3 - (-1) ^ 2 + 2 * t ^ 4 - t ^ 3 + t ^ 2 - 5 * t - c := by
    intro u v
    simp [Function.comp]
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3 - c) ((-4:ℝ), (-1:ℝ)) (x-(-4), y-(-1)) = 0) → ((x-(-4)) * (-1101) + (y-(-1)) * (3) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 4 + 3 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 3 - c) ((-4, -1)) =
      (fun p : ℝ × ℝ => 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 + 3 * p.2 ^ 2) := by
    ext1
    fun_prop
    ring
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.2 - c) ((-1:ℝ), (4:ℝ)) (x-(-1), y-4) = 0) → ((x-(-1)) * (-8) - (y-4) * (4) = 0) := by
  intro h
  have h₀ : fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 ^ 2 - 4 * p.2 - c) (-1, 4) = 0 := h
  simp [fderiv_const, fderiv_sub, fderiv_mul, fderiv_id, fderiv_pow, fderiv_const, fderiv_sub, fderiv_mul, fderiv_id, fderiv_pow] at h₀
  have h₁ : (x - -1) * (-8) - (y - 4) * 4 = 0 := by linarith
  exact h₁

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (240) + (y-3) * (229) = 0) := by
  intro h
  let u := fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 2 * p.2 ^ 4 + p.2 ^ 3 - 3 * p.2 ^ 2 + 4 * p.2 - c) ((6:ℝ), (3:ℝ))
  let v := (x-6, y-3)
  have := congr_fun (h : u v = 0)
  simp at this
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - p.1 ^ 2 - p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((4:ℝ), (0:ℝ)) (x-4, y-0) = 0) → ((x-4) * (88) - (y-0) * (-1) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - p.1 ^ 2 - p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) (4, 0) = 0 := by
    apply h
  have h2 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - p.1 ^ 2 - p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) (4, 0) (x-4, y-0) = 0 := by
    rw [h1]
    simp
  have h3 : (x-4) * (88) - (y-0) * (-1) = 0 := by
    simp at h2
    linarith
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 2 * p.1 ^ 3 + 2 * p.1 ^ 2 + 4 * p.2 - c) ((-1:ℝ), (2:ℝ)) (x-(-1), y-2) = 0) → ((x-(-1)) * (-18) + (y-2) * (4) = 0) := by
  intro h
  simp [fderiv_const, fderiv_snd, fderiv_fst, fderiv_sub, fderiv_mul, fderiv_pow] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 5 * p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) ((4:ℝ), (2:ℝ)) (x-4, y-2) = 0) → ((x-4) * (55) - (y-2) * (185) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 5 * p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) (4, 2) =
    (55, 185) := by
    sorry
  have h2 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.1 ^ 2 - p.1 - 5 * p.2 ^ 4 - 2 * p.2 ^ 3 + p.2 ^ 2 - 5 * p.2 - c) (4, 2) (x-4, y-2) =
    (55) * (x-4) - (185) * (y-2) := by
    sorry
  have h3 : (55) * (x-4) - (185) * (y-2) = 0 := by
    sorry
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 2 * p.1 + 3 * p.2 ^ 4 - c) ((-6:ℝ), (1:ℝ)) (x-(-6), y-1) = 0) → ((x-(-6)) * (-1730) + (y-1) * (12) = 0) := by
  intro h
  rw [fderiv_sub, fderiv_const, fderiv_sub, fderiv_const, fderiv_mul, fderiv_mul, fderiv_pow, fderiv_pow] at h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 ^ 2 + 4 * p.2 ^ 2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (-126) + (y-6) * (48) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 2 + 4 * p.2 ^ 2 - c) (-3, 6) = fun p => 12 * p.1 ^ 2 * (p.1 - -3) + 48 * p.2 * (p.2 - 6) := by
    funext p
    simp
    ring
  simp at h
  have h2 : 12 * (-3) ^ 2 * (x + 3) + 48 * 6 * (y - 6) = 0 := by
    rw [h1] at h
    simp at h
    ring_nf at h ⊢
    linarith
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3 * p.2 - c) ((3:ℝ), (-4:ℝ)) (x-3, y-(-4)) = 0) → ((x-3) * (20) + (y-(-4)) * (-37) = 0) := by
  intro h
  simp [fderiv_const, Submodule.mem_bot, sub_eq_zero, add_assoc] at h
  simp [h, mul_comm, add_assoc, add_comm, add_left_comm, add_assoc, add_comm, add_left_comm]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((-2:ℝ), (-3:ℝ)) (x-(-2), y-(-3)) = 0) → ((x-(-2)) * (2) + (y-(-3)) * (-171) = 0) := by
  intro h
  simp only [fderiv_const, zero_apply, add_zero, zero_mul, zero_sub, mul_neg, neg_neg,
    mul_one, mul_zero, sub_zero, zero_add, neg_add_rev, neg_sub, neg_mul_eq_neg_mul] at h
  have : HasFDerivAt (fun p ↦ 2 * p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 - 3 * p.2 ^ 2 - c)
    (fun p ↦ !![2; -171]) (-2, -3) := by
    apply HasFDerivAt.const_add
    apply HasFDerivAt.sub
    · apply HasFDerivAt.pow
      apply HasFDerivAt_id
    · apply HasFDerivAt.sub
      · apply HasFDerivAt.mul_const
        apply HasFDerivAt.pow
        apply HasFDerivAt_id
      · apply HasFDerivAt.const_mul
        apply HasFDerivAt.pow
        apply HasFDerivAt_id
  simpa [ContinuousLinearMap.ext_iff] using this.fderiv

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2 - c) ((-5:ℝ), (5:ℝ)) (x-(-5), y-5) = 0) → ((x-(-5)) * (-8) + (y-5) * (1705) = 0) := by
  intro h
  have h' :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2 - c) (-5, 5) = 0 := by
    rw [h]
    rfl
  simp only [fderiv, ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.map_mul, ContinuousLinearMap.map_pow] at h'
  have h'' :
    (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2 - c)
      = fun p : ℝ × ℝ => p.1 ^ 2 + 2 * p.1 + 3 * p.2 ^ 4 + 3 * p.2 ^ 3 - 2 * p.2 ^ 2 := by
    ext1
    simp
  rw [h''] at h'
  simp only [Function.comp_apply, ContinuousLinearMap.coe_sub',
    ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_mul',
    ContinuousLinearMap.coe_pow'] at h'
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 2 * p.1 ^ 2 - 2 * p.1 - 5 * p.2 ^ 3 + 5 * p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (18) - (y-3) * (103) = 0) := by
  intro h
  have h' := congr_arg (fun x => x - 0) h
  simp at h'
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 2 * p.1 + 5 * p.2 ^ 2 - p.2 - c) ((4:ℝ), (-3:ℝ)) (x-4, y-(-3)) = 0) → ((x-4) * (22) + (y-(-3)) * (-31) = 0) := by
  intro h; simp_all [fderiv_const, fderiv_fst, fderiv_snd, fderiv_sub, fderiv_mul,
    fderiv_add, fderiv_pow]
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 2 * p.2 ^ 2 + p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (2) - (y-(-1)) * (-5) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 - 2 * p.2 ^ 2 + p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0 := h
  simp [fderiv_const, fderiv_sub, fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const] at h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 - c) ((4:ℝ), (-4:ℝ)) (x-4, y-(-4)) = 0) → ((x-4) * (253) + (y-(-4)) * (-24) = 0) := by
  intro h
  have h₁ : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 - c) (4, -4) =
    (fun p : ℝ × ℝ => 0) := by
    apply IsBoundedLinearMap.fderiv
    exact IsBoundedLinearMap.const_smul _ _
  have h₂ : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 3 + 2 * p.1 ^ 2 - 3 * p.1 + 3 * p.2 ^ 2 - c) (4, -4) (x - 4, y + 4) =
    (0 : ℝ × ℝ →L[ℝ] ℝ) (x - 4, y + 4) := by
    rw [h₁]
    rfl
  simp [h₂] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 ^ 2 - 4 * p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (0) - (y-5) * (4) = 0) := by
  intro h
  have h1 := h
  simp at h1
  simp
  ring_nf at h1 ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) ((0:ℝ), (4:ℝ)) (x-0, y-4) = 0) → ((x-0) * (-5) + (y-4) * (1069) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 3 * p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 4 - 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) ((0:ℝ), (4:ℝ)) =  fun (x,y) ↦ (-5,1069) := by
    sorry
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c) ((-5:ℝ), (6:ℝ)) (x-(-5), y-6) = 0) → ((x-(-5)) * (-329) - (y-6) * (65) = 0) := by
  intro h
  have h₀ :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2 - c)
      (⟨-5, 6⟩ : ℝ × ℝ) =
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2)
      (⟨-5, 6⟩ : ℝ × ℝ) := by
    congr
    ext1
    ring
  have h₁ :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2)
      (⟨-5, 6⟩ : ℝ × ℝ) (x - -5, y - 6) = 0 := by
    rw [h₀] at h
    exact h
  have h₂ :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 4 * p.1 - 5 * p.2 ^ 2 - 5 * p.2)
      (⟨-5, 6⟩ : ℝ × ℝ) (x - -5, y - 6) =
    (4 * (x + 5) ^ 3 - 12 * (x + 5) ^ 2, -10 * (y - 6)) := by
    rw [fderiv_eq_zero_iff_eq_const] at h₁
    simp [h₁]
    rfl
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 2 * p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (38) + (y-(-1)) * (12) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  ring_nf at h1 ⊢
  simp [h1]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 2 * p.1 ^ 2 + 5 * p.1 + 5 * p.2 ^ 2 + 3 * p.2 - c) ((-1:ℝ), (0:ℝ)) (x-(-1), y-0) = 0) → ((x-(-1)) * (12) + (y-0) * (3) = 0) := by
  intro h; simp_all [fderiv_const]
  -- ⊢ (x + 1) * 12 + y * 3 = 0
  <;> linarith
  <;> assumption
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith
  <;> simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - p.2 - c) ((1:ℝ), (-6:ℝ)) (x-1, y-(-6)) = 0) → ((x-1) * (2) - (y-(-6)) * (1) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 - p.2 - c) ((1:ℝ), (-6:ℝ)) (x-1, y-(-6)) = 0 := h
  have h2 : (2:ℝ) • (x-1, y-(-6)) = (2 * (x-1), 2 * (y-(-6))) := by simp [smul_prod]
  rw [h2] at h1
  have h3 : (2 * (x-1), 2 * (y-(-6))) = (x-1, y-(-6)) := by
    rw [← sub_eq_zero] at h1
    have h4 : (2:ℝ) • (x-1, y-(-6)) - (x-1, y-(-6)) = 0 := by simp [h1]
    have h5 : (2:ℝ) • (x-1, y-(-6)) - (x-1, y-(-6)) = ((2:ℝ) - 1) • (x-1, y-(-6)) := by
      simp [sub_smul]
    rw [h5] at h4
    have h6 : ((2:ℝ) - 1) • (x-1, y-(-6)) = 0 := by simp [h4]
    have h7 : (2:ℝ) - 1 = 1 := by norm_num
    rw [h7] at h6
    have h8 : (1:ℝ) • (x-1, y-(-6)) = (x-1, y-(-6)) := by simp
    rw [h8] at h6
    simp [h6]
  rw [h3] at h1
  simp [h1]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 3 * p.1 ^ 2 + p.1 - 2 * p.2 ^ 2 + 2 * p.2 - c) ((-4:ℝ), (-2:ℝ)) (x-(-4), y-(-2)) = 0) → ((x-(-4)) * (-535) - (y-(-2)) * (-10) = 0) := by
  intro h
  rw [fderiv_fun_comp] at h
  simp at h
  simp [mul_comm, mul_left_comm, mul_assoc] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 5 * p.1 ^ 3 + p.1 ^ 2 + 5 * p.1 + p.2 ^ 4 - p.2 ^ 3 - p.2 ^ 2 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (254) + (y-3) * (75) = 0) := by
  intro h
  simp_all only [fderiv_add, fderiv_sub, fderiv_const, fderiv_id, fderiv_pow, fderiv_mul,
    fderiv_comp, fderiv_smul, add_zero, sub_zero, zero_add, zero_sub, sub_self,
    mul_one, mul_zero, add_assoc, add_left_neg, add_right_neg, sub_eq_add_neg]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 4 * p.1 + p.2 ^ 2 + 4 * p.2 - c) ((-5:ℝ), (-3:ℝ)) (x-(-5), y-(-3)) = 0) → ((x-(-5)) * (-54) + (y-(-3)) * (-2) = 0) := by
  intro h
  simp [fderiv_eq_zero_iff_eq_zero] at h
  ring_nf at h
  ring_nf
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.1 + 2 * p.2 ^ 2 + 2 * p.2 - c) ((-5:ℝ), (4:ℝ)) (x-(-5), y-4) = 0) → ((x-(-5)) * (-29) + (y-4) * (18) = 0) := by
  intro h
  rw [fderiv_const_apply] at h
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 + p.1 ^ 3 + 2 * p.1 ^ 2 - p.1 - p.2 ^ 2 - 2 * p.2 - c) ((-1:ℝ), (5:ℝ)) (x-(-1), y-5) = 0) → ((x-(-1)) * (-22) - (y-5) * (12) = 0) := by
  intro h
  simp only [fderiv_const_apply, fderiv_add_apply, fderiv_mul_apply, fderiv_pow, fderiv_id'',
    fderiv_sub_apply, fderiv_const', sub_zero, zero_sub, sub_neg_eq_add, zero_mul, zero_add, zero_sub,
    neg_sub, neg_neg, neg_zero, add_zero] at h
  ring_nf at h ⊢
  simp [h]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) ((5:ℝ), (5:ℝ)) (x-5, y-5) = 0) → ((x-5) * (150) - (y-5) * (405) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 5 * p.2 ^ 3 - 3 * p.2 ^ 2 - c) (5, 5) =
    fun p ↦ 6 * p.1 ^ 2 - 3 * p.2 ^ 2 - 15 * p.2 := by
    apply hasFDerivAt_iff_hasDerivAt.mp
    apply HasFDerivAt.congr_of_eventuallyEq
    · apply HasFDerivAt.sub_const
      apply HasFDerivAt.sub_const
      apply HasFDerivAt.sub_const
      apply HasFDerivAt.const_mul
      apply HasFDerivAt.pow
      apply HasFDerivAt_id
      apply HasFDerivAt.const_mul
      apply HasFDerivAt.pow
      apply HasFDerivAt_id
      apply HasFDerivAt.const_mul
      apply HasFDerivAt.pow
      apply HasFDerivAt_id
    · rw [Filter.eventuallyEq_iff_exists_mem]
      use univ
      simp
  simp at h1
  simp [h1] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 - 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (-12) + (y-(-2)) * (43) = 0) := by
  intro h
  have h₁ : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 - 5 * p.2) ((-1, -2)) =
    fun p : ℝ × ℝ => 0 := by
    ext p
    have h₂ := h
    simp [fderiv_eq_zero_iff_eq_zero] at h₂
    have h₃ := h₂
    simp [fderiv_eq_zero_iff_eq_zero] at h₃
    simp [h₃, h]
  have h₄ : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 2 * p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 3 - 5 * p.2) ((-1, -2)) (x - -1, y - -2) =
    0 := by
    rw [h₁]
    simp
  simp at h₄
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 + p.2 ^ 2 + 5 * p.2 - c) ((2:ℝ), (-1:ℝ)) (x-2, y-(-1)) = 0) → ((x-2) * (25) + (y-(-1)) * (3) = 0) := by
  intro h
  simp [fderiv_const_apply, fderiv_add, fderiv_mul_const_field, fderiv_id', fderiv_const,
    fderiv_sub, fderiv_pow, fderiv_comp, fderiv_id, fderiv_fpow, fderiv_fpow_apply,
    fderiv_fpow, fderiv_fpow_apply, fderiv_fpow, fderiv_fpow_apply, fderiv_fpow,
    fderiv_fpow_apply, fderiv_fpow, fderiv_fpow_apply, fderiv_fpow, fderiv_fpow_apply] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 3 * p.2 - c) ((4:ℝ), (5:ℝ)) (x-4, y-5) = 0) → ((x-4) * (86) + (y-5) * (7) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 3 * p.2 - c) ((4:ℝ), (5:ℝ)) (x-4, y-5) = 0 := h
  have h2 : fderiv ℝ (fun p ↦ p.1 ^ 3 + 5 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 3 * p.2 - c) ((4:ℝ), (5:ℝ)) (x-4, y-5) = 0 := h1
  have h3 : (x-4) * (86) + (y-5) * (7) = 0 := by
    simp [fderiv_eq_zero_iff_eq_zero] at h2
    linarith
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 3 + 2 * p.2 ^ 2 - 3 * p.2 - c) ((-6:ℝ), (2:ℝ)) (x-(-6), y-2) = 0) → ((x-(-6)) * (1) + (y-2) * (17) = 0) := by
  intro h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (1:ℝ)) (x-0, y-1) = 0) → ((x-0) * (-4) + (y-1) * (9) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 2 - 4 * p.1 + 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (1:ℝ)) =
    LinearMap.mk₂ ℝ (fun p ↦ p.1 * (-4) + p.2 * (9)) (fun x y ↦ 0) (fun x y ↦ 0)
      (fun x y ↦ 0) (fun x y ↦ 0) := by
    rw [fderiv_eq_iff_eq_linearMap] at h
    exact h
  simp [h1] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (44) - (y-1) * (6) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 - c : ℝ))
    (2, 1) = fun p : ℝ × ℝ => (44 * p.1 - 6 * p.2 : ℝ) := by
    rw [fderiv_const_sub_apply, fderiv_add_apply, fderiv_sub_apply, fderiv_sub_apply, fderiv_add_apply,
      fderiv_add_apply, fderiv_pow_apply, fderiv_pow_apply, fderiv_pow_apply, fderiv_pow_apply, fderiv_const_apply,
      fderiv_const_apply, fderiv_id_apply, fderiv_id_apply]
    · simp
    · ring_nf
    · simp
    · ring_nf
  have h2 : (44 * (x - 2) - 6 * (y - 1) : ℝ) = 0 := by
    have h3 : fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 - c : ℝ))
        (2, 1) (x - 2, y - 1) = 0 := by
      simpa [h1] using h
    have h4 : fderiv ℝ (fun p : ℝ × ℝ => (5 * p.1 ^ 3 - 4 * p.1 ^ 2 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - p.2 - c : ℝ))
        (2, 1) (x - 2, y - 1) = fun p : ℝ × ℝ => (44 * p.1 - 6 * p.2 : ℝ) := by
      simp [h1]
    simpa [h4] using h3
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 4 * p.2 ^ 3 + p.2 - c) ((4:ℝ), (-1:ℝ)) (x-4, y-(-1)) = 0) → ((x-4) * (192) + (y-(-1)) * (13) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, Finset.sum_range_succ,
    Finset.sum_range_zero, Finset.sum_singleton, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_coe, ContinuousLinearMap.id_apply] at h1
  ring_nf at h1 ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * p.2 - c) ((-3:ℝ), (-3:ℝ)) (x-(-3), y-(-3)) = 0) → ((x-(-3)) * (-240) + (y-(-3)) * (-15) = 0) := by
  intro h
  have h' : fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 + 4 * p.1 ^ 2 + 3 * p.2 ^ 2 + 3 * p.2 - c) (-3, -3) = 0 := by
    apply h
  simp [fderiv_const_sub, fderiv_sub_const, fderiv_pow, fderiv_id, fderiv_const,
    fderiv_mul_const, fderiv_const_mul, fderiv_comp, fderiv_add_const, fderiv_sub_const,
    fderiv_pow, fderiv_id, fderiv_const, fderiv_mul_const, fderiv_const_mul, fderiv_comp,
    fderiv_add_const, fderiv_sub_const, fderiv_pow, fderiv_id, fderiv_const, fderiv_mul_const,
    fderiv_const_mul, fderiv_comp, fderiv_add_const, fderiv_sub_const, fderiv_pow, fderiv_id,
    fderiv_const, fderiv_mul_const, fderiv_const_mul, fderiv_comp, fderiv_add_const, fderiv_sub_const] at h'
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (17) + (y-(-3)) * (-24) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 4 * p.1 ^ 2 + p.1 + 4 * p.2 ^ 2 - c) (2, -3) = 0 := by
    -- The derivative is zero because the function is constant at the point (2, -3)
    -- The derivative of a constant function is zero
    rw [fderiv_zero_apply] at h
    exact h
  -- The derivative at (2, -3) is zero, so the function is constant in a neighborhood of (2, -3)
  -- Therefore, the function value at any point in a neighborhood of (2, -3) is the same as the function value at (2, -3)
  -- We can choose any point in a neighborhood of (2, -3), such as (x, y)
  -- Therefore, the function value at (x, y) is the same as the function value at (2, -3)
  -- This gives us the equation (x-2) * (17) + (y-(-3)) * (-24) = 0
  have h2 : ∀ x y : ℝ, (x - 2) * 17 + (y - (-3)) * (-24) = 0 := by
    intro x y
    rw [sub_eq_add_neg, sub_eq_add_neg]
    ring
  exact h2 x y

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) (x-3, y-1) = 0) → ((x-3) * (1) - (y-1) * (13) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) = 0 := by
    apply h
  have h2 : (x - 3) * 1 - (y - 1) * 13 = 0 := by
    simp at h1
    have h3 : (fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c) = fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c := by
      rfl
    simp [h3] at h1
    have h4 : fderiv ℝ (fun p ↦ p.1 - p.2 ^ 4 - 2 * p.2 ^ 2 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) = fun p ↦ 1 - 4 * 1 ^ 3 - 2 * 2 * 1 - 5 := by
      apply h1
    simp at h4
    have h5 : (x - 3) * 1 - (y - 1) * 13 = 0 := by
      linarith
    exact h5
  exact h2

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (4) - (y-3) * (432) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.1 ^ 2 + p.1 - 4 * p.2 ^ 4 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0 := h
  simp [fderiv_const_sub, fderiv_sub, fderiv_pow, fderiv_mul, fderiv_const_mul, fderiv_id] at h1
  simp [mul_comm] at h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 - p.1 ^ 2 + 4 * p.2 ^ 3 + 4 * p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (426) + (y-0) * (4) = 0) := by
  intro h
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 3 * p.1 + 4 * p.2 ^ 3 - 3 * p.2 ^ 2 + 5 * p.2 - c) ((-3:ℝ), (-1:ℝ)) (x-(-3), y-(-1)) = 0) → ((x-(-3)) * (-9) + (y-(-1)) * (23) = 0) := by
  intro h;
  have h₀ := h
  simp [fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.pi_apply, smul_eq_mul] at h₀
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 4 * p.2 ^ 3 - 4 * p.2 ^ 2 - c) ((-6:ℝ), (5:ℝ)) (x-(-6), y-5) = 0) → ((x-(-6)) * (-36) + (y-5) * (260) = 0) := by
  intro h
  simp only [fderiv_const, Pi.zero_apply, map_zero] at h
  simp_all only [add_zero, mul_zero, mul_one, zero_add, zero_sub, zero_mul, sub_zero]
  linarith [h]

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + 3 * p.2 - c) ((-3:ℝ), (-3:ℝ)) (x-(-3), y-(-3)) = 0) → ((x-(-3)) * (2) + (y-(-3)) * (3) = 0) := by
  intro h
  simp only [fderiv_const_apply, fderiv_add, fderiv_sub, fderiv_smul, fderiv_const, fderiv_id,
    fderiv_mul, ContinuousLinearMap.id_comp, ContinuousLinearMap.smulRight_apply, mul_one, mul_zero,
    sub_zero, zero_mul, add_zero, sub_self, zero_sub, sub_neg_eq_add, add_sub_cancel, sub_add_cancel,
    mul_smul, mul_assoc, mul_comm, mul_left_comm] at h
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) ((-3:ℝ), (-6:ℝ)) (x-(-3), y-(-6)) = 0) → ((x-(-3)) * (27) + (y-(-6)) * (-10) = 0) := by
  intro h
  have h1 := h
  rw [fderiv_eq_zero_iff_eq_const] at h1
  have h2 := h1
  simp at h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((1:ℝ), (5:ℝ)) (x-1, y-5) = 0) → ((x-1) * (3) + (y-5) * (885) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((1:ℝ), (5:ℝ)) = 0 := by
    apply h
  have h2 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 5 * p.1 + p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 - c) ((1:ℝ), (5:ℝ)) (x-1, y-5) = 0 := by
    apply h
  have h3 : (x-1) * (3) + (y-5) * (885) = 0 := by
    linarith [h2, h1]
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + 2 * p.1 - 2 * p.2 ^ 3 - 2 * p.2 ^ 2 - 3 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (38) - (y-(-5)) * (133) = 0) := by
  intro h; simp [fderiv_const_apply] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 - c) ((5:ℝ), (-4:ℝ)) (x-5, y-(-4)) = 0) → ((x-5) * (30) + (y-(-4)) * (-116) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 - c) ((5:ℝ), (-4:ℝ)) = 0 := by
    apply hasFDerivAt_of_hasDerivAt_real (fun p ↦ 3 * p.1 ^ 2 + p.2 ^ 4 + 3 * p.2 ^ 3 - 4 * p.2 - c) ((5:ℝ), (-4:ℝ))
    rw [hasDerivAt_iff_hasFDerivAt_real]
    apply HasDerivAt.const_add
    apply HasDerivAt.add
    apply HasDerivAt.const_mul
    apply HasDerivAt.pow
    apply hasDerivAt_id
    apply HasDerivAt.pow
    apply hasDerivAt_id
    apply HasDerivAt.const_mul
    apply hasDerivAt_id
    apply HasDerivAt.const_sub
    apply hasDerivAt_id
  simp [h1] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((6:ℝ), (-2:ℝ)) (x-6, y-(-2)) = 0) → ((x-6) * (540) + (y-(-2)) * (57) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((6:ℝ), (-2:ℝ)) =
    (fun p ↦ (540) * p.1 + (57) * p.2) := by
    rw [fderiv_add, fderiv_const, fderiv_mul, fderiv_pow, fderiv_pow, fderiv_id, fderiv_id]
    all_goals simp
    <;> norm_num
  rw [h1] at h
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - 2 * p.2 ^ 3 - 3 * p.2 - c) ((-1:ℝ), (0:ℝ)) (x-(-1), y-0) = 0) → ((x-(-1)) * (-2) - (y-0) * (3) = 0) := by
  intro h
  have h2 := h
  rw [fderiv_iff_hasFDerivAt] at h2
  have h3 := h2.1
  simp at h3
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 - 2 * p.2 - c) ((-2:ℝ), (5:ℝ)) (x-(-2), y-5) = 0) → ((x-(-2)) * (3) + (y-5) * (8) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 + p.2 ^ 2 - 2 * p.2 - c) ((-2:ℝ), (5:ℝ)) = fun p ↦ 3 • p.1 + 8 • p.2 := by
    apply fderiv_const_sub
    apply fderiv_add
    apply fderiv_const_mul
    apply fderiv_id
    apply fderiv_pow
    simp
  have h2 : (fun p ↦ 3 • p.1 + 8 • p.2) (x-(-2), y-5) = 0 := by
    simp_all
  simp_all
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 4 * p.2 ^ 4 - 3 * p.2 ^ 2 + 2 * p.2 - c) ((3:ℝ), (4:ℝ)) (x-3, y-4) = 0) → ((x-3) * (2) - (y-4) * (1046) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 2 * p.1 - 4 * p.2 ^ 4 - 3 * p.2 ^ 2 + 2 * p.2 - c) (3, 4) = 0 := by
    simpa [fderiv_const_sub_apply, fderiv_add_const_apply, fderiv_sub_const_apply, fderiv_const_apply, fderiv_id_apply] using h
  have h2 : (x - 3) * 2 - (y - 4) * 1046 = 0 := by
    simpa [fderiv_const_sub_apply, fderiv_add_const_apply, fderiv_sub_const_apply, fderiv_const_apply, fderiv_id_apply] using h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (-4:ℝ)) (x-0, y-(-4)) = 0) → ((x-0) * (0) + (y-(-4)) * (177) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) ((0 : ℝ), (-4 : ℝ))
    = fun p : ℝ × ℝ => (0 : ℝ) * p.1 + (177 : ℝ) * p.2 := by
    ext p
    have h2 : fderiv ℝ (fun p : ℝ × ℝ => 5 * p.1 ^ 2 + 3 * p.2 ^ 3 - 4 * p.2 ^ 2 + p.2 - c) ((0 : ℝ), (-4 : ℝ))
      = fun p : ℝ × ℝ => (0 : ℝ) * p.1 + (177 : ℝ) * p.2 := by
      rw [fderiv_const_sub_apply]
      simp
      apply HasFDerivAt.fderiv
      apply HasFDerivAt.const_mul (HasFDerivAt.id)
      apply HasFDerivAt.const_add
      apply HasFDerivAt.neg
      apply HasFDerivAt.pow
      apply HasFDerivAt.const_mul (HasFDerivAt.id)
      apply HasFDerivAt.const_add
      apply HasFDerivAt.neg
      apply HasFDerivAt.pow
    rw [h2]
  rw [h1] at h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 5 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 - 5 * p.2 - c) ((0:ℝ), (-1:ℝ)) (x-0, y-(-1)) = 0) → ((x-0) * (-5) - (y-(-1)) * (14) = 0) := by
  intro h
  have h₁ := h
  simp_all
  have h₂ := h₁
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 4 * p.2 ^ 2 - c) ((4:ℝ), (-5:ℝ)) (x-4, y-(-5)) = 0) → ((x-4) * (3) - (y-(-5)) * (-40) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 - 4 * p.2 ^ 2 - c) ((4:ℝ), (-5:ℝ)) = fun p ↦ (3:ℝ) * p.1 - (-40:ℝ) * p.2 := by
    rw [fderiv_sub, fderiv_const, fderiv_sub, fderiv_const] <;>
    simp [fderiv_id, fderiv_const, fderiv_mul_const_field, fderiv_pow_field, fderiv_id', fderiv_const']
  simp [h1] at h
  ring_nf at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 4 * p.2 ^ 3 - c) ((-3:ℝ), (-6:ℝ)) (x-(-3), y-(-6)) = 0) → ((x-(-3)) * (33) - (y-(-6)) * (432) = 0) := by
  intro h
  have h₀ :
    fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 4 * p.2 ^ 3 - c) (-3, -6) = fun ⟨x, y⟩ ↦ 0 := by
    ext1
    simp_all
  have h₁ :
    fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 4 * p.2 ^ 3 - c) (-3, -6) (x - (-3), y - (-6)) = 0 := by
    rw [h₀]
    simp
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2 - c) ((-5:ℝ), (-4:ℝ)) (x-(-5), y-(-4)) = 0) → ((x-(-5)) * (-35) - (y-(-4)) * (164) = 0) := by
  intro h
  have h' : fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - 5 * p.1 - 3 * p.2 ^ 3 + 2 * p.2 ^ 2 - 4 * p.2 - c) ((-5:ℝ), (-4:ℝ)) = fun _ ↦ 0 := by
    rw [fderiv_const]
  have h'' : (fun _ ↦ 0 : ℝ →L[ℝ] ℝ) = 0 := by rfl
  rw [h''] at h'
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2 - c) ((-1:ℝ), (4:ℝ)) (x-(-1), y-4) = 0) → ((x-(-1)) * (-3) + (y-4) * (286) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 4 + 2 * p.1 ^ 3 - 5 * p.1 + p.2 ^ 4 + 4 * p.2 ^ 2 - 2 * p.2 - c) ((-1:ℝ), (4:ℝ)) = fun p ↦ (4 * p.1 ^ 3 + 6 * p.1 ^ 2 - 5) • (fun _ ↦ (1:ℝ)) + (fun p ↦ (4 * p.2 ^ 3 + 8 * p.2 ^ 2 - 2)) := by
    sorry
  have h2 : (fun p ↦ (4 * p.1 ^ 3 + 6 * p.1 ^ 2 - 5) • (fun _ ↦ (1:ℝ)) + (fun p ↦ (4 * p.2 ^ 3 + 8 * p.2 ^ 2 - 2))) (x-(-1), y-4) = 0 := by
    sorry
  have h3 : (x-(-1)) * (-3) + (y-4) * (286) = 0 := by
    sorry
  exact h3

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (45) + (y-(-5)) * (-2582) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) (6, -5) =
    (fun p ↦ 3 * p.1 ^ 2 - 10 * p.1 - 3 + 20 * p.2 ^ 3 - 3 * p.2 ^ 2 + 3) := by
    apply fderiv_comp (g := fun p ↦ p.1) (f := fun p ↦ p.2)
    simp
    apply fderiv_id
    apply fderiv_const
  have h2 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 5 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 4 - p.2 ^ 3 + p.2 ^ 2 + 3 * p.2) (6, -5) (x - 6, y - (-5)) =
    3 * (x - 6) ^ 2 - 10 * (x - 6) - 3 + 20 * (y - (-5)) ^ 3 - 3 * (y - (-5)) ^ 2 + 3 := by
    rw [h1]
    simp
    apply fderiv_const
  rw [h2] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + 4 * p.2 ^ 2 + p.2 - c) ((0:ℝ), (5:ℝ)) (x-0, y-5) = 0) → ((x-0) * (2) + (y-5) * (41) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_eq_zero_of_eq] at h1
  have h2 := h1
  simp at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 - 5 * p.2 ^ 2 - c) ((-5:ℝ), (1:ℝ)) (x-(-5), y-1) = 0) → ((x-(-5)) * (-11) - (y-1) * (10) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 - 5 * p.2 ^ 2 - c) ((-5:ℝ), (1:ℝ)) = fun v ↦ (2 * v.1 - v.1) • (1:ℝ) - (0:ℝ) • v.2 := by
    sorry
  have h2 : fderiv ℝ (fun p ↦ p.1 ^ 2 - p.1 - 5 * p.2 ^ 2 - c) ((-5:ℝ), (1:ℝ)) (x - (-5), y - 1) = (x - (-5)) * (-11) - (y - 1) * (10) := by
    sorry
  have h3 : (2 * (x - (-5)) - (x - (-5))) • (1:ℝ) - (0:ℝ) • (y - 1) = 0 := by
    sorry
  have h4 : (x - (-5)) * (-11) - (y - 1) * (10) = 0 := by
    sorry
  exact h4

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 3 * p.1 - 4 * p.2 ^ 4 + 2 * p.2 ^ 3 + 5 * p.2 ^ 2 + 3 * p.2 - c) ((6:ℝ), (6:ℝ)) (x-6, y-6) = 0) → ((x-6) * (15) - (y-6) * (3177) = 0) := by
  intro h
  rw [fderiv_iff_hasFDerivAt] at h
  simp only [Function.hasFDerivAt_iff_hasDerivAt, Function.hasDerivAt_iff_tendsto_slope,
    slope_fun_def, sub_eq_add_neg, neg_add_rev, neg_mul, neg_neg, mul_neg, neg_sub] at h
  have h1 := h.1
  have h2 := h.2
  norm_num at h1
  norm_num at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - 3 * p.2 ^ 2 + p.2 - c) ((2:ℝ), (5:ℝ)) (x-2, y-5) = 0) → ((x-2) * (2) - (y-5) * (29) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 - 3 * p.2 ^ 2 + p.2 - c) ((2:ℝ), (5:ℝ)) = fun p ↦ 2 - 3 * 2 * p.2 + 1 := by
    apply fderiv_const_sub
    apply fderiv_const_add
    apply fderiv_mul
    apply fderiv_const_sub
    apply fderiv_const_add
    apply fderiv_id
    apply fderiv_id
  rw [h1] at h
  simp at h
  ring_nf at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.1 + 2 * p.2 ^ 4 + 2 * p.2 ^ 3 - 4 * p.2 ^ 2 - 5 * p.2 - c) ((5:ℝ), (-5:ℝ)) (x-5, y-(-5)) = 0) → ((x-5) * (18) + (y-(-5)) * (-815) = 0) := by
  intro h
  have h₁ := h
  simp only [fderiv_const_apply, fderiv_add_const_apply, fderiv_sub_const_apply,
    fderiv_mul_const_apply, fderiv_pow_apply, fderiv_id'', fderiv_const',
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, mul_one, mul_zero, sub_zero, zero_sub, add_zero] at h₁
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) (x-3, y-1) = 0) → ((x-3) * (3) - (y-1) * (5) = 0) := by
  intro h
  have : fderiv ℝ (fun p ↦ 3 * p.1 - 5 * p.2 - c) ((3:ℝ), (1:ℝ)) = fun _ ↦ 0 := by
    rw [fderiv_const_sub_apply (fun p ↦ 3 * p.1 - 5 * p.2) ((3:ℝ), (1:ℝ))]
    rw [fderiv_sub_apply (fun x ↦ 3 * x) (fun x ↦ 5 * x) ((3:ℝ), (1:ℝ))]
    rw [fderiv_const_mul_apply 3 (fun x ↦ x) ((3:ℝ), (1:ℝ))]
    rw [fderiv_id_apply (3:ℝ), fderiv_const_mul_apply 5 (fun x ↦ x) ((3:ℝ), (1:ℝ))]
    rw [fderiv_id_apply (1:ℝ)]
    simp
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 + 3 * p.1 - 3 * p.2 ^ 4 - p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (1:ℝ)) (x-2, y-1) = 0) → ((x-2) * (11) - (y-1) * (12) = 0) := by
  intro h
  simp_all [fderiv_const]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2 - c) ((-2:ℝ), (1:ℝ)) (x-(-2), y-1) = 0) → ((x-(-2)) * (-19) + (y-1) * (23) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2 - c) ((-2:ℝ), (1:ℝ)) = 0 := by
    simpa [h] using h
  have h2 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 + 4 * p.2 ^ 2 - c) ((-2:ℝ), (1:ℝ)) (x-(-2), y-1) = 0 := by
    rw [h1]
    simp
  simp at h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) ((-6:ℝ), (5:ℝ)) (x-(-6), y-5) = 0) → ((x-(-6)) * (-37) - (y-5) * (33) = 0) := by
  intro h
  have h1 := h
  have h2 := fderiv_const_apply ℝ (-6) (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) (x-(-6), y-5)
  have h3 := fderiv_const_apply ℝ 5 (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) (x-(-6), y-5)
  have h4 := fderiv_const_apply ℝ 0 (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) (x-(-6), y-5)
  have h5 := fderiv_const_apply ℝ 0 (fun p ↦ 3 * p.1 ^ 2 - p.1 - 3 * p.2 ^ 2 - 3 * p.2 - c) (x-(-6), y-5)
  simp at h1 h2 h3 h4 h5
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 - c) ((3:ℝ), (-4:ℝ)) (x-3, y-(-4)) = 0) → ((x-3) * (35) - (y-(-4)) * (4) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 - c) ((3:ℝ), (-4:ℝ)) (x-3, y-(-4)) = 0 := h
  have h2 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + 5 * p.1 - 4 * p.2 - c) ((3:ℝ), (-4:ℝ)) =
    ContinuousLinearMap.smulRight (ContinuousLinearMap.add (ContinuousLinearMap.smulRight (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) 5) 5) (ContinuousLinearMap.smulRight (ContinuousLinearMap.neg (ContinuousLinearMap.id ℝ ℝ)) 4)) (fun _ ↦ -c) := by
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.add
    apply HasFDerivAt.smul_const
    apply HasFDerivAt.pow
    exact hasFDerivAt_id ℝ
    apply HasFDerivAt.smul_const
    exact hasFDerivAt_id ℝ
    apply HasFDerivAt.neg
    apply HasFDerivAt.smul_const
    exact hasFDerivAt_id ℝ
  rw [h2] at h1
  simp at h1
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 - p.2 ^ 3 - 3 * p.2 - c) ((-3:ℝ), (-2:ℝ)) (x-(-3), y-(-2)) = 0) → ((x-(-3)) * (81) - (y-(-2)) * (15) = 0) := by
  intro h
  have h₁ : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 ^ 3 - p.2 ^ 3 - 3 * p.2 - c) (-3, -2) =
    fun p : ℝ × ℝ => 0 := by
    rw [fderiv_const_apply]
  have h₂ := congr_fun h₁ (x + 3, y + 2)
  have h₃ := congr_fun h₁ (x, y)
  simp at h₂ h₃
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 3 + 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 - 3 * p.2 - c) ((-3:ℝ), (-1:ℝ)) (x-(-3), y-(-1)) = 0) → ((x-(-3)) * (106) + (y-(-1)) * (-7) = 0) := by
  intro h
  simp only [fderiv_const, fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_comp,
    fderiv_prod_mk, fderiv_const_apply, fderiv_id', fderiv_sub, fderiv_pow, fderiv_id,
    fderiv_const, fderiv_add, fderiv_mul, fderiv_comp, fderiv_prod_mk, fderiv_const_apply,
    fderiv_id', fderiv_sub] at h
  simp_all [fderiv_const, fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_comp,
    fderiv_prod_mk, fderiv_const_apply, fderiv_id', fderiv_sub, fderiv_pow, fderiv_id,
    fderiv_const, fderiv_add, fderiv_mul, fderiv_comp, fderiv_prod_mk, fderiv_const_apply,
    fderiv_id', fderiv_sub]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.2 - c) ((-3:ℝ), (0:ℝ)) (x-(-3), y-0) = 0) → ((x-(-3)) * (30) + (y-0) * (5) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 4 * p.1 ^ 2 + 5 * p.2 - c) ((-3:ℝ), (0:ℝ)) = fun x ↦ 0 := by
    apply fderiv_const_of_mem
    intro x
    simp
    ring
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 5 * p.1 + 2 * p.2 - c) ((-3:ℝ), (6:ℝ)) (x-(-3), y-6) = 0) → ((x-(-3)) * (-1) + (y-6) * (2) = 0) := by
  intro h
  simp [fderiv_const, fderiv_add, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const', fderiv_sub,
    fderiv_comp, fderiv_neg, fderiv_mul_const] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 4 * p.1 + 4 * p.2 - c) ((1:ℝ), (-6:ℝ)) (x-1, y-(-6)) = 0) → ((x-1) * (13) + (y-(-6)) * (4) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 4 * p.1 + 4 * p.2 - c) ((1:ℝ), (-6:ℝ)) = fun p ↦ (13:ℝ) * p.1 + (4:ℝ) * p.2 := by
    rw [fderiv_sub, fderiv_const, fderiv_add, fderiv_add, fderiv_mul, fderiv_mul,
      fderiv_pow, fderiv_pow, fderiv_id, fderiv_id, fderiv_const, fderiv_const]
    · ring
    · exact differentiableAt_id
    · exact differentiableAt_const _
    · exact differentiableAt_id
    · exact differentiableAt_const _
    · exact differentiableAt_id
    · exact differentiableAt_const _
    · exact differentiableAt_id
    · exact differentiableAt_const _
    · exact differentiableAt_id
    · exact differentiableAt_const _
    · exact differentiableAt_id
    · exact differentiableAt_const _
  simp only [h1] at h
  simp only [h, mul_sub, mul_one, mul_neg, mul_zero, sub_zero, neg_mul, neg_neg, zero_mul, zero_sub,
    sub_neg_eq_add, add_zero, zero_add, mul_comm, mul_left_comm, mul_assoc] at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 4 + 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 3 * p.1 + 5 * p.2 ^ 3 - c) ((3:ℝ), (3:ℝ)) (x-3, y-3) = 0) → ((x-3) * (528) + (y-3) * (135) = 0) := by
  intro h
  simp only [fderiv_const, Pi.smul_apply, smul_zero, mul_zero, sub_zero, zero_add, mul_one] at h
  ring_nf at h
  simp_all only [mul_comm, mul_left_comm, mul_assoc, mul_one, mul_zero, add_zero, sub_zero]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 4 - 5 * p.1 ^ 3 - 5 * p.1 ^ 2 - 5 * p.1 - 5 * p.2 - c) ((-5:ℝ), (-5:ℝ)) (x-(-5), y-(-5)) = 0) → ((x-(-5)) * (-1330) - (y-(-5)) * (5) = 0) := by
  intro h
  have h₀ := h
  simp [fderiv_const] at h₀
  have h₁ := h₀
  simp [fderiv_const] at h₁
  have h₂ := h₁
  simp [fderiv_const] at h₂
  have h₃ := h₂
  simp [fderiv_const] at h₃
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + 3 * p.2 - c) ((-4:ℝ), (2:ℝ)) (x-(-4), y-2) = 0) → ((x-(-4)) * (-39) + (y-2) * (3) = 0) := by
  intro h
  simp [fderiv_const_apply, fderiv_add_const, fderiv_mul_const, fderiv_add_const, fderiv_const_apply] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 - 5 * p.2 ^ 2 - c) ((6:ℝ), (-5:ℝ)) (x-6, y-(-5)) = 0) → ((x-6) * (3) - (y-(-5)) * (-50) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => 3 * p.1 - 5 * p.2 ^ 2 - c) ((6, -5)) = fun p : ℝ × ℝ => (3 : ℝ) • p.1 - (5 : ℝ) • p.2 ^ 2 := by
    funext p
    rw [fderiv_const_sub_apply]
    simp only [fderiv_const_apply, fderiv_sub, fderiv_mul, fderiv_id'', fderiv_const', fderiv_snd', fderiv_fst',
      fderiv_of_mem_pi, ne_eq, map_sub, map_mul, map_of_mem_pi, map_add, map_pow, of_eq_true]
    rfl
  simp only [h1, Function.comp_apply, sub_eq_zero] at h
  simp only [mul_sub, mul_one, mul_neg, mul_add, sub_eq_zero] at h
  ring_nf at h
  exact h

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + 5 * p.2 ^ 2 - c) ((2:ℝ), (6:ℝ)) (x-2, y-6) = 0) → ((x-2) * (1) + (y-6) * (60) = 0) := by
  intro h
  have h1 := h
  simp only [fderiv_const, fderiv_add, fderiv_snd, fderiv_fst, fderiv_mul, fderiv_id, fderiv_const,
    fderiv_comp, fderiv_pow, fderiv_sub, fderiv_id, fderiv_const] at h1
  ring_nf at h1 ⊢
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 4 * p.2 ^ 2 + p.2 - c) ((2:ℝ), (3:ℝ)) (x-2, y-3) = 0) → ((x-2) * (28) + (y-3) * (25) = 0) := by
  intro h
  simp_all [fderiv_const]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 - 4 * p.2 ^ 4 + 5 * p.2 ^ 3 + p.2 ^ 2 + p.2 - c) ((0:ℝ), (6:ℝ)) (x-0, y-6) = 0) → ((x-0) * (0) - (y-6) * (2903) = 0) := by
  intro h
  simp at h
  have h := h
  ring_nf at h ⊢
  nlinarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + 2 * p.1 + p.2 ^ 2 + p.2 - c) ((3:ℝ), (-1:ℝ)) (x-3, y-(-1)) = 0) → ((x-3) * (8) + (y-(-1)) * (-1) = 0) := by
  intro h
  simp [fderiv_const_apply, fderiv_add_apply, fderiv_mul_apply, fderiv_id_apply, fderiv_comp,
    fderiv_pow, fderiv_sub_apply, fderiv_const_apply, fderiv_id_apply] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 4 - 5 * p.2 ^ 2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) = 0) → ((x-5) * (19) + (y-4) * (216) = 0) := by
  intro h
  simp [fderiv_within_of_open, isOpen_Ioi, Ioi_mem_nhds] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 2 - p.1 - 4 * p.2 ^ 3 + 4 * p.2 ^ 2 - 2 * p.2 - c) ((4:ℝ), (4:ℝ)) (x-4, y-4) = 0) → ((x-4) * (31) - (y-4) * (162) = 0) := by
  intro h
  simp [fderiv, ContinuousLinearMap] at h
  have h₁ := h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.2 ^ 3 - p.2 - c) ((5:ℝ), (3:ℝ)) (x-5, y-3) = 0) → ((x-5) * (300) - (y-3) * (136) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.2 ^ 3 - p.2 - c) (5, 3) =
    (fun p ↦ (120 * p.1 ^ 2 - 45 * p.2 ^ 2 - 1) : ℝ × ℝ → ℝ) := by
    sorry
  have h2 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.2 ^ 3 - p.2 - c) (5, 3) (x - 5, y - 3) = 0 := by
    rw [h1] at h
    simp_all
  have h3 : 120 * (x - 5) ^ 2 - 45 * (y - 3) ^ 2 - 1 = 0 := by
    apply congr_fun h2
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 - p.2 ^ 4 - 3 * p.2 ^ 2 - c) ((3:ℝ), (-6:ℝ)) (x-3, y-(-6)) = 0) → ((x-3) * (2) - (y-(-6)) * (-900) = 0) := by
  intro h
  simp [fderiv_const, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const,
    fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id,
    fderiv_const, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id,
    fderiv_const, fderiv_sub, fderiv_mul, fderiv_pow, fderiv_id] at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 + 4 * p.2 - c) ((5:ℝ), (-5:ℝ)) (x-5, y-(-5)) = 0) → ((x-5) * (76) - (y-(-5)) * (296) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 + p.1 - 4 * p.2 ^ 3 + 4 * p.2 - c) ((5:ℝ), (-5:ℝ)) (x-5, y-(-5)) = 0 := h
  simp [fderiv_const] at h1
  ring_nf at h1 ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 - p.2 ^ 2 + 4 * p.2 - c) ((3:ℝ), (0:ℝ)) (x-3, y-0) = 0) → ((x-3) * (1) - (y-0) * (-4) = 0) := by
  intro h
  have h₁ := h
  simp [fderiv_eq_zero_iff_eq_zero] at h₁
  norm_num at h₁
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 3 * p.1 ^ 3 + 3 * p.1 ^ 2 - 2 * p.1 + p.2 ^ 2 - 4 * p.2 - c) ((6:ℝ), (3:ℝ)) (x-6, y-3) = 0) → ((x-6) * (358) + (y-3) * (2) = 0) := by
  intro h
  simp [fderiv] at h
  have h' := h
  simp [h']
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - p.1 ^ 2 - 5 * p.1 + 5 * p.2 ^ 2 - 5 * p.2 - c) ((2:ℝ), (-1:ℝ)) (x-2, y-(-1)) = 0) → ((x-2) * (3) + (y-(-1)) * (-15) = 0) := by
  intro h
  have h' := h
  rw [fderiv_eq_zero_iff_eq] at h'
  simp at h'
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 + 2 * p.2 - c) ((-3:ℝ), (-5:ℝ)) (x-(-3), y-(-5)) = 0) → ((x-(-3)) * (108) + (y-(-5)) * (2) = 0) := by
  intro h
  have h' := congr_arg (fun x ↦ x / 3) h
  simp at h'
  ring_nf at h'
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) ((3:ℝ), (6:ℝ)) (x-3, y-6) = 0) → ((x-3) * (59) - (y-6) * (516) = 0) := by
  intro h
  have h1 := h
  simp [fderiv_const] at h1
  have h2 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 3 + 5 * p.1 - 5 * p.2 ^ 3 + 2 * p.2 ^ 2 - c) ((3:ℝ), (6:ℝ)) = 0 := by
    ext
    simp_all
    <;> ring_nf
    <;> simp_all
  simp_all
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.1 - 3 * p.2 ^ 4 - 5 * p.2 ^ 3 - 5 * p.2 - c) ((-2:ℝ), (-5:ℝ)) (x-(-2), y-(-5)) = 0) → ((x-(-2)) * (-10) - (y-(-5)) * (-1120) = 0) := by
  intro h
  have h := h
  simp [fderiv_const] at h
  ring_nf at h ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 4 - 4 * p.1 ^ 3 + 2 * p.2 ^ 3 - c) ((2:ℝ), (-6:ℝ)) (x-2, y-(-6)) = 0) → ((x-2) * (112) + (y-(-6)) * (216) = 0) := by
  intro h
  simp_all [fderiv_const]
  ring
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (-3:ℝ)) (x-2, y-(-3)) = 0) → ((x-2) * (1) + (y-(-3)) * (-193) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 + p.2 ^ 4 - 3 * p.2 ^ 3 + p.2 ^ 2 + 2 * p.2 - c) ((2:ℝ), (-3:ℝ)) = fun _ ↦ 0 := by
    rw [fderiv_const_sub_apply]
    simp
  have h2 := congr_fun h1 (x-2, y-(-3))
  have h3 := h2
  simp at h3
  ring_nf at h3
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) (x-(-1), y-(-2)) = 0) → ((x-(-1)) * (-9) + (y-(-2)) * (-35) = 0) := by
  intro h
  have h1 := h
  have h2 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 + p.1 + p.2 ^ 4 + 2 * p.2 ^ 2 + 5 * p.2 - c) ((-1:ℝ), (-2:ℝ)) =
    fun p ↦ (5 * (2 * (-1)) + 1 + 4 * (-2) ^ 3 + 2 * (2 * (-2)) + 5) • p := by
    funext p
    simp [fderiv, hasFDerivAt_iff_hasDerivAt, hasDerivAt_iff_tendsto_slope]
    ring_nf
  have h3 : (5 * (2 * (-1)) + 1 + 4 * (-2) ^ 3 + 2 * (2 * (-2)) + 5) = -9 := by norm_num
  have h4 : (5 * (2 * (-2)) + 1 + 4 * (-1) ^ 3 + 2 * (2 * (-1)) + 5) = -35 := by norm_num
  simp_all only [h3, h4, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one, zero_mul,
    mul_neg, mul_assoc]
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 2 - p.2 - c) ((3:ℝ), (-5:ℝ)) (x-3, y-(-5)) = 0) → ((x-3) * (27) + (y-(-5)) * (-21) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 5 * p.1 ^ 2 - 3 * p.1 + 2 * p.2 ^ 2 - p.2 - c) ((3:ℝ), (-5:ℝ)) = fun p ↦ 0 := by
    rw [fderiv_const]
  have h2 : (fun p ↦ 0) (x-3, y-(-5)) = 0 := by
    simp
  have h3 : 0 = 0 := by
    rfl
  have h4 : (x-3) * (27) + (y-(-5)) * (-21) = 0 := by
    linarith
  simp_all

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) = 0) → ((x-5) * (19) + (y-4) * (9) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) =
    LinearMap.toSpanSingleton ℝ ℝ 0 := by
    rw [h]
    exact LinearMap.toSpanSingleton_zero ℝ ℝ
  have h2 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) =
    0 := by
    rw [h1]
    exact LinearMap.map_zero _
  have h3 : (x-5, y-4) ∈
    (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ⁻¹' {0} := by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    linarith
  have h4 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (x-5, y-4) =
    (x-5, y-4).fst • fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (1,0) +
    (x-5, y-4).snd • fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (0,1) := by
    rw [h1]
    exact LinearMap.toSpanSingleton_apply ℝ ℝ 0 (x-5, y-4)
  have h5 : (x-5, y-4).fst • fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (1,0) +
    (x-5, y-4).snd • fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - p.1 + p.2 ^ 2 + p.2 - c) ((5:ℝ), (4:ℝ)) (0,1) =
    0 := by
    rw [h4] at h2
    exact h2
  have h6 : (x-5) * (19) + (y-4) * (9) = 0 := by
    linarith
  exact h6

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.2 ^ 3 - c) ((0:ℝ), (2:ℝ)) (x-0, y-2) = 0) → ((x-0) * (0) - (y-2) * (24) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 2 * p.1 ^ 2 - 2 * p.2 ^ 3 - c) ((0:ℝ), (2:ℝ)) = fun p ↦ 4 * p.1 - 24 * p.2 := by
    rw [fderiv_sub, fderiv_const, fderiv_sub, fderiv_const, fderiv_mul, fderiv_pow,
      fderiv_id, fderiv_mul, fderiv_pow, fderiv_id, fderiv_const, fderiv_const]
    all_goals simp
  rw [h1] at h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + p.2 - c) ((-5:ℝ), (2:ℝ)) (x-(-5), y-2) = 0) → ((x-(-5)) * (352) + (y-2) * (21) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ 4 * p.1 ^ 3 - 5 * p.1 ^ 2 + 2 * p.1 + 5 * p.2 ^ 2 + p.2 - c) ((-5:ℝ), (2:ℝ)) =
    fun p ↦ (352:ℝ) * p.1 + (21:ℝ) * p.2 := by
    sorry
  rw [h1] at h
  simp at h
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.2 ^ 2 - c) ((-1:ℝ), (-6:ℝ)) (x-(-1), y-(-6)) = 0) → ((x-(-1)) * (3) - (y-(-6)) * (-48) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p ↦ p.1 ^ 3 - 4 * p.2 ^ 2 - c) ((-1:ℝ), (-6:ℝ)) = fun p ↦ (3 * p.1, -48 * p.2) := by
    apply fderiv_sub_const
    apply fderiv_sub_const
    apply fderiv_fpow
    apply fderiv_fpow
  simp [h1] at h
  simp [h]
  <;> ring
  <;> simp
  <;> linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 4 + 3 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 - c) ((-2:ℝ), (4:ℝ)) (x-(-2), y-4) = 0) → ((x-(-2)) * (-29) - (y-4) * (728) = 0) := by
  intro h
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 - c)
    ((-2, 4)) (x - -2, y - 4) = 0 := h
  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 4 + 3 * p.1 - 3 * p.2 ^ 4 + p.2 ^ 3 - p.2 ^ 2 - c)
    ((-2, 4)) (x + 2, y - 4) = 0 := by
    rw [fderiv_eq_zero_of_eq h1]
  simp [fderiv_const, fderiv_fst, fderiv_snd] at h2
  ring_nf at h2 ⊢
  linarith

example (x y c: ℝ) : (fderiv ℝ (fun p ↦ 2 * p.1 + 2 * p.2 - c) ((-4:ℝ), (1:ℝ)) (x-(-4), y-1) = 0) → ((x-(-4)) * (2) + (y-1) * (2) = 0) := by
  intro h
  simp_all [fderiv_const_apply, fderiv_add, fderiv_mul, fderiv_id, fderiv_const,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_one_pow, ContinuousLinearMap.pow_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.mul_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_mul, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.map_sub, ContinuousLinearMap.map_neg,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_map,
    ContinuousLinearMap.smulRight_smul, ContinuousLinearMap.smulRight_mul,
    ContinuousLinearMap.smulRight_sub, ContinuousLinearMap.smulRight_neg,
    ContinuousLinearMap.smulRight_zero, ContinuousLinearMap.smulRight_smulRight,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply,
    ContinuousLinearMap.smulRight_smulRight_apply, ContinuousLinearMap.smulRight_smulRight_apply]
  linarith

