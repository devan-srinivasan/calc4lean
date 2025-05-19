import Mathlib
open Real

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 1600) (Icc (10: ℝ) (13: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx y hy h
  simp_all only [Icc_subset_Icc_iff, le_of_lt]
  nlinarith [sq_nonneg (x - 10), sq_nonneg (y - 10)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 64) (Icc (4: ℝ) (13: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx
  have h : 4 * x ^ 2 - 32 * x + 64 = (x - 4) ^ 2 * 4 := by ring
  rw [h]
  apply mul_nonneg
  apply sq_nonneg
  norm_num
  <;> linarith [hx.1, hx.2]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 625) (Icc (5: ℝ) (6: ℝ)) := by
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  apply monotoneOn_id
  simp
  <;> norm_num
  <;> apply MonotoneOn.const_mul
  <;> apply MonotoneOn.pow
  <;> apply monotoneOn_id
  <;> simp
  <;> norm_num
  <;> apply MonotoneOn.const_mul
  <;> apply MonotoneOn.pow
  <;> apply monotoneOn_id
  <;> simp
  <;> norm_num
  <;> apply MonotoneOn.const_mul
  <;> apply MonotoneOn.pow
  <;> apply monotoneOn_id
  <;> simp
  <;> norm_num

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 200) (Icc (5: ℝ) (15: ℝ)) := by
  intro x hx y hy h
  norm_num at hx hy
  nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 162 * x + 6561) (Icc (9: ℝ) (10: ℝ)) := by
  apply MonotoneOn.sub
  · intro x hx y hy hxy
    nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9), sq_nonneg (x - y)]
  · intro x hx y hy hxy
    nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 700) (Icc (10: ℝ) (19: ℝ)) := by
  apply MonotoneOn.sub
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  exact monotoneOn_id
  exact monotoneOn_const
  apply MonotoneOn.const_mul
  apply MonotoneOn.sub
  exact monotoneOn_const
  exact monotoneOn_id
  exact monotoneOn_const
  norm_num
  norm_num
  norm_num

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 54 * x + 486) (Icc (9: ℝ) (16: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  intro x hx y hy hxy
  simp only [Function.comp_apply, Icc_subset_Icc_iff] at hx hy ⊢
  ring_nf
  have hxy' : 0 ≤ y - x := by linarith
  nlinarith [sq_nonneg (y - x), sq_nonneg (x - 9), sq_nonneg (y - 9)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 108 * x + 3402) (Icc (9: ℝ) (12: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  intro x hx
  have hx' : x ∈ Icc (9: ℝ) (12: ℝ) := hx
  ring_nf
  have hx'' : 9 ≤ x ∧ x ≤ 12 := hx'
  nlinarith [sq_nonneg (x - 9), sq_nonneg (x - 12)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 30 * x + 270) (Icc (3: ℝ) (5: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq, le_iff_lt_or_eq] at hx hy
  cases' hx with hx1 hx2
  · cases' hy with hy1 hy2
    · nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    · rw [hy2]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
  · cases' hy with hy1 hy2
    · rw [hx2]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]
    · rw [hx2, hy2]
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 36 * x + 972) (Icc (9: ℝ) (13: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9), sq_nonneg (x - y),
    sq_nonneg (x + y - 12)]

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 270) (Icc (3: ℝ) (4: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, Set.mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 576) (Icc (6: ℝ) (14: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 160) (Icc (2: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy h
  have h1 : ∀ z, (λ x ↦ 8 * x ^ 2 - 32 * x + 160) z = 8 * z ^ 2 - 32 * z + 160 := by simp
  simp_all only [h1]
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 126 * x + 3528) (Icc (7: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ (Set.Icc_subset_Ici_self)
  exact fun x hx y hy hxy => by
    nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 7), sq_nonneg (x + y - 16)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (16: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 72 * x + 324) (Icc (9: ℝ) (16: ℝ)) := by
  apply MonotoneOn.mono
  apply convex_Icc
  intro x hx y hy a b ha hb hab
  simp only [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9), sq_nonneg (x - y),
    sq_nonneg (x + y), sq_nonneg (x - 16), sq_nonneg (y - 16)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 28) (Icc (1: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  exact fun x hx y hy hxy => by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 96 * x + 768) (Icc (8: ℝ) (15: ℝ)) := by
  exact MonotoneOn.const_mul (by nlinarith) (by nlinarith)

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 700) (Icc (5: ℝ) (9: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, hx, hy, mem_setOf_eq] at hx hy
  ring_nf
  nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption
  <;> simp_all
  <;> linarith [sq_nonneg (x - 5), sq_nonneg (y - 5)]
  <;> assumption

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 72 * x + 1008) (Icc (4: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4)]
  <;> nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6)]
  <;> nlinarith [sq_nonneg (x + y - 10)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 3600) (Icc (10: ℝ) (19: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_def, and_imp, ge_iff_le, le_of_lt]
  ring_nf
  linarith [sq_nonneg (x - 15), sq_nonneg (y - 15)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 1000) (Icc (5: ℝ) (15: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_subset_Icc_iff, le_refl, true_and]
  ring_nf
  nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5), hx, hy]

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 1344) (Icc (8: ℝ) (11: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy hxy => by
      nlinarith [sq_nonneg (x - 8), sq_nonneg (y - 8), sq_nonneg (x - y)]
  · exact fun x hx y hy hxy => by
      nlinarith [sq_nonneg (x - 11), sq_nonneg (y - 11), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 2205) (Icc (7: ℝ) (11: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 7), sq_nonneg (x - 11), sq_nonneg (y - 11)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 216) (Icc (3: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (fun x hx => _)
  · intro x hx
    have h₁ : 3 ≤ x := by simp_all [Real.sqrt_le_iff]
    have h₂ : x ≤ 10 := by simp_all [Real.sqrt_le_iff]
    nlinarith [sq_nonneg (x - 6)]
  · simp_all [Real.sqrt_le_iff]
  · linarith

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 1152) (Icc (4: ℝ) (7: ℝ)) := by
  apply MonotoneOn.mono _ (fun x hx => by simp [hx])
  have h : ∀ x ∈ Icc (4: ℝ) (7: ℝ), (8 * x ^ 2 - 64 * x + 1152) = 8 * (x - 4) ^ 2 + 288 := by
    intro x hx
    simp [sq, mul_add, mul_sub, mul_comm, mul_left_comm]
    ring
  intro x hx y hy hxy
  simp [h x hx, h y hy]
  linarith [sq_nonneg (x - 4), sq_nonneg (y - 4)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 448) (Icc (4: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  apply MonotoneOn.sub
  · apply MonotoneOn.const_mul
    apply MonotoneOn.pow
    exact monotoneOn_id
  · apply MonotoneOn.const_mul
    apply MonotoneOn.pow
    exact monotoneOn_id
  apply MonotoneOn.const_add
  apply MonotoneOn.const_add
  exact monotoneOn_id

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 45) (Icc (1: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 40 * x + 240) (Icc (2: ℝ) (10: ℝ)) := by
  intro x hx y hy hxy
  simp only [mul_assoc, mul_one, sub_eq_add_neg, neg_add_rev, neg_mul_eq_neg_mul] at hx hy ⊢
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x + y - 10)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 60 * x + 810) (Icc (3: ℝ) (13: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 60) (Icc (2: ℝ) (9: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, le_set_biUnion_iff, mem_Icc] at hx hy ⊢
  simp_all only [ge_iff_le, gt_iff_lt, sub_le_sub_iff_right, sub_lt_sub_iff_right]
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 4) (Icc (1: ℝ) (11: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  have hxy : x ≤ y := by simpa using hxy
  simp only [mul_assoc]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 144 * x + 2592) (Icc (9: ℝ) (19: ℝ)) := by
  apply MonotoneOn.const_mul
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]
  <;> norm_num
  <;> norm_num
  <;> linarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]
  <;> norm_num
  <;> norm_num
  <;> linarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]
  <;> norm_num
  <;> norm_num
  <;> linarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]
  <;> norm_num
  <;> norm_num
  <;> linarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]
  <;> norm_num
  <;> norm_num
  <;> linarith [sq_nonneg (x - 12), sq_nonneg (y - 12)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 112 * x + 3136) (Icc (8: ℝ) (10: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 200) (Icc (5: ℝ) (14: ℝ)) := by
  apply MonotoneOn.sub
  · apply MonotoneOn.const_mul
    · exact fun x hx y hy h => mul_le_mul_of_nonneg_left h (by norm_num)
    · exact 200
  · apply MonotoneOn.const_mul
    · exact fun x hx y hy h => mul_le_mul_of_nonneg_left h (by norm_num)
    · exact 80
  · exact fun x hx y hy h => mul_le_mul_of_nonneg_left h (by norm_num)
  · exact 200
  · exact 80
  · exact Icc_subset_Icc (by norm_num) (by norm_num)

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 16 * x + 48) (Icc (2: ℝ) (10: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_def, and_imp, ge_iff_le, le_of_lt]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), hx.1, hx.2, hy.1, hy.2]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 432) (Icc (3: ℝ) (8: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  exact
    MonotoneOn.sub (MonotoneOn.const_mul (by norm_num) <|
      MonotoneOn.pow (MonotoneOn.id (by norm_num) (by norm_num)))
      (MonotoneOn.const_mul (by norm_num) <| MonotoneOn.id (by norm_num) (by norm_num))

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 84 * x + 252) (Icc (6: ℝ) (16: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy hxy ↦ by nlinarith [sq_nonneg (x - y)]
  · exact fun x hx y hy hxy ↦ by nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 40 * x + 400) (Icc (10: ℝ) (16: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 10), sq_nonneg (y - 10)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  apply MonotoneOn.id
  exact fun x hx => ⟨by nlinarith, by nlinarith⟩

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 112 * x + 2744) (Icc (7: ℝ) (13: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_left
  intro x hx y hy hxy
  simp only [mul_assoc, mul_one, mul_comm] at hx hy ⊢
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (15: ℝ)) := by
  apply MonotoneOn.sub
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  intro x hx
  apply MonotoneOn.id
  simp [hx.1, hx.2]
  apply MonotoneOn.const_mul
  intro x hx
  apply MonotoneOn.id
  simp [hx.1, hx.2]
  norm_num
  <;> simp_all only [Icc_def, le_refl, true_and, and_true]
  <;> norm_num
  <;> intro x hx
  <;> simp_all only [Icc_def, le_refl, true_and, and_true]
  <;> norm_num
  <;> linarith

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 648) (Icc (6: ℝ) (7: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x + y - 12),
    sq_nonneg (y + x - 12)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (17: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq] at hx hy
  have h : (x : ℝ) ≤ y := hxy
  nlinarith [sq_nonneg (x - 7), sq_nonneg (y - 7)]
  <;> nlinarith

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 432) (Icc (6: ℝ) (7: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (8: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy hxy ↦ mul_le_mul_of_nonneg_left hxy (by norm_num)
  · exact fun x hx y hy hxy ↦ mul_le_mul_of_nonneg_left hxy (by norm_num)

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 360) (Icc (6: ℝ) (12: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_left
  exact fun x hx y hy hxy => by
    simp only [mem_Icc] at hx hy
    nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 40 * x + 320) (Icc (4: ℝ) (14: ℝ)) := by
  intro x hx y hy hxy
  simp_all only [Icc_def, le_refl, true_and, and_true, le_of_lt]
  have h : ∀ x, (λ x ↦ 5 * x ^ 2 - 40 * x + 320) x = 5 * x ^ 2 - 40 * x + 320 := by
    intro x
    rfl
  simp_all only [h]
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 140 * x + 4410) (Icc (7: ℝ) (16: ℝ)) := by
  apply MonotoneOn.sub
  intro x hx
  norm_num
  intro y hy
  norm_num
  apply (convex_Icc _ _).monotoneOn_of_deriv_nonneg
  norm_num
  norm_num
  intro z hz
  norm_num
  linarith [hz.1, hz.2]
  <;> simp_all
  <;> norm_num
  <;> linarith

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 24 * x + 48) (Icc (2: ℝ) (12: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  exact
    MonotoneOn.sub (fun x hx y hy hxy => by
      nlinarith [sq_nonneg (x - y)])
      (fun x hx y hy hxy => by
        nlinarith [sq_nonneg (x + y - 4)])

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 64) (Icc (2: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_right (by linarith))
  intro x hx
  have h : ∀ x : ℝ, x ∈ Icc (2 : ℝ) (9 : ℝ) → 8 * x ^ 2 - 32 * x + 64 ≤ 8 * (x + 2) ^ 2 := by
    intro x hx
    ring_nf
    nlinarith [sq_nonneg (x - 4)]
  intro x hx y hy hxy
  nlinarith [h x hx, h y hy, sq_nonneg (x + 2 - (y + 2))]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (17: ℝ)) := by
  apply MonotoneOn.mono _
  apply convex_Icc
  intro x hx
  simp
  ring_nf
  nlinarith [sq_nonneg (x - 10)]

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 48) (Icc (2: ℝ) (3: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_left
  intro x hx y hy hxy
  simp only [Function.comp_apply, mul_add, mul_one, sub_add, sub_self,
    mul_comm (3 : ℝ), mul_assoc, sub_eq_add_neg, add_assoc]
  nlinarith [sq_nonneg (x + y - 4)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 108) (Icc (3: ℝ) (12: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  exact MonotoneOn.const_mul (fun x hx y hy hxy => by nlinarith) 6
  <;> norm_num
  <;> intro x hx <;> nlinarith
  <;> norm_num
  <;> intro x hx <;> nlinarith
  <;> norm_num
  <;> intro x hx <;> nlinarith

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 224) (Icc (2: ℝ) (6: ℝ)) := by
  apply MonotoneOn.sub
  · intro x hx y hy hxy
    simp_all only [mul_comm, mul_assoc, mul_left_comm, mul_one, mul_zero, sub_eq_add_neg, neg_add_rev,
      neg_mul_eq_neg_mul]
    ring_nf
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4)]
  · intro x hx y hy hxy
    simp_all only [mul_comm, mul_assoc, mul_left_comm, mul_one, mul_zero, sub_eq_add_neg, neg_add_rev,
      neg_mul_eq_neg_mul]
    ring_nf
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 2025) (Icc (9: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  exact fun x hx y hy h => by
    nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (10: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, mem_setOf, le_of_lt] at hx hy
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 2)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 1176) (Icc (7: ℝ) (11: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, ← and_assoc] at hx hy
  ring_nf at h ⊢
  have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (x + y - 14)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 54 * x + 162) (Icc (3: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), hxy]
  <;> exact ⟨le_of_lt (by norm_num : (3 : ℝ) < 4), le_of_lt (by norm_num : (4 : ℝ) < 10)⟩

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 108 * x + 324) (Icc (6: ℝ) (13: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  simp only [sub_le_sub_iff_right, mul_comm, mul_assoc, mul_left_comm]
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 12) (Icc (1: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono _
  · intro x hx y hy hxy
    have h : ∀ x, 2 * x ^ 2 - 4 * x + 12 = 2 * (x - 1) ^ 2 + 10 := by
      intro x
      ring
    simp_all only [h]
    linarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
  · simp; norm_num

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 10) (Icc (1: ℝ) (2: ℝ)) := by
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  apply MonotoneOn.sub
  exact monotoneOn_const
  apply MonotoneOn.mul_const
  apply MonotoneOn.id
  norm_num
  exact monotoneOn_const
  norm_num
  exact monotoneOn_id
  <;> norm_num
  <;> exact fun _ hx => hx.1.trans hx.2
  <;> exact fun _ hx => hx.1.trans hx.2

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 12) (Icc (1: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, le_sub_iff_add_le, sub_le_iff_le_add, add_right_inj] at hx hy hxy
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y - x)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 768) (Icc (4: ℝ) (7: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  intro x hx y hy hxy
  simp only [hx, hy, hxy, mem_Icc, ge_iff_le] at *
  nlinarith [sq_nonneg (x - 6)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 24) (Icc (1: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono (fun x hx => by simp_all)
  intro x hx y hy hxy
  simp_all only [mul_one, mul_zero, sub_zero, zero_add, mul_two, mul_comm, mul_left_comm, mul_assoc]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 750) (Icc (5: ℝ) (9: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc_def, mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 4200) (Icc (10: ℝ) (13: ℝ)) := by
  apply MonotoneOn.mono (fun x hx y hy hxy => _)
  simp_all only [mul_sub_left_distrib, mul_sub_right_distrib, mul_one, sub_add, sub_eq_add_neg,
    mul_assoc]
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 100 * x + 2000) (Icc (5: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ <| Icc_subset_Icc (by norm_num) (by norm_num)
  exact
    MonotoneOn.sub (fun x hx y hy hxy =>
      mul_le_mul_of_nonneg_left hxy (by norm_num))
      (fun x hx y hy hxy =>
        mul_le_mul_of_nonneg_left hxy (by norm_num))

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 160 * x + 1920) (Icc (8: ℝ) (15: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq] at hx hy
  simp only [mul_comm]
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 4050) (Icc (9: ℝ) (11: ℝ)) := by
  refine' MonotoneOn.mono _ _
  · intro x hx
    simp
    ring_nf
    norm_num
    linarith [hx.1, hx.2]
  · norm_num

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 180 * x + 6480) (Icc (9: ℝ) (18: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 32 * x + 512) (Icc (8: ℝ) (14: ℝ)) := by
  apply MonotoneOn.sub
  exact MonotoneOn.const_mul (fun _ _ _ ↦ by linarith)
  exact MonotoneOn.const_mul (fun _ _ _ ↦ by linarith)
  intro x hx
  simp
  nlinarith [sq_nonneg (x - 8), sq_nonneg (x - 14)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 70) (Icc (1: ℝ) (4: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_def, mem_setOf_eq]
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 63) (Icc (1: ℝ) (3: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 2)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 882) (Icc (7: ℝ) (11: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, Set.mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 7), sq_nonneg (y - 7),
    sq_nonneg (x - 11), sq_nonneg (y - 11)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 16 * x + 224) (Icc (4: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1050) (Icc (5: ℝ) (7: ℝ)) := by
  intro x hx y hy hxy
  simp_all only [Set.mem_Icc, le_of_lt]
  ring_nf
  nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5), sq_nonneg (y - 7), sq_nonneg (x - 7)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 1215) (Icc (9: ℝ) (17: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy h => by
      have h : 9 ≤ x ∧ x ≤ 17 := hx
      have h' : 9 ≤ y ∧ y ≤ 17 := hy
      nlinarith [sq_nonneg (x - y)]
  · exact fun x hx y hy h => by
      have h : 9 ≤ x ∧ x ≤ 17 := hx
      have h' : 9 ≤ y ∧ y ≤ 17 := hy
      nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (11: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc_def, Set.mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + 6), sq_nonneg (x - y - 6)]

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 48 * x + 768) (Icc (4: ℝ) (8: ℝ)) := by
  apply MonotoneOn.const_mul
  intro x hx
  simp only [mul_sub, mul_one, mul_add, sub_add, add_sub, add_assoc, add_left_comm,
    sub_sub, sub_right_comm, sub_self, sub_zero, mul_comm, mul_left_comm, mul_assoc]
  ring_nf
  norm_num
  nlinarith [sq_nonneg (x - 6)]

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (14: ℝ)) := by
  exact fun x hx y hy hxy => by
    simp only [Set.mem_Icc] at hx hy
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 12)]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 80 * x + 800) (Icc (4: ℝ) (8: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy hxy ↦ mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by norm_num) hxy 2) (by norm_num)
  · exact fun x hx y hy hxy ↦ mul_le_mul_of_nonneg_left hxy (by norm_num)
  <;> norm_num
  <;> exact (fun x hx ↦ by norm_num [hx])
  <;> exact (fun x hx ↦ by norm_num [hx])

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 24 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
  intro x hx y hy hxy
  have := sq_nonneg (x - 4)
  have := sq_nonneg (y - 4)
  have := sq_nonneg (x + y - 4)
  nlinarith [hx.1, hx.2, hy.1, hy.2, hxy]

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 100) (Icc (1: ℝ) (6: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_def, Set.mem_setOf_eq, ge_iff_le]
  ring_nf
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 98 * x + 1372) (Icc (7: ℝ) (12: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 7), sq_nonneg (y - 7),
    sq_nonneg (x - 12), sq_nonneg (y - 12)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 42 * x + 252) (Icc (3: ℝ) (12: ℝ)) := by
  apply MonotoneOn.mono _
  · rintro x hx y hy h
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), hx.1, hx.2, hy.1, hy.2]
  rintro x hx y hy h
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), hx.1, hx.2, hy.1, hy.2]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 112) (Icc (4: ℝ) (14: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, le_def] at hx hy
  simp only [mem_Icc] at hx hy
  have h1 : 4 ≤ x ∧ x ≤ 14 := by exact hx
  have h2 : 4 ≤ y ∧ y ≤ 14 := by exact hy
  have h3 : 4 ≤ x := by linarith
  have h4 : x ≤ 14 := by linarith
  have h5 : 4 ≤ y := by linarith
  have h6 : y ≤ 14 := by linarith
  have h7 : x ≤ y := by linarith
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 8) (Icc (1: ℝ) (11: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [mul_comm]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 2)]

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1750) (Icc (5: ℝ) (8: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  apply MonotoneOn.const_mul
  apply MonotoneOn.id
  apply Icc_subset_Ici_self

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 72 * x + 1296) (Icc (6: ℝ) (10: ℝ)) := by
  apply MonotoneOn.sub
  · exact fun x hx y hy hxy ↦ by
      nlinarith [sq_nonneg (x - y)]
  · exact fun x hx y hy hxy ↦ by
      nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 128) (Icc (4: ℝ) (12: ℝ)) := by
  exact fun x hx y hy hxy ↦ by
    simp only [Icc, Set.mem_setOf_eq] at hx hy
    simp_all only [mul_add, mul_one, mul_neg, mul_comm]
    ring_nf
    nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 192) (Icc (4: ℝ) (13: ℝ)) := by
  apply MonotoneOn.mono
  apply MonotoneOn.const_mul
  intro x hx y hy h
  apply pow_le_pow_of_le_left
  exact h
  norm_num
  apply MonotoneOn.sub
  apply MonotoneOn.const_mul
  intro x hx y hy h
  apply pow_le_pow_of_le_left
  exact h
  norm_num
  apply MonotoneOn.const_mul
  intro x hx y hy h
  apply pow_le_pow_of_le_left
  exact h
  norm_num
  exact Icc_subset_Icc (by norm_num) (by norm_num) hx hy

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 189) (Icc (3: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_right (by norm_num))
  intro x hx y hy h
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 3), sq_nonneg (y - 3),
    sq_nonneg (x - 10), sq_nonneg (y - 10)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 12) (Icc (1: ℝ) (9: ℝ)) := by
  apply MonotoneOn.sub
  · apply MonotoneOn.const_mul
    · apply monotoneOn_id
    norm_num
  apply MonotoneOn.const_mul
  · apply MonotoneOn.id
  norm_num

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 126 * x + 5670) (Icc (9: ℝ) (16: ℝ)) := by
  intro x hx y hy h
  simp only [mem_Icc] at hx hy
  have hxy : x ≤ y := h
  nlinarith [sq_nonneg (x - 14), sq_nonneg (y - 14)]

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 60 * x + 1080) (Icc (6: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc, mem_setOf_eq, ← sub_le_iff_le_add] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x + y - 12)]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 300) (Icc (5: ℝ) (7: ℝ)) := by
  apply MonotoneOn.mono _ <| Icc_subset_Icc_right (by norm_num)
  exact
    MonotoneOn.sub (MonotoneOn.const_mul (fun _ hx _ hy => by
      linarith [hx.1, hy.1]) <| by norm_num) (MonotoneOn.const_mul (fun _ hx _ hy => by
      linarith [hx.1, hy.1]) <| by norm_num)

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 576) (Icc (8: ℝ) (11: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  exact
    (convex_Icc _ _).monotoneOn_of_deriv_nonneg (fun x _ => by
     
      norm_num) (fun x _ => by norm_num)
  <;> norm_num
  <;> apply DifferentiableOn.congr _ (fun x hx => ?_)
  <;> apply DifferentiableOn.const_mul
  <;> apply DifferentiableOn.pow
  <;> apply DifferentiableOn.id
  <;> simp
  <;> apply DifferentiableOn.const_sub
  <;> apply DifferentiableOn.const_add
  <;> apply DifferentiableOn.const_mul
  <;> apply DifferentiableOn.pow
  <;> apply DifferentiableOn.id
  <;> simp
  <;> apply DifferentiableOn.const_sub
  <;> apply DifferentiableOn.const_add
  <;> apply DifferentiableOn.const_mul
  <;> apply DifferentiableOn.pow
  <;> apply DifferentiableOn.id
  <;> simp
  <;> apply DifferentiableOn.const_sub
  <;> apply DifferentiableOn.const_add

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 168) (Icc (2: ℝ) (10: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Icc (by norm_num) (by norm_num))
  exact fun x hx y hy hxy => sub_le_sub
    (by nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), hxy])
    (by nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), hxy])

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 336) (Icc (4: ℝ) (8: ℝ)) := by
  intro x hx y hy h
  simp only [Icc, mem_setOf_eq, le_of_lt] at hx hy
  nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), sq_nonneg (x - y)]

