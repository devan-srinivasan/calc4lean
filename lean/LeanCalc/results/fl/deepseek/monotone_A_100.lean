import Mathlib
open Real Set

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 4 * x ^ 6 + 7 * x ^ 5 + 3 * x ^ 4 + 15 * x ^ 3 + 10 * x ^ 2 + 4) (Icc (0: ℝ) (4: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + x + y),
    sq_nonneg (x - y - (x + y))]

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 6 * x ^ 4 + 4 * x ^ 3) (Icc (0: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono
  exact fun x hx y hy hxy => by
    simp only [mul_assoc, mul_comm, mul_left_comm, mul_pow]
    nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2)]
  exact Set.Icc_subset_Icc_right (by norm_num)

example: MonotoneOn (λ x ↦ 16 * x ^ 3 + 17 * x ^ 2 + 7 * x + 6) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [mul_assoc, mul_comm, mul_left_comm] at hx hy ⊢
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), hxy, hx, hy]

example: MonotoneOn (λ x ↦ 18 * x ^ 6 + 7 * x ^ 4 + 17 * x ^ 3 + 4) (Icc (0: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Ici_self
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x + y), hx.1, hx.2, hy.1, hy.2, hxy]

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 3 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ x := by
    cases' hx with hx₁ hx₂
    nlinarith
  have hy' : y ≤ 3 := by
    cases' hy with hy₁ hy₂
    nlinarith
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 13 * x ^ 6 + 8 * x ^ 5 + 19 * x ^ 4 + 15 * x ^ 3 + 8 * x ^ 2 + 19 * x + 5) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy h
  norm_num
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2),
    sq_nonneg (y - 1 / 2), sq_nonneg (y + 1 / 2)]

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy h
  have h₁ : 0 ≤ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20 := by nlinarith
  have h₂ : 0 ≤ 16 * y ^ 7 + 8 * y ^ 6 + 4 * y ^ 5 + 16 * y ^ 4 + 12 * y ^ 2 + 20 := by nlinarith
  have h₃ : 0 ≤ 16 * (y - x) ^ 7 + 8 * (y - x) ^ 6 + 4 * (y - x) ^ 5 + 16 * (y - x) ^ 4 + 12 * (y - x) ^ 2 + 20 := by
    nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (2 * y - x), sq_nonneg (y + 2 * x),
      sq_nonneg (y - 2 * x), sq_nonneg (2 * y + x), sq_nonneg (2 * y - 3 * x), sq_nonneg (3 * y - 2 * x)]
  nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (2 * y - x), sq_nonneg (y + 2 * x),
    sq_nonneg (y - 2 * x), sq_nonneg (2 * y + x), sq_nonneg (2 * y - 3 * x), sq_nonneg (3 * y - 2 * x)]

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 9 * x ^ 3 + 12 * x ^ 2 + 2 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc_subset_Icc_iff] at hx hy
  nlinarith [sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 2 * x * y),
    sq_nonneg (x ^ 2 + y ^ 2 + 2 * x * y)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 4 + 19 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  simp_all only [Icc_def, le_refl, le_of_lt, true_and, and_true, le_of_eq]
  nlinarith [sq_nonneg (x ^ 3 + 2 * x ^ 2), sq_nonneg (y ^ 3 + 2 * y ^ 2)]

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 2 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (7: ℝ)) := by
  apply MonotoneOn.of_deriv (fun x hx => _)
  intro x hx
  nlinarith [sq_nonneg (2 * x ^ 3 + 2 * x), sq_nonneg (2 * x ^ 2 + 2 * x), sq_nonneg (x ^ 2 + x)]
  <;> simp [deriv_within]
  <;> norm_num
  <;> nlinarith [sq_nonneg (2 * x ^ 3 + 2 * x), sq_nonneg (2 * x ^ 2 + 2 * x), sq_nonneg (x ^ 2 + x)]
  <;> simp [deriv_within]
  <;> norm_num
  <;> nlinarith [sq_nonneg (2 * x ^ 3 + 2 * x), sq_nonneg (2 * x ^ 2 + 2 * x), sq_nonneg (x ^ 2 + x)]
  <;> simp [deriv_within]
  <;> norm_num
  <;> nlinarith [sq_nonneg (2 * x ^ 3 + 2 * x), sq_nonneg (2 * x ^ 2 + 2 * x), sq_nonneg (x ^ 2 + x)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 18 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ <| Icc_subset_Ici_self
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2)]

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 18 * x ^ 6 + 2 * x ^ 5 + 17 * x ^ 3 + 7 * x) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.mono
  exact (monotone_iff_forall_lt.2 fun x _ y _ h => by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2),
      sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 5 - y ^ 5), sq_nonneg (x ^ 6 - y ^ 6), sq_nonneg (x ^ 7 - y ^ 7)]
  )
  exact Icc_subset_Icc_right (by norm_num)
  <;> simp_all
  <;> norm_num
  <;> linarith
  <;> norm_num
  <;> linarith

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 18 * x ^ 6 + 11 * x ^ 5 + 14 * x ^ 4 + 20 * x ^ 3 + 13 * x ^ 2 + 5 * x + 8) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx
  intro y hy
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 2), sq_nonneg (x + y + 2)]

example: MonotoneOn (λ x ↦ 16 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 3 + 15 * x ^ 2 + 8 * x) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy h
  simp only [MonotoneOn, Set.mem_Icc] at hx hy h ⊢
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2), sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 15 * x ^ 6 + 9 * x ^ 4 + 8 * x ^ 2 + 17 * x + 15) (Icc (0: ℝ) (10: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (x ^ 2 + x), sq_nonneg (y ^ 3 + y ^ 2),
    sq_nonneg (y ^ 2 + y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 8 * x ^ 5 + 15 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [Function.comp_apply, mul_assoc, mul_comm, mul_left_comm,
    mul_right_comm] at hx hy ⊢
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2),
    sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 6 * x ^ 2 + 5 * x + 4) (Icc (0: ℝ) (10: ℝ)) := by
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y + x + y),
    sq_nonneg (x - y - x - y)]

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 11 * x ^ 6 + 2 * x ^ 4 + 19 * x ^ 2) (Icc (0: ℝ) (7: ℝ)) := by
  refine' monotoneOn_of_deriv_nonneg _ _
  · exact fun x _ => by positivity
  · intro x hx
    have : 0 < x := lt_of_le_of_lt (by simp [hx]) (by norm_num)
    simp
    nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 2), sq_nonneg (x ^ 4), sq_nonneg (x ^ 5),
      sq_nonneg (x ^ 6), sq_nonneg (x ^ 7)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 7 * x ^ 6 + 13 * x ^ 5 + 13 * x ^ 3) (Icc (0: ℝ) (2: ℝ)) := by
  intro x hx y hy h
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 3 * x ^ 6 + 17 * x ^ 4 + 13 * x ^ 3 + 2 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (2: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 3 + 11 * x + 4) (Icc (0: ℝ) (6: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Ici_self)
  apply MonotoneOn.add
  · exact fun x hx y hy hxy => by nlinarith [sq_nonneg (x - y)]
  · exact fun x hx y hy hxy => by nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 14 * x ^ 3 + 2 * x ^ 2 + 18 * x + 19) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx
  intro y hy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x ^ 3 - x ^ 2 * y), sq_nonneg (x ^ 2 * y - x * y ^ 2), sq_nonneg (x * y ^ 2 - y ^ 3)]

example: MonotoneOn (λ x ↦ 9 * x ^ 4 + 3 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx
  intro y hy
  intro h
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 14 * x ^ 6 + 3 * x ^ 3 + 20 * x ^ 2 + 13 * x) (Icc (0: ℝ) (5: ℝ)) := by
  intro x hx y hy hxy
  simp only [mul_assoc, mul_comm, mul_left_comm] at *
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 2 + 6) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.mono _ (Set.Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 6 * x ^ 2 + 12 * x + 4) (Icc (0: ℝ) (7: ℝ)) := by
  intro x hx y hy h
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y - 2)]

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 11 * x ^ 5 + 19 * x + 10) (Icc (0: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ x := by
    cases' hx with hx₁ hx₂
    linarith
  have hy' : 0 ≤ y := by
    cases' hy with hy₁ hy₂
    linarith
  have hxy' : 0 ≤ y - x := by linarith
  simp only [mul_assoc, mul_one, mul_add, mul_comm, mul_left_comm]
  nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 2), sq_nonneg x, sq_nonneg (y ^ 3), sq_nonneg (y ^ 2), sq_nonneg y, sq_nonneg (x - y), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 18 * x ^ 5 + 9 * x ^ 3 + 4 * x ^ 2 + 3 * x) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  have hx' := hx
  have hy' := hy
  simp_all only [Set.mem_Icc, Set.mem_Icc]
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 19 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 18) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_right (by norm_num))
  exact
    MonotoneOn.add
      (MonotoneOn.add
        (MonotoneOn.add (MonotoneOn.add (by exact (monotone_id.const_mul (by norm_num)).monotoneOn)
          (by exact (monotone_id.const_mul (by norm_num)).monotoneOn))
          (by exact (monotone_id.const_mul (by norm_num)).monotoneOn))
        (by exact (monotone_id.const_mul (by norm_num)).monotoneOn))
      (by exact (monotone_id.const_mul (by norm_num)).monotoneOn)

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 11 * x ^ 5 + 17 * x ^ 4 + 5 * x ^ 3 + 18 * x ^ 2 + 13 * x) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_right
  exact fun x hx y hy h => by
    simp only [Set.mem_Icc] at hx hy
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 7 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 4 + 9 * x ^ 2 + 16 * x) (Icc (0: ℝ) (4: ℝ)) := by
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2), sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 18 * x ^ 6 + 4 * x ^ 5 + 20 * x ^ 4 + 11 * x ^ 3 + 2 * x ^ 2 + 9 * x + 7) (Icc (0: ℝ) (3: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Ici_self)
  exact fun x hx y hy h => by
    simp only [mul_comm, mul_left_comm, mul_assoc] at h
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2),
      sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x ^ 2 - 3 * y ^ 2), sq_nonneg (x ^ 2 + 3 * y ^ 2),
      sq_nonneg (2 * x ^ 2 - y ^ 2), sq_nonneg (2 * x ^ 2 + y ^ 2)]

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 10 * x ^ 6 + 20 * x ^ 5 + 8 * x ^ 3 + 15 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  intro x hx y hy hxy
  simp only [mul_assoc, mul_one, mul_zero, add_assoc, add_zero, add_left_comm] at hxy ⊢
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x - y),
    sq_nonneg (x + y),
    sq_nonneg (x ^ 3 + x ^ 2),
    sq_nonneg (y ^ 3 + y ^ 2),
    sq_nonneg (x ^ 3 - x ^ 2),
    sq_nonneg (y ^ 3 - y ^ 2)]

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 17 * x ^ 6 + 10 * x ^ 2 + 12 * x + 13) (Icc (0: ℝ) (3: ℝ)) := by
  intro x hx y hy h
  norm_num
  nlinarith [sq_nonneg (x ^ 3 + 13 * x ^ 2), sq_nonneg (y ^ 3 + 13 * y ^ 2)]

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 8 * x + 14) (Icc (0: ℝ) (7: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_subset_Icc_iff, le_of_lt]
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), hx.1, hx.2, hy.1, hy.2]

example: MonotoneOn (λ x ↦ 6 * x ^ 4 + 20 * x ^ 3 + 5 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 2 + 5 * x), sq_nonneg (y ^ 2 + 5 * y),
    sq_nonneg (x + y), sq_nonneg (x ^ 2 + y ^ 2), hxy]

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 15 * x ^ 6 + 8 * x ^ 5 + 2 * x ^ 4 + 7 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.mono _
  · intro x hx
    simp_all only [Set.mem_Icc, le_refl, true_and_iff, zero_le_four]
    norm_num
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), sq_nonneg (x ^ 4), sq_nonneg (x ^ 5), sq_nonneg (x ^ 6), sq_nonneg (x ^ 7)]
  apply MonotoneOn.add
  · apply MonotoneOn.const_mul
    · apply MonotoneOn.pow
      exact monotoneOn_id
    norm_num
  apply MonotoneOn.add
  · apply MonotoneOn.const_mul
    · apply MonotoneOn.pow
      exact monotoneOn_id
    norm_num
  apply MonotoneOn.add
  · apply MonotoneOn.const_mul
    · apply MonotoneOn.pow
      exact monotoneOn_id
    norm_num
  apply MonotoneOn.add
  · apply MonotoneOn.const_mul
    · apply MonotoneOn.pow
      exact monotoneOn_id
    norm_num
  apply MonotoneOn.add
  · apply MonotoneOn.const_mul
    · apply MonotoneOn.pow
      exact monotoneOn_id
    norm_num
  apply MonotoneOn.const_mul
  · apply MonotoneOn.id
  norm_num

example: MonotoneOn (λ x ↦ 9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono (fun x hx => ?_)
  have h₀ : 0 ≤ x := by linarith [hx.1]
  have h₁ : 0 ≤ 5 := by linarith [hx.2]
  have h₂ : 0 ≤ 9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x := by
    nlinarith [sq_nonneg (3 * x ^ 3 + x), sq_nonneg (3 * x ^ 2), sq_nonneg x, sq_nonneg 1]
  have h₃ : 0 ≤ 9 * 5 ^ 7 + 7 * 5 ^ 5 + 19 * 5 ^ 3 + 7 * 5 := by
    nlinarith [sq_nonneg (3 * 5 ^ 3 + 5), sq_nonneg (3 * 5 ^ 2), sq_nonneg 5, sq_nonneg 1]
  have h₄ : 0 ≤ (9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x) / 7 := by positivity
  have h₅ : 0 ≤ (9 * 5 ^ 7 + 7 * 5 ^ 5 + 19 * 5 ^ 3 + 7 * 5) / 7 := by positivity
  linarith [sq_nonneg (3 * x ^ 3 + x), sq_nonneg (3 * x ^ 2), sq_nonneg x, sq_nonneg 1]

example: MonotoneOn (λ x ↦ 8 * x ^ 4 + 15 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  have hx' : 0 ≤ x := by exact hx.1
  have hy' : 0 ≤ y := by exact hy.1
  nlinarith [sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x + y), sq_nonneg (x - y),
    sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (2 * x), sq_nonneg (2 * y)]

example: MonotoneOn (λ x ↦ 3 * x ^ 6 + 14 * x ^ 5 + 14 * x ^ 4) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  apply MonotoneOn.add
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  exact monotoneOn_id
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  exact monotoneOn_id
  apply MonotoneOn.const_mul
  apply MonotoneOn.pow
  exact monotoneOn_id

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 6 * x ^ 5 + 3 * x ^ 4 + 6 * x ^ 3 + 16 * x + 14) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.mono _
  exact Icc_subset_Icc_left (by norm_num)
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x ^ 3 - x ^ 2 * y), sq_nonneg (x ^ 2 * y - x * y ^ 2), sq_nonneg (x * y ^ 2 - y ^ 3)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 15 * x ^ 6 + 20 * x ^ 5 + 17 * x ^ 4 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2 * y + y ^ 2 * x + y ^ 3)]
  <;> nlinarith [sq_nonneg (x ^ 3 - x ^ 2 * y), sq_nonneg (y ^ 3 - y ^ 2 * x), sq_nonneg (x ^ 2 * y - y ^ 2 * x)]
  <;> nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 * y - y ^ 2 * x)]
  <;> nlinarith [sq_nonneg (x + y)]
  <;> nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 3 * x ^ 3 + 6 * x ^ 2 + 17 * x + 6) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  simp only [Set.mem_Icc] at hxy
  nlinarith [sq_nonneg (x ^ 2 + y ^ 2), hx.1, hx.2, hy.1, hy.2, sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 5 + 17 * x ^ 4 + 9 * x ^ 3 + 12 * x + 18) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono (fun x hx y hy hxy => ?_) (Set.Icc_subset_Icc_left (by norm_num))
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x ^ 3 - x ^ 2 * y), sq_nonneg (x ^ 2 * y - x * y ^ 2), sq_nonneg (x * y ^ 2 - y ^ 3)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 9 * x ^ 6 + 3 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 18 * x) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_left
  intro x hx y hy hxy
  have h₁ : 0 ≤ x := by linarith [hx.1]
  have h₂ : 0 ≤ y := by linarith [hy.1]
  have h₃ : 0 ≤ x + y := by linarith
  have h₄ : 0 ≤ x * y := by positivity
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (x + 1),
    sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x - y - 1), sq_nonneg (x - y + 1),
    sq_nonneg (x + y - 1), sq_nonneg (x + y + 1)]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 12 * x ^ 6 + 14 * x ^ 5 + 13 * x ^ 4 + 18 * x ^ 3 + 5 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.add
  <;> apply MonotoneOn.const_mul
  <;> apply MonotoneOn.pow
  <;> intro x hx y hy hxy
  <;> norm_num
  <;> linarith [hx.1, hx.2, hy.1, hy.2, hxy]

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 4 * x ^ 6 + 19 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  apply le_of_not_lt
  intro h
  have h₁ : 0 < 7 * x ^ 6 + 4 * x ^ 5 + 19 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 4 * x := by
    nlinarith [pow_pos hx.1 6, pow_pos hx.1 5, pow_pos hx.1 4, pow_pos hx.1 3, pow_pos hx.1 2, h]
  have h₂ : 0 < 7 * y ^ 6 + 4 * y ^ 5 + 19 * y ^ 4 + 10 * y ^ 3 + 10 * y ^ 2 + 4 * y := by
    nlinarith [pow_pos hy.1 6, pow_pos hy.1 5, pow_pos hy.1 4, pow_pos hy.1 3, pow_pos hy.1 2, h]
  nlinarith [mul_pos h₁ h₂, pow_pos hxy 6, pow_pos hxy 5, pow_pos hxy 4, pow_pos hxy 3, pow_pos hxy 2, h]

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 13 * x ^ 6 + 9 * x ^ 5 + 16 * x ^ 4 + 15 * x ^ 3 + 5 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  simp only [mul_comm, mul_add, mul_one, mul_assoc, mul_left_comm]
  ring_nf
  nlinarith [sq_nonneg (x ^ 2 + x), sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (x ^ 2 + 1),
    sq_nonneg (x ^ 3 + x), sq_nonneg (x ^ 2 + x), sq_nonneg (x ^ 3 + x),
    sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 3 + x), sq_nonneg (x ^ 2 + x),
    sq_nonneg (x ^ 3 + x), sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 3 + x)]

example: MonotoneOn (λ x ↦ 5 * x ^ 5 + 15 * x ^ 3 + 20 * x ^ 2) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy h
  simp only [mul_assoc, mul_one, mul_zero, add_assoc, add_right_comm, add_zero, mul_add, mul_comm, mul_left_comm] at h ⊢
  ring_nf at h ⊢
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 12 * x ^ 5 + 15 * x ^ 4 + 4 * x ^ 2 + 11 * x + 4) (Icc (0: ℝ) (5: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Ici_self)
  apply MonotoneOn.add
  all_goals apply MonotoneOn.const_mul
  all_goals exact MonotoneOn.pow (fun _ _ ↦ by rfl)
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num

example: MonotoneOn (λ x ↦ 17 * x ^ 4 + 6 * x ^ 3 + 2 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 2 + 7 / 10), sq_nonneg (y ^ 2 + 7 / 10), sq_nonneg (x - y),
    sq_nonneg (x + y), sq_nonneg (x + y - 1), sq_nonneg (x + y + 1)]

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 10 * x ^ 5 + 13 * x ^ 4 + 3 * x) (Icc (0: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx
  intro y hy
  simp_all only [Set.mem_Icc, and_imp]
  intro hx0 hx1 hy0 hy1
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 12 * x ^ 5 + 14 * x ^ 4 + 12 * x ^ 2 + 7 * x) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y), sq_nonneg (x - y)]
  <;> assumption

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 12 * x ^ 4 + 18 * x ^ 3 + 8) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono
  exact fun _ hx _ _ h => by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3),
      sq_nonneg (x + 1), sq_nonneg (x + 2), sq_nonneg (x + 3)]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 9 * x ^ 5 + 5 * x ^ 3) (Icc (0: ℝ) (3: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  apply MonotoneOn.add
  all_goals nlinarith [sq_nonneg x, sq_nonneg (x ^ 3), sq_nonneg (x ^ 5), sq_nonneg (x ^ 7)]

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 15 * x ^ 5 + 15 * x ^ 3 + 15 * x ^ 2 + 7 * x + 3) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx y hy hxy
  simp only [Function.comp_apply, Icc_subset_Icc_iff] at hx hy ⊢
  norm_num
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x) (Icc (0: ℝ) (2: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  apply le_of_not_gt
  intro h
  have h' :=
    MVT x y (fun x => 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x) hxy
  obtain ⟨c, hc, hc'⟩ := h'
  simp only [Set.mem_Icc] at hc
  norm_num at hc'
  linarith [hc.1, hc.2, hxy, hc']

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 9 * x ^ 3 + 18 * x ^ 2 + 12 * x + 16) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  apply MonotoneOn.add
  all_goals
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left hxy (by norm_num)
  <;> apply MonotoneOn.const_mul <;>
  apply MonotoneOn.pow <;>
  exact monotoneOn_id

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 6 * x ^ 6 + 17 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc_def, le_iff_exists_add] at hx hy
  obtain ⟨x_1, rfl⟩ := hx.1
  obtain ⟨y_1, rfl⟩ := hy.1
  ring_nf
  nlinarith

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 12 * x ^ 6 + 12 * x ^ 5 + 3 * x ^ 4 + 7 * x) (Icc (0: ℝ) (8: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 5 * x ^ 3 + 16 * x ^ 2 + 7) (Icc (0: ℝ) (10: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_subset_Icc_iff, le_refl, true_and_iff, le_of_eq,
    zero_le_one, zero_le_two, zero_le_three, zero_le_four, zero_le_five, zero_le_six,
    zero_le_seven, zero_le_eight, zero_le_nine, zero_le_ten]
  nlinarith [sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 20 * x ^ 4 + 4 * x ^ 2 + 18 * x + 15) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.const_add
  apply MonotoneOn.add
  apply MonotoneOn.add
  apply MonotoneOn.mul
  exact monotoneOn_pow 7
  exact monotoneOn_pow 4
  apply MonotoneOn.mul
  exact monotoneOn_pow 2
  exact monotoneOn_id
  exact monotoneOn_const

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 19 * x ^ 5 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (7: ℝ)) := by
  exact fun x hx y hy hxy ↦ by
    simp only [two_mul, mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm]
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 5 * x ^ 6 + 12 * x ^ 5 + 17 * x ^ 4 + 8 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
  <;> simp_all
  <;> linarith

example: MonotoneOn (λ x ↦ 13 * x ^ 6 + 13 * x ^ 5 + 17 * x ^ 4 + 17 * x ^ 3 + 7 * x ^ 2 + 10 * x + 2) (Icc (0: ℝ) (7: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x ^ 2 - 1),
    sq_nonneg (y ^ 2 - 1),
    sq_nonneg (x - y),
    sq_nonneg (x - 1),
    sq_nonneg (y - 1)]

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 11 * x ^ 4 + 8 * x ^ 2 + 20 * x) (Icc (0: ℝ) (5: ℝ)) := by
  apply MonotoneOn.mono _
  intro x hx y hy hxy
  have hx := hx.1
  have hy := hy.2
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2),
    sq_nonneg (2 * x - 2 * y), sq_nonneg (2 * x + 2 * y)]

example: MonotoneOn (λ x ↦ 2 * x ^ 6 + 4 * x ^ 4 + 11 * x ^ 2 + 19 * x + 3) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x + y), hx.1, hx.2, hy.1, hy.2, hxy]

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 14 * x ^ 4 + 12 * x + 10) (Icc (0: ℝ) (2: ℝ)) := by
  apply MonotoneOn.mono _ (Set.Icc_subset_Icc_right (by norm_num : (2 : ℝ) ≤ 2))
  exact
    MonotoneOn.add
      (MonotoneOn.const_mul (fun x hx => by norm_num) (by norm_num : (0 : ℝ) ≤ 9))
      (MonotoneOn.const_mul (fun x hx => by norm_num) (by norm_num : (0 : ℝ) ≤ 14))

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 4 * x ^ 5 + 8 * x ^ 4 + 3 * x ^ 3 + 20 * x ^ 2 + 8 * x) (Icc (0: ℝ) (9: ℝ)) := by
  intro x hx y hy h
  simp only [mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 20 * x ^ 5 + 16 * x ^ 4) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_right (by norm_num))
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]
  <;> linarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]
  <;> norm_num
  <;> assumption
  <;> norm_num
  <;> assumption

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 3 + 20 * x ^ 2 + 17 * x + 8) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx
  intro y hy
  ring_nf
  norm_num
  intro h
  nlinarith [hx.1, hx.2, hy.1, hy.2, h]

example: MonotoneOn (λ x ↦ 16 * x ^ 4 + 10 * x ^ 3 + 13 * x ^ 2) (Icc (0: ℝ) (9: ℝ)) := by
  intro x hx y hy hxy
  have hx' : 0 ≤ x := by
    cases' hx with hx₁ hx₂
    nlinarith
  have hy' : 0 ≤ y := by
    cases' hy with hy₁ hy₂
    nlinarith
  have hxy' : x ≤ y := by
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x ^ 2 + y ^ 2)]

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 6 * x ^ 4 + 7 * x ^ 3 + 12 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 5 * x ^ 6 + 15 * x ^ 4 + 3 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  apply le_of_sub_nonneg
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2),
    sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14) (Icc (0: ℝ) (7: ℝ)) := by
  intro x hx y hy h
  have hx' := hx; have hy' := hy
  simp_all only [Set.mem_Icc]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 20 * x ^ 2 + 14 * x + 20) (Icc (0: ℝ) (3: ℝ)) := by
  intro x hx y hy h
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 16 * x ^ 4 + 5 * x ^ 3 + 19 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  exact fun x hx y hy hxy => by
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2),
      sq_nonneg (x + y), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 5 + 19 * x ^ 4 + 6 * x ^ 3 + 12 * x + 14) (Icc (0: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ <| Icc_subset_Icc_right (by norm_num)
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 + 1), sq_nonneg (y ^ 3 + 1), sq_nonneg (x ^ 2 + 1), sq_nonneg (y ^ 2 + 1),
    sq_nonneg (x + 1), sq_nonneg (y + 1)]

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 3 * x ^ 5 + 8 * x ^ 4 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (4: ℝ)) := by
  apply MonotoneOn.add
  <;> apply MonotoneOn.const_mul
  <;> exact monotone_pow (by norm_num)
  <;> exact (by norm_num : (0:ℝ) ≤ 4)
  <;> exact (by norm_num : (0:ℝ) ≤ 3)
  <;> exact (by norm_num : (0:ℝ) ≤ 8)
  <;> exact (by norm_num : (0:ℝ) ≤ 4)
  <;> exact (by norm_num : (0:ℝ) ≤ 20)

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 2 * x ^ 6 + 9 * x ^ 5 + 10 * x + 13) (Icc (0: ℝ) (9: ℝ)) := by
  apply MonotoneOn.mono _ Icc_subset_Icc_right
  refine' MonotoneOn.add _ _ <;>
  (
    exact
      fun _ ha _ hb hab =>
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (min_le_left _ _) hab _)
          (by linarith [ha.1, ha.2, hb.1, hb.2])
  )

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 11 * x ^ 5 + 20 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 12 * x + 3) (Icc (0: ℝ) (3: ℝ)) := by
  intro x hx y hy h
  simp_all only [Icc_subset_Icc_iff, le_refl, true_and, le_of_lt, and_true]
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x ^ 2 - x * y), sq_nonneg (x * y - y ^ 2)]

example: MonotoneOn (λ x ↦ 15 * x ^ 4 + 19 * x + 13) (Icc (0: ℝ) (7: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [mul_comm, mul_one] at hx hy
  norm_num
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2)]

example: MonotoneOn (λ x ↦ 7 * x ^ 4 + 6 * x ^ 3 + 14 * x ^ 2 + 6) (Icc (0: ℝ) (5: ℝ)) := by
  refine' MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x + y + 1)]

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 9 * x ^ 5 + 14 * x ^ 4 + 3 * x ^ 2 + 17) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ (Set.Icc_subset_Ici_self)
  exact fun x hx y hy hxy ↦ by
    simp_all only [Set.mem_Icc, Set.mem_Ici, le_refl, true_and_iff, and_true_iff]
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3),
      sq_nonneg (x ^ 2 - y ^ 2),
      sq_nonneg (x - y),
      sq_nonneg (x + y),
      sq_nonneg (x ^ 2 + y ^ 2),
      sq_nonneg (x ^ 3 + y ^ 3)]

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 14 * x ^ 4 + 18 * x ^ 3 + 3 * x ^ 2 + 8 * x) (Icc (0: ℝ) (7: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  intro x hx y hy hxy
  simp only [mul_assoc, mul_one, mul_add, add_assoc, add_left_comm, add_comm] at hx hy ⊢
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 + y ^ 2),
    sq_nonneg (x ^ 3 + y ^ 3), hx, hy]

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 19 * x ^ 5 + 13 * x ^ 4 + 4 * x ^ 2 + 8 * x + 12) (Icc (0: ℝ) (10: ℝ)) := by
  apply MonotoneOn.mono _ <| Icc_subset_Icc (by norm_num) (by norm_num)
  intro x hx y hy hxy
  simp only [mul_comm]
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 13 * x ^ 2 + 12 * x) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  simp only [Icc_def, mem_setOf_eq] at hx hy
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 13 * x ^ 6 + 18 * x ^ 5 + 15 * x ^ 4 + 9 * x ^ 3 + 17 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (x ^ 2 + x), sq_nonneg (y ^ 3 + y ^ 2),
    sq_nonneg (y ^ 2 + y)]

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [mem_Icc] at hx hy
  apply le_of_not_lt
  intro h
  have h' :=
    calc
      20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2 ≤
          20 * y ^ 6 + 14 * y ^ 5 + 3 * y ^ 4 + 13 * y ^ 2 := by
        nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
      _ < 20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2 := by nlinarith
  linarith

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 8 * x ^ 5 + 3 * x ^ 3 + 18 * x ^ 2 + 2 * x) (Icc (0: ℝ) (7: ℝ)) := by
  apply MonotoneOn.add
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x - y), sq_nonneg (x ^ 5 - y ^ 5), sq_nonneg (x ^ 7 - y ^ 7)]
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2),
    sq_nonneg (x - y), sq_nonneg (x ^ 5 - y ^ 5), sq_nonneg (x ^ 7 - y ^ 7)]
  <;> norm_num
  <;> norm_num
  <;> linarith
  <;> linarith

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 2 + 8 * x + 7) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono
  apply MonotoneOn.add
  <;> exact fun x hx y hy hxy => by
    simp only [mul_assoc, mul_comm, mul_left_comm]
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
  <;> exact fun x hx y hy hxy => by
    simp only [mul_assoc, mul_comm, mul_left_comm]
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
  <;> exact fun x hx y hy hxy => by
    simp only [mul_assoc, mul_comm, mul_left_comm]
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
  <;> exact fun x hx y hy hxy => by
    simp only [mul_assoc, mul_comm, mul_left_comm]
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 4 * x ^ 6 + 16 * x ^ 5 + 11 * x ^ 4 + 5 * x ^ 3 + 15 * x ^ 2 + 20) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx
  intro y hy
  simp only [Set.mem_Icc] at hx hy ⊢
  intro h
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x ^ 3 + y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2)]

example: MonotoneOn (λ x ↦ 18 * x ^ 4 + 14 * x ^ 3 + 8 * x ^ 2 + 13 * x + 11) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Icc_left (by norm_num))
  exact
    MonotoneOn.of_deriv_nonneg
      (by
        intro x hx
        simp
        nlinarith [sq_nonneg x, sq_nonneg (x + 1 / 3), sq_nonneg (x + 2 / 3),
          sq_nonneg (x + 1), sq_nonneg (x + 4 / 3), sq_nonneg (x + 5 / 3),
          sq_nonneg (x + 2), sq_nonneg (x + 7 / 3), sq_nonneg (x + 8 / 3),
          sq_nonneg (x + 3), sq_nonneg (x + 9 / 3), sq_nonneg (x + 10 / 3)]
        )
      (by
        intro x hx
        simp
        nlinarith [sq_nonneg x, sq_nonneg (x + 1 / 3), sq_nonneg (x + 2 / 3),
          sq_nonneg (x + 1), sq_nonneg (x + 4 / 3), sq_nonneg (x + 5 / 3),
          sq_nonneg (x + 2), sq_nonneg (x + 7 / 3), sq_nonneg (x + 8 / 3),
          sq_nonneg (x + 3), sq_nonneg (x + 9 / 3), sq_nonneg (x + 10 / 3)]
        )

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 10 * x ^ 6 + 11 * x ^ 4 + 10 * x ^ 3 + 13) (Icc (0: ℝ) (1: ℝ)) := by
  apply MonotoneOn.mono
  intro x hx
  have h1 : 0 ≤ x := by exact hx.1
  have h2 : x ≤ 1 := by exact hx.2
  nlinarith [pow_nonneg h1 7, pow_nonneg h1 6, pow_nonneg h1 4, pow_nonneg h1 3]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 17 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 2 + 2 * x + 10) (Icc (0: ℝ) (1: ℝ)) := by
  intro x hx y hy h
  norm_num at hx hy
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (y - 1),
    sq_nonneg (x + 1), sq_nonneg (y + 1)]

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 12 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x ^ 2 - 2 * x * y + y ^ 2)]

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 6 * x ^ 6 + 6 * x ^ 5 + 10 * x ^ 4 + 2 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (8: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y),
    sq_nonneg (x ^ 3 - x ^ 2 * y), sq_nonneg (x ^ 2 * y - x * y ^ 2), sq_nonneg (x * y ^ 2 - y ^ 3)]

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 2 + 8 * x) (Icc (0: ℝ) (5: ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 2), sq_nonneg (y ^ 3), sq_nonneg (y ^ 2),
    sq_nonneg (x ^ 3 + x ^ 2), sq_nonneg (y ^ 3 + y ^ 2)]

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 15 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
  apply MonotoneOn.mono _ (Icc_subset_Ici_self)
  intro x hx y hy hxy
  simp only [mul_comm, mul_left_comm, mul_assoc, mul_add]
  nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11) (Icc (0: ℝ) (6: ℝ)) := by
  intro x hx y hy hxy
  have h := mvt_on_Icc (fun x ↦ 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11) hx hy hxy
  simp at h
  exact h

