import Mathlib
open Real Set

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 5 * x ^ 5 - 82 * x ^ 2 + 127 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro h
  simp_all [h]
  constructor
  <;> norm_num
  <;> linarith [deriv_sq_nonneg (fun x => 2 * x ^ 6 + 5 * x ^ 5 - 82 * x ^ 2 + 127 * x) 1]
  <;> simp_all
  <;> linarith [deriv_sq_nonneg (fun x => 2 * x ^ 6 + 5 * x ^ 5 - 82 * x ^ 2 + 127 * x) 1]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - x ^ 3  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intro h
  simp_all [deriv_const, deriv_sub, deriv_mul, deriv_pow]
  <;> simp
  <;> norm_num
  <;> apply And.intro <;> simp [deriv_const, deriv_sub, deriv_mul, deriv_pow] <;> simp
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 17 * x ^ 2 + 96 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_neg,
    deriv_comp, deriv_add, deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'',
    deriv_neg, deriv_comp, deriv_add]
  norm_num
  <;> linarith [deriv_sq_nonneg (fun x : ℝ => x ^ 2 - 17 * x + 96) 6]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 121 * x ^ 2 + 324 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intro h
  simp_all only [deriv_const', deriv_add, deriv_sub, deriv_mul, deriv_pow, Nat.cast_bit0, Nat.cast_one,
    deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_pow,
    Nat.cast_bit0, Nat.cast_one, deriv_pow, Nat.cast_bit0, Nat.cast_one]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 + 30 * x ^ 2 + 60 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  intro h
  simp [h, deriv_add, deriv_mul, deriv_const, deriv_pow, Nat.cast_bit1, Nat.cast_one, Nat.cast_bit0]
  norm_num
  <;> simp
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 + 4 * x ^ 4 - 3726 * x ^ 2 - 17388 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intro h
  simp only [h]
  norm_num [deriv_const, deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_neg,
    deriv_comp, deriv_id'', deriv_pow, deriv_sub, deriv_mul, deriv_const,
    deriv_comp, deriv_id'']
  constructor
  <;> norm_num
  <;> apply And.intro
  <;> norm_num
  <;> apply And.intro
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intro h
  simp only [h, deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_id'', zero_mul, zero_add]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + 3 * x ^ 3 + 20 * x - 17 * x ^ 2) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro hf
  simp only [hf]
  constructor
  simp [deriv_add, deriv_pow, deriv_mul, deriv_const, deriv_sub, deriv_id]
  norm_num
  simp [deriv_add, deriv_pow, deriv_mul, deriv_const, deriv_sub, deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 + 2 * x ^ 3 - 214 * x ^ 2 + 1104 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> linarith
  <;> apply HasDerivAt.deriv
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.add
  <;> apply HasDerivAt.sub
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 3 * x ^ 5 - x ^ 4 + 4 * x ^ 3 + 109488 * x - 17230 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro hf
  simp only [hf, deriv_add, deriv_const, deriv_mul, deriv_pow, deriv_sub, deriv_id'', deriv_pow,
    deriv_const, deriv_id'', deriv_pow, deriv_const, deriv_id'', deriv_pow, deriv_const, deriv_id'']
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 36 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all only [deriv_add, deriv_mul, deriv_const, deriv_pow, Nat.cast_bit0, Nat.cast_one,
    deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_add, deriv_mul, deriv_const, deriv_pow,
    Nat.cast_bit0, Nat.cast_one, deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_add, deriv_mul,
    deriv_const, deriv_pow, Nat.cast_bit0, Nat.cast_one, deriv_pow, Nat.cast_bit0, Nat.cast_one]
  constructor
  norm_num
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - 4 * x ^ 3 - 93166 * x ^ 2 - 896376 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_const', deriv_add, deriv_sub, deriv_pow, deriv_mul, deriv_C, deriv_id'',
    deriv_comp, deriv_pow, deriv_mul, deriv_C, deriv_id'', zero_add, zero_sub, sub_zero, mul_one,
    mul_zero, sub_neg_eq_add, neg_mul_eq_neg_mul, mul_neg, mul_zero, zero_mul, mul_neg, neg_neg,
    mul_one, mul_zero, mul_neg, neg_mul_eq_neg_mul, neg_neg]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - x ^ 4 - 214 * x ^ 2 + 987 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_pow, deriv_sub, deriv_add, deriv_id'', deriv_const', deriv_pow,
    deriv_sub, deriv_add, deriv_id'', deriv_const', deriv_pow, deriv_sub, deriv_add, deriv_id'',
    deriv_const']
  norm_num
  <;> linarith [deriv_pow 5 3, deriv_pow 4 3, deriv_pow 2 3]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 15 * x ^ 2 + 15 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intro h
  simp_all [deriv_pow]
  ring_nf
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 5 * x ^ 4 - 4 * x ^ 3 - 258 * x ^ 2 + 840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intro h
  simp_all [deriv_const, deriv_add, deriv_sub, deriv_mul, deriv_pow]
  constructor <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 - 4319 * x ^ 2 + 38868 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro h
  rw [h]
  norm_num
  constructor
  <;> norm_num
  <;> linarith [deriv_mul (fun x => 2 * x ^ 5) (fun x => -4319 * x ^ 2 + 38868 * x) 6]
  <;> linarith [deriv_mul (fun x => -4319 * x ^ 2) (fun x => 38868 * x) 6]
  <;> linarith [deriv_const 38868 6]
  <;> linarith [deriv_pow 5 6]
  <;> linarith [deriv_pow 2 6]
  <;> linarith [deriv_id 6]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro h
  simp_all only [deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow, deriv_id',
    deriv_const', deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow, deriv_id']
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_const, deriv_mul, deriv_pow, Nat.cast_bit0, Nat.cast_one,
    deriv_id'', zero_add, zero_mul, mul_one, mul_zero, bit0_zero, add_zero, sub_zero,
    mul_comm 2]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all [deriv_add, deriv_mul, deriv_pow, deriv_const]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 75 * x ^ 2 + 375 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intro h
  simp_all only [deriv_const', deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_const, zero_mul,
    zero_sub, zero_add, one_mul, deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_const, zero_mul,
    zero_sub, zero_add, one_mul, deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_const, zero_mul,
    zero_sub, zero_add, one_mul]
  norm_num
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_pow, deriv_const, zero_mul, zero_add, zero_sub, sub_zero, mul_one, mul_neg, mul_zero, neg_neg, neg_zero]
  constructor <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 2 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro hf
  simp only [hf, deriv_add, deriv_pow, deriv_mul, deriv_id'', deriv_const', deriv_pow, Nat.cast_one,
    Nat.cast_zero, Nat.cast_succ, deriv_add, deriv_mul, deriv_id'', deriv_const', deriv_pow, Nat.cast_one,
    Nat.cast_zero, Nat.cast_succ, deriv_add, deriv_mul, deriv_id'', deriv_const', deriv_pow, Nat.cast_one,
    Nat.cast_zero, Nat.cast_succ]
  constructor <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 18 * x ^ 2 + 108 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith
  <;> simp_all only [pow_one, mul_one, mul_zero, add_zero]
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, add_zero]
  <;> linarith
  <;> simp_all only [mul_one, mul_zero, add_zero]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 5 * x ^ 3 - 2635 * x - 376 * x ^ 2) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intro hf
  rw [hf]
  simp [deriv_add, deriv_mul, deriv_pow, deriv_const]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> nlinarith
  <;> apply_rules [deriv_const, deriv_pow, deriv_sub, deriv_mul, deriv_id, deriv_const', deriv_pow',
    deriv_sub', deriv_mul', deriv_id', deriv_const, deriv_pow, deriv_sub, deriv_mul, deriv_id,
    deriv_const', deriv_pow', deriv_sub', deriv_mul', deriv_id']
  <;> simp_all
  <;> nlinarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 6 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro h
  rw [h]
  norm_num
  constructor
  <;> simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro hf
  rw [hf]
  simp [deriv]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 2 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) < 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith [deriv_sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 12 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_mul, deriv_const, deriv_id'', deriv_pow, one_mul, mul_one, mul_zero,
    add_zero, zero_mul, sub_zero]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - x ^ 5 + 3 * x ^ 3 - 60426 * x ^ 2 - 578988 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all only [deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'',
    h, Nat.cast_ofNat, zero_add, zero_sub, add_zero, sub_zero, Nat.cast_one, one_mul,
    mul_one, mul_zero, zero_mul, sub_neg_eq_add]
  norm_num
  <;> norm_num <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 8 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro h
  simp [h, deriv_add, deriv_mul, deriv_const, deriv_pow, Nat.cast_ofNat]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 4 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_add, deriv_const, deriv_mul, deriv_id'', deriv_pow, Nat.cast_one,
    Nat.cast_zero, Nat.cast_succ, Nat.cast_zero, Nat.cast_one, deriv_pow, Nat.cast_one,
    Nat.cast_zero, Nat.cast_succ, Nat.cast_zero, Nat.cast_one]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 + 80 * x + 22 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith [hasDerivAt_id (-4 : ℝ), hasDerivAt_const (-4 : ℝ) 80, hasDerivAt_pow 3 (-4 : ℝ), hasDerivAt_mul_const 2 (-4 : ℝ), hasDerivAt_mul_const 22 (-4 : ℝ)]
  <;> simp_all only [mul_one, mul_zero, add_zero, mul_neg, mul_comm]
  <;> apply hasDerivAt_id
  <;> apply hasDerivAt_const
  <;> apply hasDerivAt_pow
  <;> apply hasDerivAt_mul_const
  <;> apply hasDerivAt_mul_const

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 + 5 * x ^ 3 - 39 * x ^ 2 + 47 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intro h
  simp_all only [deriv_add, deriv_mul, deriv_pow, deriv_const, zero_add, zero_sub, zero_mul,
    zero_pow, zero_sub, sub_zero, sub_neg_eq_add, neg_mul, neg_neg, mul_neg, mul_zero, neg_zero]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 - x ^ 4 - 2347 * x ^ 2 + 17720 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow,
    deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow, deriv_sub, deriv_const,
    deriv_mul, deriv_pow, deriv_id'', deriv_pow]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 9 * x ^ 2 + 27 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro h
  rw [h]
  constructor
  <;> simp [deriv_sub, deriv_pow, deriv_id', deriv_const, deriv_mul, deriv_add, deriv_pow, deriv_id',
    deriv_const, deriv_mul, deriv_add, deriv_pow, deriv_id', deriv_const, deriv_mul, deriv_add,
    deriv_pow, deriv_id', deriv_const, deriv_mul, deriv_add]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intro h
  simp_all [deriv_pow, deriv_mul, deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 + 9 * x ^ 2 + 12 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro hf
  simp only [hf]
  constructor
  <;> norm_num [deriv_add, deriv_mul, deriv_const, deriv_pow]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 20 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith
  <;> simp_all only [deriv_const, deriv_mul, deriv_sub, deriv_pow, deriv_id'', deriv_const',
      deriv_pow, deriv_id'', deriv_const, deriv_mul, deriv_sub, deriv_pow, deriv_id'',
      deriv_const', deriv_pow, deriv_id'', deriv_const, deriv_mul, deriv_sub, deriv_pow,
      deriv_id'', deriv_const', deriv_pow, deriv_id'']
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 4 * x ^ 4 + 5 * x ^ 3 - 13 * x ^ 2 + 40 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intro h
  simp [h, deriv_pow, deriv_add, deriv_sub, deriv_mul, deriv_const]
  norm_num
  <;> linarith [deriv_pow_two_eq_mul_nat_succ (fun x => x ^ 3) 1,
    deriv_pow_two_eq_mul_nat_succ (fun x => x ^ 2) 1,
    deriv_pow_two_eq_mul_nat_succ (fun x => x) 1]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 121 * x ^ 2 - 616 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro h
  simp_all only [h, neg_mul, neg_sub, mul_neg, mul_one, sub_neg_eq_add, add_assoc, add_left_comm,
    add_right_comm, add_assoc]
  norm_num
  <;> apply And.intro
  <;> apply HasDerivAt.deriv
  <;> apply HasDerivAt.add
  <;> apply HasDerivAt.mul_const
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const_sub
  <;> apply HasDerivAt.neg
  <;> apply HasDerivAt.mul_deriv
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const_sub
  <;> apply HasDerivAt.neg
  <;> apply HasDerivAt.mul_deriv
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const_sub
  <;> apply HasDerivAt.neg
  <;> apply HasDerivAt.mul_deriv
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const_sub
  <;> apply HasDerivAt.neg
  <;> apply HasDerivAt.mul_deriv

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + x ^ 4 + x ^ 3 + 8445 * x ^ 2 + 76176 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro hf
  simp only [hf]
  norm_num [deriv_const, deriv_add, deriv_mul, deriv_pow]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + x ^ 3 + 279 * x ^ 2 + 1242 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intro hf
  simp_all only [hf, deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_id'',
    Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_singleton, Finset.sum_range_zero,
    Nat.cast_one, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero,
    Nat.cast_succ, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero,
    Nat.cast_succ, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero, Nat.cast_succ, Nat.cast_zero,
    Nat.cast_succ, Nat.cast_zero]
  norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 4 * x ^ 5 + 3 * x ^ 4 + 4 * x ^ 3 - 42387 * x ^ 2 + 340820 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intro h
  simp_all only [deriv_const', deriv_pow, deriv_add, deriv_sub, deriv_mul, deriv_X, deriv_C, zero_sub, zero_mul, zero_add, sub_zero, mul_one, mul_zero, sub_neg_eq_add, add_zero, mul_comm, mul_left_comm, mul_assoc, pow_one, pow_two, deriv_pow, deriv_mul, deriv_X, deriv_C, mul_one, mul_zero, sub_zero, zero_add, sub_neg_eq_add, mul_comm, mul_left_comm, mul_assoc, pow_one, pow_two, deriv_pow, deriv_mul, deriv_X, deriv_C, mul_one, mul_zero, sub_zero, zero_add, sub_neg_eq_add, mul_comm, mul_left_comm, mul_assoc, pow_one, pow_two, deriv_pow, deriv_mul, deriv_X, deriv_C, mul_one, mul_zero, sub_zero, zero_add, sub_neg_eq_add, mul_comm, mul_left_comm, mul_assoc, pow_one, pow_two]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 + x ^ 4 + 2 * x ^ 3  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intro h
  simp_all only [deriv_add, deriv_const, deriv_mul, deriv_pow, deriv_id'', pow_one, zero_mul,
    zero_add, mul_zero, mul_one, zero_sub, sub_zero, one_mul, mul_comm]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 2 * x ^ 3 - 170 * x ^ 2 + 944 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intro h
  simp_all only [deriv_sub, deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id'',
    deriv_pow, deriv_const, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 2 * x ^ 4 - x ^ 3 - 2996 * x ^ 2 + 18128 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) = 0) := by
  intro hf
  simp_all only [deriv_const, zero_mul, zero_add, zero_sub, mul_zero, mul_one, mul_neg,
    neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc]
  norm_num
  constructor <;> linarith [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_pow, deriv_id,
    deriv_const', deriv_id']

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 20 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp_all only [deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_pow, pow_two,
    deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_pow, pow_two,
    deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_pow, pow_two]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 - 158 * x ^ 2 + 768 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intro hf
  simp_all only [deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_id'', pow_one, pow_two,
    pow_three, mul_one, mul_zero, add_zero, zero_add, mul_neg, mul_assoc]
  norm_num
  norm_num
  norm_num
  norm_num
  norm_num
  linarith [deriv_pow_succ 4 3, deriv_pow_succ 3 2, deriv_pow_succ 2 1, deriv_pow_succ 1 0]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 4 * x ^ 3 - 71 * x ^ 2 + 106 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  rw [h]
  norm_num
  constructor <;>
  simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id] <;>
  norm_num
  <;>
  linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 16 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  simp_all [deriv]
  constructor
  <;> norm_num
  <;> linarith [hasDerivAt_id 4]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3  - 3 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_pow, deriv_sub, deriv_id'', deriv_const', deriv_mul, deriv_pow, deriv_sub,
    deriv_id'', deriv_const', deriv_mul, deriv_pow, deriv_sub, deriv_id'', deriv_const', deriv_mul]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3  + 2 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> linarith
  <;> simp_all only [h]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 + x ^ 3 - 27 * x ^ 2 - 37 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  intro h
  rw [h]
  simp only [deriv_add, deriv_sub, deriv_pow, deriv_const, deriv_mul, deriv_id'', zero_add, zero_sub,
    zero_mul, sub_zero, mul_one, mul_zero, mul_assoc, mul_comm, mul_left_comm]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 8 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  rw [h]
  constructor
  simp [deriv_pow]
  norm_num
  simp [deriv_pow]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 180 * x ^ 2 + 1512 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intro hf
  rw [hf]
  simp only [deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id, deriv_pow,
    deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id, deriv_pow, deriv_add, deriv_sub,
    deriv_const, deriv_mul, deriv_id, deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul,
    deriv_id, deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - x ^ 5 + x ^ 4 + 3 * x ^ 3 - 1164 * x ^ 2 + 3708 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intro h
  simp only [h, deriv_sub, deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_id'',
    zero_sub, zero_add, zero_mul, sub_zero, mul_one]
  norm_num
  <;> simp [h]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 18 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro h
  simp only [h]
  constructor
  <;> norm_num
  <;> linarith [deriv_sq_pos_of_deriv_pos (by norm_num : (fun x:ℝ => 3 * x ^ 2 + 18 * x) = fun x:ℝ => 3 * x ^ 2 + 18 * x)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - x ^ 3 - 397 * x ^ 2 - 2104 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro h
  simp only [h]
  constructor
  <;> norm_num
  <;> linarith
  <;> apply HasDerivAt.hasDerivAt_of_hasDerivAt_of_ne
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.sub
  <;> apply HasDerivAt.pow
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.sub
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.sub
  <;> apply HasDerivAt.const_mul
  <;> apply HasDerivAt.sub
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.const
  <;> apply HasDerivAt.id

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 - 59958 * x ^ 2 - 575316 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all
  constructor
  all_goals
    norm_num
    linarith [deriv_const' 0, deriv_const' 1, deriv_const' 2, deriv_const' 3, deriv_const' 4, deriv_const' 5]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 + 11 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro h
  simp only [h, deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_pow, one_mul, Nat.cast_one,
    sub_zero, zero_add]
  norm_num
  <;> linarith [deriv_sub (deriv_pow' 5 1) (deriv_pow' 4 1),
    deriv_sub (deriv_pow' 3 1) (deriv_pow' 2 1)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 1200 * x ^ 2 + 3840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) = 0) := by
  intro hf
  simp_all only [deriv_const', deriv_add', deriv_sub', deriv_mul', deriv_pow', deriv_id'',
    deriv_const, zero_mul, zero_sub, zero_add, mul_one, sub_zero, mul_zero, sub_neg_eq_add]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intro h
  simp_all
  exact ⟨by simp [deriv], by simp [deriv]⟩

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + x ^ 4 + 5 * x ^ 3 - 38 * x ^ 2 + 47 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro hf
  simp only [hf]
  constructor
  <;> norm_num
  <;> ring_nf
  <;> linarith [deriv_one_pow 5, deriv_one_pow 4, deriv_one_pow 3, deriv_one_pow 2]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 8 * x ^ 2 + 7 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intro h
  simp_all only [deriv_add, deriv_const, deriv_mul, deriv_pow, one_mul, zero_mul, zero_add,
    deriv_id'', deriv_pow, pow_one, pow_two, deriv_add, deriv_mul, deriv_pow, one_mul,
    zero_mul, zero_add, deriv_id'', deriv_pow, pow_one, pow_two]
  norm_num
  <;> linarith [deriv_mul (fun x => x + 1) (fun x => x + 1)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - 5 * x ^ 5 - 5 * x ^ 4 - 3 * x ^ 3 + 2 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intro h
  simp [h]
  norm_num
  <;>
  constructor <;>
  linarith [hasDerivAt_pow 6 (0:ℝ),
    hasDerivAt_pow 5 (0:ℝ),
    hasDerivAt_pow 4 (0:ℝ),
    hasDerivAt_pow 3 (0:ℝ),
    hasDerivAt_pow 2 (0:ℝ)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 10 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intro hf
  rw [hf]
  simp [deriv_add, deriv_pow, deriv_const, deriv_id, deriv_mul, deriv_pow, deriv_const, deriv_id,
    deriv_add, deriv_pow, deriv_const, deriv_id, deriv_mul, deriv_pow, deriv_const, deriv_id]
  norm_num
  <;> norm_num <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - x ^ 3 - 16 * x ^ 2 + 44 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith [deriv_fderiv.mpr (differentiable_fderiv.mpr (by simp [h]; ring_nf; nlinarith))]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + x ^ 3 - 29115 * x - 6063 * x ^ 2) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro hf
  simp only [hf]
  norm_num [deriv_add, deriv_sub, deriv_pow, deriv_const, deriv_mul, deriv_id,
    deriv_comp, deriv_pow, deriv_const, deriv_mul, deriv_id, deriv_comp,
    deriv_pow, deriv_const, deriv_mul, deriv_id, deriv_comp, deriv_pow, deriv_const,
    deriv_mul, deriv_id, deriv_comp]
  norm_num
  <;> apply And.intro <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 8 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> simp [deriv_add, deriv_const, deriv_pow, deriv_id, deriv_mul, deriv_const, deriv_pow, deriv_id,
    deriv_mul, deriv_const, deriv_pow, deriv_id, deriv_mul, deriv_const, deriv_pow, deriv_id,
    deriv_mul, deriv_const, deriv_pow, deriv_id, deriv_mul]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 57 * x ^ 2 + 360 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) < 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> linarith [deriv_cube 6, deriv_sq 6]
  <;> simp_all only [h, deriv_const, deriv_add, deriv_mul, deriv_pow, deriv_id']
  <;> norm_num
  <;> linarith [deriv_cube 6, deriv_sq 6]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 16 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro h
  simp only [h]
  constructor
  simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id, mul_one, one_mul, zero_add]
  norm_num
  simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id, mul_one, one_mul, zero_add]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 12 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, Nat.cast_one, one_mul,
    Nat.cast_zero, zero_mul, sub_zero, zero_sub, mul_one, mul_neg, mul_zero, neg_zero]
  constructor
  <;> norm_num
  <;> linarith [deriv_two_mul_deriv_sub_deriv_mul_deriv (fun x => x ^ 2) (fun x => 3) (fun x => x) 2]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 39 * x ^ 2 + 126 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro h
  simp_all
  norm_num
  constructor
  <;> norm_num
  <;> linarith [hasDerivAt_pow 3 (-3)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 72 * x ^ 2 + 432 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> linarith [hasDerivAt_pow 3 (-6)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all only [deriv_const', deriv_add', deriv_mul, deriv_pow, Nat.cast_one, Nat.cast_zero, Nat.cast_succ,
    Nat.zero_eq, Nat.zero_add, Nat.one_eq_succ_zero]
  norm_num
  linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 4 * x ^ 3 - 48 * x ^ 2 - 84 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  intro h
  simp only [h]
  constructor <;> norm_num
  <;> simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow,
    deriv_id, deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow, deriv_id,
    deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow, deriv_id, deriv_pow]
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 749 * x ^ 2 + 4990 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_const', deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_const, zero_sub,
    zero_mul, sub_zero, zero_add, mul_one, mul_zero, mul_assoc, mul_comm]
  norm_num
  <;> linarith [show (2 : ℝ) = 2 * 1 by norm_num]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 176 * x + 46 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro h
  simp_all [deriv_pow, deriv_add, deriv_mul, deriv_const]
  norm_num
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 4 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro h
  simp_all only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id, zero_add, zero_mul,
    zero_sub, sub_zero, sub_neg_eq_add, add_zero, add_left_neg, mul_one, mul_zero, mul_neg,
    neg_add_rev, neg_mul_eq_neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc, mul_add,
    add_mul]
  norm_num
  <;> linarith [deriv_two_mul_deriv_pow_two f (-1)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 12 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro hf
  simp only [hf]
  constructor
  <;> simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 16 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro hf
  simp_all only [h

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 12 * x ^ 2 + 19 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro h
  simp_all
  constructor
  norm_num [deriv_const, deriv_pow, deriv_sub, deriv_mul, deriv_id, pow_one]
  norm_num [deriv_const, deriv_pow, deriv_sub, deriv_mul, deriv_id, pow_one]
  <;> linarith
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + x ^ 5 + x ^ 4 - 5 * x ^ 3 - 54 * x ^ 2 - 76 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro h
  simp_all
  norm_num
  <;> linarith [deriv_cubic_at_minus_one, deriv_deriv_cubic_at_minus_one]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 150 * x ^ 2 + 1000 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intro hf
  simp_all
  constructor <;> norm_num [deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + 42 * x ^ 2 + 64 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro h
  simp_all
  constructor
  <;> norm_num
  <;> linarith [deriv_cubic (-1 : ℝ)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 21 * x ^ 2 + 36 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro h
  rw [h]
  constructor
  simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  norm_num
  simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 10 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_sub, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_pow,
    deriv_const, deriv_id'', deriv_sub, deriv_mul, deriv_id'', deriv_pow, deriv_const,
    deriv_id'', deriv_sub, deriv_mul, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 46 * x ^ 2 + 235 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intro hf
  rw [hf]
  constructor
  rw [deriv_cubic]
  norm_num
  rw [deriv_deriv_cubic]
  norm_num
  <;> linarith
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 69 * x ^ 2 + 392 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  rw [h]
  norm_num [deriv_pow, deriv_sub, deriv_mul, deriv_add, deriv_id, deriv_const]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 4 * x ^ 2 + 5 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow,
    deriv_sub, deriv_const, deriv_mul, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 32 * x + 10 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro hf
  simp only [hf]
  constructor
  rw [deriv_add]
  · rw [deriv_pow]
    norm_num
    rw [deriv_const]
    norm_num
    rw [deriv_mul]
    norm_num
    rw [deriv_pow]
    norm_num
    rw [deriv_const]
    norm_num
    rw [deriv_id]
    norm_num
  · rw [deriv_add]
    · rw [deriv_pow]
      norm_num
      rw [deriv_const]
      norm_num
      rw [deriv_mul]
      norm_num
      rw [deriv_pow]
      norm_num
      rw [deriv_const]
      norm_num
      rw [deriv_id]
      norm_num
    · rw [deriv_pow]
      norm_num
      rw [deriv_const]
      norm_num
      rw [deriv_id]
      norm_num
  norm_num
  <;> try linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 48 * x ^ 2 - 128 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  intro h
  simp_all only [h, deriv_const', deriv_pow'', deriv_sub, deriv_mul, deriv_add, deriv_neg,
    deriv_id'', pow_one, mul_one, mul_zero, sub_zero, zero_add, zero_sub, neg_neg, neg_zero,
    zero_mul, add_zero, mul_assoc]
  norm_num
  <;> linarith
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 60 * x ^ 2 + 300 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intro h
  simp_all
  constructor <;> norm_num
  <;> linarith [hasDerivAt_pow 3 (-5)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 3 * x ^ 5 + 2 * x ^ 4 + 2 * x ^ 3 - 122 * x ^ 2 + 185 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id'', deriv_sub,
    deriv_neg, zero_add, zero_sub, zero_mul, sub_zero, mul_one, mul_zero, add_zero, sub_neg_eq_add,
    deriv_comp, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_id'',
    deriv_sub, deriv_neg, zero_add, zero_sub, zero_mul, sub_zero, mul_one, mul_zero, add_zero,
    sub_neg_eq_add, deriv_comp, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_mul, deriv_const,
    deriv_id'', deriv_sub, deriv_neg, zero_add, zero_sub, zero_mul, sub_zero, mul_one, mul_zero,
    add_zero, sub_neg_eq_add, deriv_comp, deriv_exp, deriv_log, deriv_pow, deriv_add, deriv_mul,
    deriv_const, deriv_id'', deriv_sub, deriv_neg, zero_add, zero_sub, zero_mul, sub_zero, mul_one,
    mul_zero, add_zero, sub_neg_eq_add]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 76 * x ^ 2 + 385 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intro h
  simp only [h]
  constructor
  simp [deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_id]
  norm_num
  simp [deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 4 * x ^ 5 + 5 * x ^ 4 - x ^ 3 - 105 * x - 69 * x ^ 2) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_const, deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_id'',
    Nat.cast_bit1, Nat.cast_bit0, Nat.cast_one, Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  <;> simp_all
  <;> linarith
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 - 3 * x ^ 4 - 4 * x ^ 3 + 289872 * x - 29520 * x ^ 2) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intro hf
  simp_all only [Function.funext_iff, deriv_sub, deriv_const', deriv_add, deriv_mul, deriv_pow,
    deriv_C, deriv_X, zero_mul, zero_add, zero_sub, sub_zero, mul_one, mul_zero, sub_self,
    add_zero]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  simp_all
  constructor
  norm_num
  norm_num
  <;> linarith [deriv_sq_pos (fun x:ℝ => 2 * x ^ 2 - 4 * x) 1]
  <;> simp_all
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + 2 * x ^ 3 + 45 * x ^ 2 + 64 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_const, zero_add, zero_mul, zero_sub, sub_zero, mul_one, mul_zero,
    mul_neg, mul_assoc, mul_comm, mul_left_comm]
  norm_num [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id, deriv_neg, pow_one, pow_two,
    pow_three]
  constructor <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 + 9470 * x ^ 2 + 84480 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro h
  simp_all only [h, one_div, mul_neg, mul_one, mul_add, mul_sub, sub_neg_eq_add,
    mul_assoc, mul_comm]
  constructor
  norm_num [deriv]
  norm_num [deriv]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 5 * x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 + 290 * x ^ 2 + 822 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_add,
    deriv_mul, deriv_const, deriv_pow, deriv_add, deriv_mul, deriv_const, deriv_pow,
    deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_add, deriv_mul, deriv_const]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 89 * x ^ 2 + 528 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  simp only [hf]
  constructor
  <;> norm_num [deriv_sub, deriv_const, deriv_mul, deriv_pow]
  <;> linarith
  <;> norm_num [deriv_sub, deriv_const, deriv_mul, deriv_pow]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 5 * x ^ 4 + 2 * x ^ 3 - 28 * x ^ 2 + 45 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro hf
  rw [hf]
  constructor
  simp [deriv_const, deriv_sub, deriv_add, deriv_mul, deriv_pow, mul_one, sub_self, zero_add]
  norm_num
  simp [deriv_const, deriv_sub, deriv_add, deriv_mul, deriv_pow, mul_one, sub_self, zero_add]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 - 18 * x ^ 2 + 54 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro h
  rw [h]
  simp only [deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_id'', zero_sub, zero_add,
    zero_mul, sub_zero, pow_one, pow_two, pow_three]
  constructor <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 38 * x ^ 2 + 160 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intro h
  simp_all
  constructor
  norm_num [deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_add, deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_add]
  norm_num [deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_add, deriv_pow, deriv_mul, deriv_const, deriv_id, deriv_sub, deriv_add]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 3 * x ^ 5 - 50624 * x ^ 2 - 403115 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_bit0
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_bit1
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_neg
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_mul
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_const_mul
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith
  <;> apply deriv_pow
  <;> simp_all only [h]
  <;> norm_num
  <;> nlinarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 5 * x ^ 5 + x ^ 4 - 107 * x ^ 2 - 412 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro h
  rw [h]
  norm_num [deriv_add, deriv_mul, deriv_const, deriv_pow, Nat.cast_zero, Nat.cast_one, Nat.cast_bit0, Nat.cast_bit1, Nat.cast_ofNat]
  <;> simp_all
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 55 * x ^ 2 + 222 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_pow,
    deriv_sub, deriv_const, deriv_mul, deriv_id'']
  norm_num
  <;> simp_all
  <;> apply And.intro <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 + 6804 * x - 1350 * x ^ 2) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro h
  simp_all only [h, deriv_const', deriv_add, deriv_sub, deriv_pow, deriv_mul, deriv_id'',
    deriv_pow, deriv_mul, deriv_id'', deriv_pow, deriv_mul, deriv_id'']
  constructor <;> norm_num
  <;> simp_all only [h, deriv_const', deriv_add, deriv_sub, deriv_pow, deriv_mul, deriv_id'',
    deriv_pow, deriv_mul, deriv_id'']
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 6 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_sub, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_pow,
    deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_sub, deriv_const, deriv_mul,
    deriv_id'', deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow]
  norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 6 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro h
  simp_all
  constructor
  rw [deriv_pow]
  simp
  ring_nf
  linarith
  rw [deriv_sub]
  simp_all [deriv_pow]
  ring_nf
  linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> ring_nf
  <;> linarith [deriv_sq_eq_iff_has_deriv_at.mp (hasDerivAt_pow 2 6)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 5 * x ^ 3 - 738 * x ^ 2 - 5724 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all only [h, deriv_sub, deriv_const, deriv_mul, deriv_pow, Nat.cast_bit0, Nat.cast_one,
    deriv_add, deriv_id'', deriv_neg, mul_one, mul_zero, sub_zero, zero_sub, zero_mul,
    one_mul, sub_neg_eq_add, zero_add, add_zero]
  norm_num
  apply And.intro <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 2 * x ^ 5 + x ^ 4 - 35150 * x ^ 2 + 282250 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intro h
  simp_all only [h, zero_add, zero_sub, sub_zero, sub_neg_eq_add, sub_self, mul_zero, mul_one, mul_neg,
    mul_assoc]
  norm_num
  constructor
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 480 * x ^ 2 - 2560 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intro h
  simp only [h]
  constructor
  <;> simp [deriv_sub, deriv_const, deriv_mul, deriv_pow, pow_one, pow_two, pow_three,
    mul_assoc, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 2 * x ^ 5 - x ^ 4  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intro h
  simp [h, deriv_pow, deriv_mul, deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_sub, deriv_const]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 12 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro h
  simp_all [deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id, deriv_comp]
  norm_num
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + 3 * x ^ 5 + 2 * x ^ 4 - 3 * x ^ 3 - 9828 * x ^ 2 - 63376 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intro h
  simp only [h]
  norm_num
  constructor <;>
  linarith [deriv_c_mul_x_pow 6 (-4), deriv_c_mul_x_pow 5 (-4), deriv_c_mul_x_pow 4 (-4),
    deriv_c_mul_x_pow 3 (-4), deriv_c_mul_x_pow 2 (-4), deriv_c_mul_x_pow 1 (-4),
    deriv_c_mul_x_pow 0 (-4)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 3 - 253 * x ^ 2 + 740 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intro h
  simp_all only [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id'', deriv_sub,
    deriv_neg, deriv_comp, deriv_pow, deriv_id'', deriv_const, deriv_mul, deriv_pow,
    deriv_id'', deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_const, deriv_mul,
    deriv_pow, deriv_id'', deriv_const, deriv_mul, deriv_pow, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 5 * x ^ 4 + 5 * x ^ 3 - 5175 * x ^ 2 + 24543 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro h
  simp only [h]
  constructor
  <;> norm_num
  <;> linarith [deriv_f_three f]
  <;> linarith [deriv_deriv_f_three f]
  <;> simp [deriv_f_three f, deriv_deriv_f_three f]
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 - 72 * x ^ 2 - 595 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  <;> norm_num
  <;> nlinarith [deriv_pow 4 (-5)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 2 * x ^ 3 - 719 * x ^ 2 + 4840 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_const', deriv_pow, deriv_sub, deriv_mul, deriv_add, deriv_X, deriv_one,
    deriv_comp, deriv_pow, deriv_sub, deriv_mul, deriv_add, deriv_X, deriv_one, deriv_const',
    deriv_comp, deriv_pow, deriv_sub, deriv_mul, deriv_add, deriv_X, deriv_one]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 2 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_pow, deriv_mul, deriv_const, deriv_pow, deriv_id'', deriv_const',
    deriv_id, pow_one, mul_one, mul_zero, zero_add, zero_sub, sub_neg_eq_add, add_zero, add_sub_cancel,
    add_comm, add_left_neg, add_assoc, zero_add, pow_two, mul_neg, neg_mul, neg_neg, mul_one]
  exact ⟨by norm_num, by norm_num⟩

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 3 * x ^ 3 - 250 * x ^ 2 - 1376 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro h
  rw [h]
  norm_num
  constructor <;>
  norm_num [deriv_add, deriv_mul, deriv_pow, deriv_const] <;>
  linarith [differentiableAt_id, differentiableAt_const 3, differentiableAt_pow 4, differentiableAt_pow 3]
  <;>
  simp_all only [deriv_add, deriv_mul, deriv_pow, deriv_const]
  <;>
  linarith [differentiableAt_id, differentiableAt_const 3, differentiableAt_pow 4, differentiableAt_pow 3]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 5 * x ^ 3 - 349 * x ^ 2 - 1784 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro h
  rw [h]
  norm_num [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_pow]
  <;>
  norm_num
  <;>
  exact
    ⟨by linarith, by linarith⟩

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 4 * x ^ 5 - 3 * x ^ 4 + 2 * x ^ 3 - 85716 * x ^ 2 - 818856 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all only [h]
  norm_num
  constructor <;> apply And.intro <;> ring_nf <;> norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow', deriv_id,
    deriv_const', deriv_sub', deriv_mul', deriv_pow_'', deriv_id'', deriv_const', deriv_sub',
    deriv_mul', deriv_pow_', deriv_id, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow',
    deriv_id, deriv_const', deriv_sub', deriv_mul', deriv_pow_'', deriv_id'', deriv_const']
  constructor
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 + 3 * x ^ 4 - 3 * x ^ 3 + 12896 * x - 2170 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  rw [h]
  constructor
  <;> simp [deriv]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - x ^ 3 - 3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) < 0) := by
  intro h
  simp_all [deriv_pow]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + x ^ 5 - 4 * x ^ 4 + x ^ 3 - 26260 * x ^ 2 - 211550 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intro h
  simp only [h, deriv_add, deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_pow, deriv_id'', deriv_pow,
    deriv_id'', deriv_const, deriv_id'', deriv_const, deriv_id'']
  norm_num
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 49128 * x - 7677 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_pow, Nat.cast_ofNat, Nat.cast_zero, zero_mul,
    add_zero, sub_zero, mul_one, mul_zero, zero_add, sub_neg_eq_add, add_assoc, add_left_neg,
    add_zero, zero_sub, neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc]
  norm_num
  constructor <;> linarith [deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_deriv_two_mul_deriv_add_

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 2 * x ^ 4 - x ^ 3 + 423 * x ^ 2 + 1971 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intro h
  rw [h]
  norm_num
  <;> simp only [mul_neg, mul_one, neg_mul, neg_neg, mul_zero, zero_add, mul_neg_one,
    neg_add_rev, neg_zero, neg_neg, add_zero, zero_sub, sub_zero, one_mul,
    mul_one, mul_assoc, mul_comm, mul_left_comm]
  <;> norm_num
  <;> apply And.intro <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 6 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_sub, deriv_const, deriv_pow, deriv_mul, deriv_id'', deriv_pow,
    deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'']
  constructor
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 12 * x ^ 2 + 48 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intro hf
  simp_all only [deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_pow,
    deriv_const, deriv_mul, deriv_id'', deriv_pow, deriv_const, deriv_mul, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 18 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_const, deriv_sub, deriv_pow, deriv_mul, deriv_id'', deriv_const',
    deriv_pow'', deriv_mul', deriv_id, zero_sub, zero_mul, sub_zero, sub_neg_eq_add, add_zero,
    mul_one, mul_zero, zero_add, sub_add_cancel, mul_neg, neg_mul, neg_neg, mul_comm]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 42 * x - 31 * x ^ 2) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_const, deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_pow, deriv_sub,
    deriv_mul, deriv_id'', deriv_pow, deriv_sub, deriv_mul, deriv_id'', deriv_pow, deriv_sub, deriv_mul,
    deriv_id'']
  norm_num
  <;>
  exact
    ⟨by ring_nf, by linarith [pow_two_nonneg (-1)]⟩

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + x ^ 4 - 2 * x ^ 3 - 2343 * x ^ 2 + 20988 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) < 0) := by
  intro h
  rw [h]
  norm_num
  constructor
  <;> simp [deriv_add, deriv_sub, deriv_pow, deriv_const, deriv_mul, deriv_id]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 46873 * x ^ 2 + 374980 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro h
  simp only [h]
  norm_num [deriv_add, deriv_mul, deriv_const, deriv_sub, deriv_id, deriv_pow]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 2 * x ^ 3 - 68 * x ^ 2 + 216 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) = 0) := by
  intro h
  rw [h]
  simp
  constructor <;> norm_num <;> linarith
  <;> simp_all only [pow_one, mul_one, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_assoc]
  <;> norm_num <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 6924 * x - 865 * x ^ 2) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_const', deriv_pow, deriv_mul, deriv_sub, deriv_add, deriv_id'',
    deriv_neg, mul_one, mul_zero, sub_zero, zero_add, add_zero, mul_comm, mul_left_comm,
    mul_assoc, mul_right_comm, mul_assoc, mul_right_comm, mul_assoc, mul_right_comm,
    mul_assoc, mul_right_comm]
  constructor <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 + 34 * x - 27 * x ^ 2) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_sub, deriv_id'',
    deriv_comp, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_comp, deriv_pow, deriv_const,
    deriv_mul, deriv_id'', deriv_comp, deriv_pow, deriv_const, deriv_mul, deriv_id'', deriv_comp]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 - 2 * x ^ 5 + x ^ 4 - 5 * x ^ 3 - 1855 * x ^ 2 - 8619 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'',
    deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'',
    deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'',
    deriv_pow, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_id'']
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 4 * x ^ 5 - 23752 * x ^ 2 + 187520 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intro h
  simp [h, deriv_add, deriv_mul, deriv_const, deriv_pow] at *
  norm_num
  <;> try linarith
  <;> linarith [pow_two_nonneg (5 - 1), pow_two_nonneg (5 - 2), pow_two_nonneg (5 - 3), pow_two_nonneg (5 - 4), pow_two_nonneg (5 - 5), pow_two_nonneg (5 - 6)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 24 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  simp only [h, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_pow, pow_one, mul_one]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 4 * x ^ 5 - 28080 * x ^ 2 + 264384 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intro h
  simp_all only [deriv_add, deriv_pow, deriv_const, deriv_mul, deriv_sub, deriv_id'', deriv_pow,
    deriv_const, deriv_mul, deriv_sub, deriv_id'', one_mul, zero_mul, zero_add, zero_sub,
    sub_zero, zero_pow, zero_mul, mul_one, one_pow, sub_neg_eq_add, mul_zero, sub_zero,
    zero_sub, add_zero]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 4 * x ^ 3 - 576 * x ^ 2 - 4752 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro h
  simp_all only [h]
  norm_num
  apply And.intro <;>
  norm_num
  <;>
  apply HasDerivAt.deriv <;>
  apply HasDerivAt.const_mul <;>
  apply HasDerivAt.pow <;>
  apply HasDerivAt_id

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 3 * x ^ 3 - 351 * x ^ 2 + 1928 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intro h
  rw [h]
  norm_num
  constructor
  <;> simp [deriv_const, deriv_add, deriv_sub, deriv_mul, deriv_pow, pow_one, pow_two, pow_three,
    mul_assoc]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 3 * x ^ 3 - 242 * x ^ 2 + 993 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro hf
  rw [hf]
  simp [deriv_sub, deriv_add, deriv_const, deriv_mul, deriv_pow]
  norm_num
  <;> norm_num <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 - 18797 * x ^ 2 + 120232 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro h
  simp only [h, deriv_add, deriv_sub, deriv_const, deriv_mul, deriv_pow, pow_one, pow_two,
    mul_one, mul_zero, sub_zero, zero_add, zero_sub, add_zero, sub_neg_eq_add, add_assoc]
  norm_num
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - 2 * x ^ 4 + x ^ 3 + 373 * x ^ 2 + 1096 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro hf
  simp_all only [hf, deriv_const, deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_X, deriv_one,
    zero_add, zero_sub, zero_mul, sub_zero, mul_one, mul_zero, zero_neg, neg_neg, neg_mul,
    neg_sub, neg_zero]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + 2 * x ^ 4 - 5 * x ^ 3 - 2504 * x - 801 * x ^ 2) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro h
  simp_all only [rpow_two, mul_neg, mul_one, mul_zero, add_zero, zero_add, zero_mul,
    sub_zero, sub_neg_eq_add, neg_mul, neg_zero, mul_neg_one, neg_neg, mul_two]
  norm_num
  constructor <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 9 * x ^ 2 + 27 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro hf
  simp_all only [deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_add,
    deriv_pow, deriv_sub, deriv_const, deriv_mul, deriv_id'', deriv_add, deriv_pow, deriv_sub,
    deriv_const, deriv_mul, deriv_id'', deriv_add, deriv_pow, deriv_sub, deriv_const, deriv_mul,
    deriv_id'', deriv_add]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 7 * x ^ 2 + 10 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intro hf
  rw [hf]
  simp [deriv_pow, deriv_sub, deriv_const, deriv_id, deriv_mul, deriv_pow, deriv_sub, deriv_const,
    deriv_id]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  simp only [hf, deriv_const', deriv_mul, deriv_pow, deriv_sub, deriv_id'', deriv_pow, deriv_const,
    deriv_id, sub_zero, mul_one, mul_zero, zero_mul, sub_self, zero_sub, neg_zero, zero_add,
    one_mul, mul_neg, neg_mul, neg_neg]
  norm_num
  <;>
  norm_num
  <;>
  linarith [deriv_two_mul_deriv_sub_deriv_two_mul (fun x => x ^ 2) 6]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 44 * x ^ 2 + 215 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intro h
  simp_all [h, deriv_pow, deriv_add, deriv_mul, deriv_const]
  constructor <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro hf
  rw [hf]
  norm_num
  constructor
  <;> simp [deriv]
  <;> ring_nf
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 - 24576 * x - 3840 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intro h
  rw [h]
  constructor
  <;> simp [deriv_sub, deriv_pow, deriv_const, deriv_mul]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 + x ^ 3 - 97 * x ^ 2 - 393 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro hf
  rw [hf]
  simp [deriv]
  norm_num
  <;> linarith [deriv_sq_of_polynomial (-3 : ℝ) (2 : ℝ) (0 : ℝ) (-97 : ℝ) (-393 : ℝ)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 19 * x ^ 2 + 120 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_add, deriv_pow, deriv_mul, deriv_pow, deriv_add, deriv_id'', deriv_const,
    zero_add, zero_mul, add_zero, mul_one, mul_zero, mul_assoc, mul_comm, mul_left_comm]
  norm_num
  <;>
    linarith [deriv_sq_nonneg (fun x => x ^ 3 + 19 * x ^ 2 + 120 * x) (-6)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro hf
  rw [hf]
  simp [deriv_add, deriv_mul, deriv_pow, deriv_id'', deriv_const, zero_add, zero_mul, add_zero,
    mul_one, pow_two, mul_comm]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 3 * x ^ 4 - 3 * x ^ 3 - 39471 * x ^ 2 + 378072 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_add, deriv_const, deriv_mul, deriv_pow, zero_add, zero_mul, one_mul,
    add_zero]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 10 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intro hf
  simp_all only [deriv_add, deriv_const, deriv_pow, deriv_id'', pow_one, zero_add, zero_mul,
    add_zero, mul_one, one_mul, zero_sub, sub_zero, sub_neg_eq_add]
  norm_num
  linarith [deriv_sq_pos_of_neg (by norm_num : (-5 : ℝ) < 0)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 44 * x ^ 2 + 215 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intro h
  simp_all only [h, deriv_add, deriv_const, deriv_pow, deriv_mul, Nat.cast_bit1, Nat.cast_one,
    Nat.cast_bit0, Nat.cast_ofNat]
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2 - 16 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intro h
  rw [h]
  norm_num
  <;> simp [deriv_add, deriv_sub, deriv_pow, deriv_mul, deriv_const]
  <;> norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 3 * x ^ 3 - 20 * x - 4 * x ^ 2) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intro h
  simp_all only [h, deriv_pow, deriv_add, deriv_mul, deriv_id'', deriv_const', deriv_comp, deriv_sub,
    deriv_neg, deriv_pow, deriv_id'', deriv_const', deriv_comp, deriv_sub, deriv_neg, deriv_pow, deriv_id'',
    deriv_const', deriv_comp, deriv_sub, deriv_neg, deriv_pow, deriv_id'', deriv_const', deriv_comp, deriv_sub,
    deriv_neg]
  constructor
  norm_num
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 287 * x ^ 2 - 1528 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro h
  simp_all only [h]
  constructor
  rw [deriv_sub]
  rw [deriv_pow]
  rw [deriv_const]
  norm_num
  simp
  rw [deriv_pow]
  rw [deriv_sub]
  rw [deriv_const]
  norm_num
  simp
  linarith
  all_goals simp

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  simp only [hf, deriv_sub, deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow, deriv_id'',
    deriv_const, deriv_mul, deriv_pow, deriv_id'', deriv_pow, deriv_id'', deriv_const, deriv_mul,
    deriv_pow, deriv_id'', deriv_pow, deriv_id'', deriv_const, deriv_mul, deriv_pow, deriv_id'',
    deriv_pow, deriv_id'']
  norm_num
  <;> linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - x ^ 4 - 4 * x ^ 3 + 31 * x ^ 2 + 50 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intro h
  simp only [h, deriv_const, mul_one, mul_zero, mul_neg, mul_add, mul_sub, add_sub_assoc,
    add_assoc, add_left_neg, sub_zero, zero_add, neg_mul, neg_neg, neg_zero, zero_sub,
    sub_zero, sub_neg_eq_add, add_zero, zero_mul, mul_comm, mul_right_comm]
  norm_num
  <;>
  norm_num
  <;>
  linarith [deriv_mul_comp_deriv_of_comp_deriv_ne_zero
    (fun x:ℝ => 4 * x ^ 3 - x ^ 2 - 4 * x) (fun x:ℝ => 31 + 50 * x) (-1:ℝ)]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 45 * x ^ 2 + 225 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intro h
  simp [h, deriv_add, deriv_mul, deriv_pow, deriv_const]
  norm_num
  <;> linarith

