
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp

open Real

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 5 * x ^ 5 - 82 * x ^ 2 + 127 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 + 25 * x ^ 4 - 164 * x + 127 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 + 100 * x ^ 3 - 164 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - x ^ 3  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  8 * x ^ 3 - 3 * x ^ 2   := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x ^ 2 - 6 * x  := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 17 * x ^ 2 + 96 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 - 34 * x + 96 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x - 34 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 121 * x ^ 2 + 324 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 242 * x + 324 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 242 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 + 30 * x ^ 2 + 60 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 2 + 60 * x + 60 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x + 60 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 + 4 * x ^ 4 - 3726 * x ^ 2 - 17388 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 - 20 * x ^ 4 + 16 * x ^ 3 - 7452 * x - 17388 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 - 80 * x ^ 3 + 48 * x ^ 2 - 7452 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + 3 * x ^ 3 + 20 * x - 17 * x ^ 2) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 + 9 * x ^ 2 + 20 - 34 * x := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 + 18 * x - 34 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 + 2 * x ^ 3 - 214 * x ^ 2 + 1104 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  8 * x ^ 3 + 6 * x ^ 2 - 428 * x + 1104 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x ^ 2 + 12 * x - 428 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 3 * x ^ 5 - x ^ 4 + 4 * x ^ 3 + 109488 * x - 17230 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 + 15 * x ^ 4 - 4 * x ^ 3 + 12 * x ^ 2 + 109488 - 34460 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 + 60 * x ^ 3 - 12 * x ^ 2 + 24 * x - 34460 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 36 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x + 36 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - 4 * x ^ 3 - 93166 * x ^ 2 - 896376 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 + 10 * x ^ 4 + 4 * x ^ 3 - 12 * x ^ 2 - 186332 * x - 896376 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 + 40 * x ^ 3 + 12 * x ^ 2 - 24 * x - 186332 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - x ^ 4 - 214 * x ^ 2 + 987 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 - 4 * x ^ 3 - 428 * x + 987 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 - 12 * x ^ 2 - 428 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 15 * x ^ 2 + 15 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 2 - 30 * x + 15 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x - 30 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 5 * x ^ 4 - 4 * x ^ 3 - 258 * x ^ 2 + 840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  25 * x ^ 4 - 20 * x ^ 3 - 12 * x ^ 2 - 516 * x + 840 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  100 * x ^ 3 - 60 * x ^ 2 - 24 * x - 516 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 - 4319 * x ^ 2 + 38868 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  10 * x ^ 4 - 8638 * x + 38868 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  40 * x ^ 3 - 8638 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 75 * x ^ 2 + 375 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 2 - 150 * x + 375 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x - 150 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 2 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 2 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 18 * x ^ 2 + 108 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 + 36 * x + 108 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x + 36 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 5 * x ^ 3 - 2635 * x - 376 * x ^ 2) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 + 15 * x ^ 2 - 2635 - 752 * x := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 + 30 * x - 752 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 6 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x + 6 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 2 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 - 4 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 - 4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 12 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 12 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - x ^ 5 + 3 * x ^ 3 - 60426 * x ^ 2 - 578988 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 - 5 * x ^ 4 + 9 * x ^ 2 - 120852 * x - 578988 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 - 20 * x ^ 3 + 18 * x - 120852 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 8 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 8 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 4 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 + 80 * x + 22 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 2 + 80 + 44 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x + 44 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 + 5 * x ^ 3 - 39 * x ^ 2 + 47 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  16 * x ^ 3 + 15 * x ^ 2 - 78 * x + 47 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  48 * x ^ 2 + 30 * x - 78 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 - x ^ 4 - 2347 * x ^ 2 + 17720 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  10 * x ^ 4 - 4 * x ^ 3 - 4694 * x + 17720 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  40 * x ^ 3 - 12 * x ^ 2 - 4694 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 9 * x ^ 2 + 27 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 - 18 * x + 27 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x - 18 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 + 9 * x ^ 2 + 12 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 2 + 18 * x + 12 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x + 18 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 20 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 20 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 4 * x ^ 4 + 5 * x ^ 3 - 13 * x ^ 2 + 40 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 - 16 * x ^ 3 + 15 * x ^ 2 - 26 * x + 40 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 - 48 * x ^ 2 + 30 * x - 26 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 121 * x ^ 2 - 616 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 6 * x ^ 2 - 242 * x - 616 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 12 * x - 242 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + x ^ 4 + x ^ 3 + 8445 * x ^ 2 + 76176 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2 + 16890 * x + 76176 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 + 12 * x ^ 2 + 6 * x + 16890 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + x ^ 3 + 279 * x ^ 2 + 1242 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 + 3 * x ^ 2 + 558 * x + 1242 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 + 6 * x + 558 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 4 * x ^ 5 + 3 * x ^ 4 + 4 * x ^ 3 - 42387 * x ^ 2 + 340820 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 20 * x ^ 4 + 12 * x ^ 3 + 12 * x ^ 2 - 84774 * x + 340820 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 80 * x ^ 3 + 36 * x ^ 2 + 24 * x - 84774 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 + x ^ 4 + 2 * x ^ 3  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  25 * x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2   := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  100 * x ^ 3 + 12 * x ^ 2 + 12 * x  := by
    ext x
    rw [h_deriv_f]
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

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 2 * x ^ 3 - 170 * x ^ 2 + 944 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  8 * x ^ 3 - 6 * x ^ 2 - 340 * x + 944 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x ^ 2 - 12 * x - 340 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 2 * x ^ 4 - x ^ 3 - 2996 * x ^ 2 + 18128 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  25 * x ^ 4 - 8 * x ^ 3 - 3 * x ^ 2 - 5992 * x + 18128 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  100 * x ^ 3 - 24 * x ^ 2 - 6 * x - 5992 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 20 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 20 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 - 158 * x ^ 2 + 768 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 + 15 * x ^ 2 - 316 * x + 768 := by
    ext x
    rw [hf]
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 + 30 * x - 316 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 4 * x ^ 3 - 71 * x ^ 2 + 106 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 + 12 * x ^ 2 - 142 * x + 106 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 + 24 * x - 142 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 16 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 16 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3  - 3 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2  - 3 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x  := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3  + 2 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 6 * x ^ 2  + 2 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 12 * x  := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 + x ^ 3 - 27 * x ^ 2 - 37 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 + 3 * x ^ 2 - 54 * x - 37 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 + 6 * x - 54 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 8 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x - 8 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 180 * x ^ 2 + 1512 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 6 * x ^ 2 - 360 * x + 1512 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 12 * x - 360 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - x ^ 5 + x ^ 4 + 3 * x ^ 3 - 1164 * x ^ 2 + 3708 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 5 * x ^ 4 + 4 * x ^ 3 + 9 * x ^ 2 - 2328 * x + 3708 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 20 * x ^ 3 + 12 * x ^ 2 + 18 * x - 2328 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 18 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x + 18 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - x ^ 3 - 397 * x ^ 2 - 2104 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  16 * x ^ 3 - 3 * x ^ 2 - 794 * x - 2104 := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  48 * x ^ 2 - 6 * x - 794 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 - 59958 * x ^ 2 - 575316 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 - 5 * x ^ 4 - 8 * x ^ 3 + 15 * x ^ 2 - 119916 * x - 575316 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 - 20 * x ^ 3 - 24 * x ^ 2 + 30 * x - 119916 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 + 11 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 4 - 16 * x ^ 3 - 6 * x ^ 2 - 4 * x + 11 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 3 - 48 * x ^ 2 - 12 * x - 4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 1200 * x ^ 2 + 3840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 2400 * x + 3840 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 2400 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + x ^ 4 + 5 * x ^ 3 - 38 * x ^ 2 + 47 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  10 * x ^ 4 + 4 * x ^ 3 + 15 * x ^ 2 - 76 * x + 47 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  40 * x ^ 3 + 12 * x ^ 2 + 30 * x - 76 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 8 * x ^ 2 + 7 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 + 16 * x + 7 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x + 16 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - 5 * x ^ 5 - 5 * x ^ 4 - 3 * x ^ 3 + 2 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 - 25 * x ^ 4 - 20 * x ^ 3 - 9 * x ^ 2 + 4 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 - 100 * x ^ 3 - 60 * x ^ 2 - 18 * x + 4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 10 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 10 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - x ^ 3 - 16 * x ^ 2 + 44 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 3 * x ^ 2 - 32 * x + 44 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    exact DifferentiableAt.sub (DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 6 * x - 32 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + x ^ 3 - 29115 * x - 6063 * x ^ 2) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 + 3 * x ^ 2 - 29115 - 12126 * x := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 + 6 * x - 12126 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 8 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 8 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 57 * x ^ 2 + 360 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 - 114 * x + 360 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x - 114 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 16 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 16 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 12 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x - 12 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 39 * x ^ 2 + 126 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 2 + 78 * x + 126 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x + 78 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 72 * x ^ 2 + 432 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 2 + 144 * x + 432 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x + 144 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 4 * x ^ 3 - 48 * x ^ 2 - 84 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 + 12 * x ^ 2 - 96 * x - 84 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 + 24 * x - 96 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 749 * x ^ 2 + 4990 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 1498 * x + 4990 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 1498 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 176 * x + 46 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 2 + 176 + 92 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x + 92 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 4 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 12 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x + 12 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 16 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x + 16 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 12 * x ^ 2 + 19 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 - 24 * x + 19 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 - 24 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + x ^ 5 + x ^ 4 - 5 * x ^ 3 - 54 * x ^ 2 - 76 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3 - 15 * x ^ 2 - 108 * x - 76 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 + 20 * x ^ 3 + 12 * x ^ 2 - 30 * x - 108 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 150 * x ^ 2 + 1000 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 300 * x + 1000 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 300 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + 42 * x ^ 2 + 64 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 + 84 * x + 64 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 + 84 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 21 * x ^ 2 + 36 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 2 + 42 * x + 36 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x + 42 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 10 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x - 10 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 46 * x ^ 2 + 235 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 - 92 * x + 235 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x - 92 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 69 * x ^ 2 + 392 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 6 * x ^ 2 - 138 * x + 392 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 12 * x - 138 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 4 * x ^ 2 + 5 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 - 8 * x + 5 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x - 8 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 32 * x + 10 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 + 32 + 20 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x + 20 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 48 * x ^ 2 - 128 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  8 * x ^ 3 - 96 * x - 128 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x ^ 2 - 96 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 60 * x ^ 2 + 300 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 2 + 120 * x + 300 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x + 120 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 3 * x ^ 5 + 2 * x ^ 4 + 2 * x ^ 3 - 122 * x ^ 2 + 185 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 + 15 * x ^ 4 + 8 * x ^ 3 + 6 * x ^ 2 - 244 * x + 185 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 + 60 * x ^ 3 + 24 * x ^ 2 + 12 * x - 244 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 76 * x ^ 2 + 385 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 2 - 152 * x + 385 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x - 152 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 4 * x ^ 5 + 5 * x ^ 4 - x ^ 3 - 105 * x - 69 * x ^ 2) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 + 20 * x ^ 4 + 20 * x ^ 3 - 3 * x ^ 2 - 105 - 138 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
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
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 + 80 * x ^ 3 + 60 * x ^ 2 - 6 * x - 138 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 - 3 * x ^ 4 - 4 * x ^ 3 + 289872 * x - 29520 * x ^ 2) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 - 20 * x ^ 4 - 12 * x ^ 3 - 12 * x ^ 2 + 289872 - 59040 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 - 80 * x ^ 3 - 36 * x ^ 2 - 24 * x - 59040 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + 2 * x ^ 3 + 45 * x ^ 2 + 64 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 + 6 * x ^ 2 + 90 * x + 64 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 + 12 * x + 90 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 + 9470 * x ^ 2 + 84480 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 - 16 * x ^ 3 - 6 * x ^ 2 + 18940 * x + 84480 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 - 48 * x ^ 2 - 12 * x + 18940 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 5 * x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 + 290 * x ^ 2 + 822 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 5 + 25 * x ^ 4 - 8 * x ^ 3 + 15 * x ^ 2 + 580 * x + 822 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x ^ 4 + 100 * x ^ 3 - 24 * x ^ 2 + 30 * x + 580 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 89 * x ^ 2 + 528 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 2 - 178 * x + 528 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x - 178 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 5 * x ^ 4 + 2 * x ^ 3 - 28 * x ^ 2 + 45 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  25 * x ^ 4 - 20 * x ^ 3 + 6 * x ^ 2 - 56 * x + 45 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  100 * x ^ 3 - 60 * x ^ 2 + 12 * x - 56 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 - 18 * x ^ 2 + 54 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 2 - 36 * x + 54 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x - 36 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 38 * x ^ 2 + 160 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 - 76 * x + 160 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x - 76 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 3 * x ^ 5 - 50624 * x ^ 2 - 403115 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 15 * x ^ 4 - 101248 * x - 403115 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 60 * x ^ 3 - 101248 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 5 * x ^ 5 + x ^ 4 - 107 * x ^ 2 - 412 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 + 25 * x ^ 4 + 4 * x ^ 3 - 214 * x - 412 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 + 100 * x ^ 3 + 12 * x ^ 2 - 214 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 55 * x ^ 2 + 222 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 110 * x + 222 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 110 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 + 6804 * x - 1350 * x ^ 2) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 - 20 * x ^ 4 + 6804 - 2700 * x := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 - 80 * x ^ 3 - 2700 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 6 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x - 6 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 6 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x - 6 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 5 * x ^ 3 - 738 * x ^ 2 - 5724 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 - 15 * x ^ 2 - 1476 * x - 5724 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 - 30 * x - 1476 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 2 * x ^ 5 + x ^ 4 - 35150 * x ^ 2 + 282250 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 - 10 * x ^ 4 + 4 * x ^ 3 - 70300 * x + 282250 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 - 40 * x ^ 3 + 12 * x ^ 2 - 70300 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 480 * x ^ 2 - 2560 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 960 * x - 2560 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 960 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 2 * x ^ 5 - x ^ 4  ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 - 10 * x ^ 4 - 4 * x ^ 3   := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 - 40 * x ^ 3 - 12 * x ^ 2  := by
    ext x
    rw [h_deriv_f]
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

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 12 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x - 12 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + 3 * x ^ 5 + 2 * x ^ 4 - 3 * x ^ 3 - 9828 * x ^ 2 - 63376 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 + 15 * x ^ 4 + 8 * x ^ 3 - 9 * x ^ 2 - 19656 * x - 63376 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 + 60 * x ^ 3 + 24 * x ^ 2 - 18 * x - 19656 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 3 - 253 * x ^ 2 + 740 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  10 * x ^ 4 + 20 * x ^ 3 - 12 * x ^ 2 - 506 * x + 740 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  40 * x ^ 3 + 60 * x ^ 2 - 24 * x - 506 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 5 * x ^ 4 + 5 * x ^ 3 - 5175 * x ^ 2 + 24543 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 + 20 * x ^ 3 + 15 * x ^ 2 - 10350 * x + 24543 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 + 60 * x ^ 2 + 30 * x - 10350 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 - 72 * x ^ 2 - 595 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 + 15 * x ^ 2 - 144 * x - 595 := by
    ext x
    rw [hf]
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 + 30 * x - 144 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 2 * x ^ 3 - 719 * x ^ 2 + 4840 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 6 * x ^ 2 - 1438 * x + 4840 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 12 * x - 1438 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 2 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 2 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 3 * x ^ 3 - 250 * x ^ 2 - 1376 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 + 9 * x ^ 2 - 500 * x - 1376 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 + 18 * x - 500 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 5 * x ^ 3 - 349 * x ^ 2 - 1784 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 - 15 * x ^ 2 - 698 * x - 1784 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 - 30 * x - 698 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 - 4 * x ^ 5 - 3 * x ^ 4 + 2 * x ^ 3 - 85716 * x ^ 2 - 818856 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  24 * x ^ 5 - 20 * x ^ 4 - 12 * x ^ 3 + 6 * x ^ 2 - 171432 * x - 818856 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  120 * x ^ 4 - 80 * x ^ 3 - 36 * x ^ 2 + 12 * x - 171432 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 + 3 * x ^ 4 - 3 * x ^ 3 + 12896 * x - 2170 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  15 * x ^ 4 + 12 * x ^ 3 - 9 * x ^ 2 + 12896 - 4340 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 3 + 36 * x ^ 2 - 18 * x - 4340 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - x ^ 3 - 3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 3 * x ^ 2 - 6 * x  := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 6 * x - 6 := by
    ext x
    rw [h_deriv_f]
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

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + x ^ 5 - 4 * x ^ 4 + x ^ 3 - 26260 * x ^ 2 - 211550 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 + 5 * x ^ 4 - 16 * x ^ 3 + 3 * x ^ 2 - 52520 * x - 211550 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 + 20 * x ^ 3 - 48 * x ^ 2 + 6 * x - 52520 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 49128 * x - 7677 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 + 49128 - 15354 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 - 15354 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 2 * x ^ 4 - x ^ 3 + 423 * x ^ 2 + 1971 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  10 * x ^ 4 + 8 * x ^ 3 - 3 * x ^ 2 + 846 * x + 1971 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  40 * x ^ 3 + 24 * x ^ 2 - 6 * x + 846 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 6 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x - 6 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 12 * x ^ 2 + 48 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 + 24 * x + 48 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x + 24 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 18 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x - 18 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 42 * x - 31 * x ^ 2) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 42 - 62 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 62 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + x ^ 4 - 2 * x ^ 3 - 2343 * x ^ 2 + 20988 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2 - 4686 * x + 20988 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 + 12 * x ^ 2 - 12 * x - 4686 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 46873 * x ^ 2 + 374980 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 93746 * x + 374980 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 93746 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - 2 * x ^ 3 - 68 * x ^ 2 + 216 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  5 * x ^ 4 - 6 * x ^ 2 - 136 * x + 216 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  20 * x ^ 3 - 12 * x - 136 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 6924 * x - 865 * x ^ 2) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  16 * x ^ 3 - 6924 - 1730 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  48 * x ^ 2 - 1730 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 + 34 * x - 27 * x ^ 2) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 + 34 - 54 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 54 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 - 2 * x ^ 5 + x ^ 4 - 5 * x ^ 3 - 1855 * x ^ 2 - 8619 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 5 - 10 * x ^ 4 + 4 * x ^ 3 - 15 * x ^ 2 - 3710 * x - 8619 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x ^ 4 - 40 * x ^ 3 + 12 * x ^ 2 - 30 * x - 3710 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 4 * x ^ 5 - 23752 * x ^ 2 + 187520 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 + 20 * x ^ 4 - 47504 * x + 187520 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 + 80 * x ^ 3 - 47504 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 24 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 4 * x ^ 5 - 28080 * x ^ 2 + 264384 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 5 + 20 * x ^ 4 - 56160 * x + 264384 := by
    ext x
    rw [hf]
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
    exact DifferentiableAt.sub (DifferentiableAt.add (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x ^ 4 + 80 * x ^ 3 - 56160 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 4 * x ^ 3 - 576 * x ^ 2 - 4752 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 + 12 * x ^ 2 - 1152 * x - 4752 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 + 24 * x - 1152 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 3 * x ^ 3 - 351 * x ^ 2 + 1928 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  16 * x ^ 3 - 9 * x ^ 2 - 702 * x + 1928 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  48 * x ^ 2 - 18 * x - 702 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 3 * x ^ 3 - 242 * x ^ 2 + 993 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 3 - 9 * x ^ 2 - 484 * x + 993 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 2 - 18 * x - 484 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 - 18797 * x ^ 2 + 120232 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  30 * x ^ 5 - 5 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 - 37594 * x + 120232 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  150 * x ^ 4 - 20 * x ^ 3 + 24 * x ^ 2 + 24 * x - 37594 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - 2 * x ^ 4 + x ^ 3 + 373 * x ^ 2 + 1096 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 - 8 * x ^ 3 + 3 * x ^ 2 + 746 * x + 1096 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_pow _
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 - 24 * x ^ 2 + 6 * x + 746 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + 2 * x ^ 4 - 5 * x ^ 3 - 2504 * x - 801 * x ^ 2) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  18 * x ^ 5 + 8 * x ^ 3 - 15 * x ^ 2 - 2504 - 1602 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  90 * x ^ 4 + 24 * x ^ 2 - 30 * x - 1602 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 9 * x ^ 2 + 27 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 - 18 * x + 27 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x - 18 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 7 * x ^ 2 + 10 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 - 14 * x + 10 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 - 14 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 44 * x ^ 2 + 215 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 + 88 * x + 215 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x + 88 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 - 24576 * x - 3840 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  6 * x ^ 5 - 24576 - 7680 * x := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (differentiableAt_pow _) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  30 * x ^ 4 - 7680 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 + x ^ 3 - 97 * x ^ 2 - 393 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  8 * x ^ 3 + 3 * x ^ 2 - 194 * x - 393 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  24 * x ^ 2 + 6 * x - 194 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 19 * x ^ 2 + 120 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  3 * x ^ 2 + 38 * x + 120 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  6 * x + 38 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 4 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 4 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 3 * x ^ 4 - 3 * x ^ 3 - 39471 * x ^ 2 + 378072 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 5 + 12 * x ^ 3 - 9 * x ^ 2 - 78942 * x + 378072 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  60 * x ^ 4 + 36 * x ^ 2 - 18 * x - 78942 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 10 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  2 * x + 10 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  2 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 44 * x ^ 2 + 215 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 + 88 * x + 215 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x + 88 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2 - 16 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 + 15 * x ^ 2 + 6 * x - 16 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 + 30 * x + 6 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 3 * x ^ 3 - 20 * x - 4 * x ^ 2) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x ^ 3 + 9 * x ^ 2 - 20 - 8 * x := by
    ext x
    rw [hf]
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
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
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
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  12 * x ^ 2 + 18 * x - 8 := by
    ext x
    rw [h_deriv_f]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_const _
    exact DifferentiableAt.sub (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (differentiableAt_const _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 287 * x ^ 2 - 1528 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  12 * x ^ 3 - 574 * x - 1528 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  36 * x ^ 2 - 574 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - x ^ 4 - 4 * x ^ 3 + 31 * x ^ 2 + 50 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  20 * x ^ 4 - 4 * x ^ 3 - 12 * x ^ 2 + 62 * x + 50 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    
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
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_pow _
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.sub (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  80 * x ^ 3 - 12 * x ^ 2 - 24 * x + 62 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_const]
    
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
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num
    
example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 45 * x ^ 2 + 225 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x =>  9 * x ^ 2 + 90 * x + 225 := by
    ext x
    rw [hf]
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

  have h_deriv_deriv_f : deriv (deriv f) = fun x =>  18 * x + 90 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    
    ring
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  
    