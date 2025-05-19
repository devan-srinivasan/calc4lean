import Mathlib
open Real

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 + 30 * x ^ 2 + 60 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  -- replace f by its defining lambda
  subst hf

  -- 1st derivative
  have h1 : deriv f = fun x => 15*x^2 + 60*x + 60 := by
    ext x; simp

  -- 2nd derivative
  have h2 : deriv (deriv f) = fun x => 30*x + 60 := by
    ext x; simp

  -- now evaluate at x = -2
  constructor
  · rw [h1]; norm_num
  · rw [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 + 4 * x ^ 4 - 3726 * x ^ 2 - 17388 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  -- First compute f'
  have h1 : deriv f = fun x => 12 * x^5 - 20 * x^4 + 16 * x^3 - 7452 * x - 17388 := by
    ext x
    simp [hf]
  -- Then compute f''
  have h2 : deriv (deriv f) = fun x => 60 * x^4 - 80 * x^3 + 48 * x^2 - 7452 := by
    ext x
    simp [h1]
  -- Now evaluate at x = -3
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
deriv_pow {n : ℕ} [Fact (0 < n)] :
     deriv (fun x => x^n) = fun x => n * x^(n-1)

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + 3 * x ^ 3 + 20 * x - 17 * x ^ 2) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intro hf
  -- first compute f′
  have h_deriv_f : deriv f = fun x => 5 * x ^ 4 + 9 * x ^ 2 + 20 - 34 * x := by
    ext x
    rw [hf]
    -- f = (x^5 + 3*x^3) + 20*x - 17*x^2
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- now expand each piece
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
    -- supply the differentiability proofs
    all_goals
      apply differentiableAt_const <|>
      apply differentiableAt_id <|>
      apply differentiableAt_pow <|>
      apply DifferentiableAt.mul <|>
      apply DifferentiableAt.add <|>
      apply DifferentiableAt.sub

  -- then compute f″
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 20 * x ^ 3 + 18 * x - 34 := by
    ext x
    rw [h_deriv_f]
    -- deriv of (5 x^4 + 9 x^2 + 20 - 34 x)
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    -- break into pieces again
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
    all_goals
      apply differentiableAt_const <|>
      apply differentiableAt_id <|>
      apply differentiableAt_pow <|>
      apply DifferentiableAt.mul <|>
      apply DifferentiableAt.sub

  -- finally evaluate at 1
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

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
  intro hf
  -- first derivative
  have h1 : deriv f = fun x => 24*x^5 + 15*x^4 - 4*x^3 + 12*x^2 - 34460*x + 109488 := by
    ext x
    -- rewrite f‐definition and then simplify all the derivs at once
    rw [hf]
    simp!  -- unfolds deriv_add, deriv_mul_const, deriv_pow, deriv_const, deriv_id, …

  -- second derivative
  have h2 : deriv (deriv f) = fun x => 120*x^4 + 60*x^3 - 12*x^2 + 24*x - 34460 := by
    ext x
    rw [h1]
    simp!

  -- evaluate at x = 4
  constructor
  · -- deriv f 4 = 0
    simpa [h1] using by norm_num
  · -- deriv (deriv f) 4 > 0
    simpa [h2] using by norm_num

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
  -- rewrite f to its explicit lambda
  rw [hf]
  -- first compute f'
  have h1 : deriv (fun x => 5*x^6 + 2*x^5 + x^4 - 4*x^3 - 93166*x^2 - 896376*x)
             = fun x => 30*x^5 + 10*x^4 + 4*x^3 - 12*x^2 - 186332*x - 896376 := by
    ext x
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_const, deriv_id'']
  -- then compute f''
  have h2 : deriv (fun x => 30*x^5 + 10*x^4 + 4*x^3 - 12*x^2 - 186332*x - 896376)
             = fun x => 150*x^4 + 40*x^3 + 12*x^2 - 24*x - 186332 := by
    ext x
    simp only [h1, deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_const, deriv_id'']
  -- now the goal follows by rewriting and a final `norm_num`
  simp [h1, h2]; constructor; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 - x ^ 4 - 214 * x ^ 2 + 987 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) > 0) := by
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 5 * x^4 - 4 * x^3 - 428 * x + 987 := by
    ext x
    -- unfold f
    rw [hf]
    -- distribute deriv
    nth_rewrite 1 [deriv_sub (fun x => x^5) (fun x => x^4)]
    nth_rewrite 1 [deriv_mul 214 fun x => x^2]
    nth_rewrite 1 [deriv_mul 987 fun x => x]
    nth_rewrite 1 [deriv_pow'']  -- for x^5
    nth_rewrite 1 [deriv_id'']   -- for − x^4
    nth_rewrite 1 [deriv_pow'']  -- for x^2
    nth_rewrite 1 [deriv_id'']   -- for x
    nth_rewrite 1 [deriv_const]  -- for the constants 214, 987
    ring
    -- dispatch all the differentiability hypotheses
    all_goals
      try module_proof  -- this will find the differentiableAt_* proofs

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 20 * x^3 - 12 * x^2 - 428 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub (fun x => 5 * x^4) (fun x => 4 * x^3)]
    nth_rewrite 1 [deriv_mul 5 fun x => x^4]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul 4 fun x => x^3]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_const]
    ring
    all_goals
      try module_proof

  -- now check at x = 3
  constructor
  · nth_rewrite 1 [h_deriv_f]; norm_num        -- deriv f 3 = 0
  · nth_rewrite 1 [h_deriv_deriv_f]; norm_num  -- deriv (deriv f) 3 = 4 > 0

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 3 - 15 * x ^ 2 + 15 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) = 0) := by

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 5 - 5 * x ^ 4 - 4 * x ^ 3 - 258 * x ^ 2 + 840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) < 0) := by
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 25 * x ^ 4 - 20 * x ^ 3 - 12 * x ^ 2 - 516 * x + 840 := by
    ext x
    -- unfold f
    rw [hf]
    -- apply the usual derivative rules, then finish by ring
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    ring
    -- supply differentiability hypotheses for each term
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- compute the second derivative
  have h_deriv_deriv_f :
    deriv (deriv f) = fun x => 100 * x ^ 3 - 60 * x ^ 2 - 24 * x - 516 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability arguments
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- now evaluate at x = 2
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 - 4319 * x ^ 2 + 38868 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  -- first derivative
  have h1 : deriv f = fun x => 10*x^4 - 8638*x + 38868 := by
    simp [hf]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 40*x^3 - 8638 := by
    simp [h1]
  -- now evaluate at 6
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 24 := by
    ext x
    -- unfold f
    rw [hf]
    -- deriv (2 * x^2 - 24 * x)
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- provid differentiability witnesses
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    -- unfold deriv f
    rw [h_deriv_f]
    -- deriv (4 * x - 24)
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability again
    exact differentiableAt_const _
    exact differentiableAt_const _
    exact differentiableAt_id

  -- assemble the result at x = 6
  constructor
  -- deriv f 6 = 4*6 - 24 = 0
  nth_rewrite 1 [h_deriv_f]
  ring
  -- deriv (deriv f) 6 = 4 > 0
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
  -- compute f'
  have h1 : deriv f = fun x => 15 * x^2 - 150 * x + 375 := by
    ext x
    simp [hf]
  -- compute f''
  have h2 : deriv (deriv f) = fun x => 30 * x - 150 := by
    ext x
    simp [h1]
  -- check at x = 5
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

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
  intro hf

  /-- Compute the first derivative: `f' x = 2*x + 2`. -/
  have h_deriv_f : deriv f = fun x => 2 * x + 2 := by
    ext x
    -- rewrite `f` to `x^2 + 2*x`
    rw [hf]
    -- deriv (x^2 + 2*x) = deriv (x^2) + deriv (2*x)
    nth_rewrite 1 [deriv_add]
    -- deriv (x^2) = 2*x
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (2*x) = 2 * deriv x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- supplying the differentiability proofs
    exact differentiableAt_pow 2 (x := x)
    exact differentiableAt_id
    exact differentiableAt_const x
    exact (DifferentiableAt.mul (differentiableAt_const x) (differentiableAt_id x))

  /-- Compute the second derivative: `f'' x = 2`. -/
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    -- rewrite `deriv f` to `2*x + 2`
    rw [h_deriv_f]
    -- deriv (2*x + 2) = deriv (2*x) + deriv 2
    nth_rewrite 1 [deriv_add]
    -- deriv (2*x) = 2 * deriv x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- deriv 2 = 0
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability proofs
    exact differentiableAt_const x
    exact differentiableAt_id x
    exact (DifferentiableAt.mul (differentiableAt_const x) (differentiableAt_id x))
    exact differentiableAt_const x

  -- conclude the goal
  constructor
  · -- f'(-1) = 2*(-1) + 2 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- f''(-1) = 2 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 18 * x ^ 2 + 108 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro hf

  -- compute f'
  have h_deriv_f : deriv f = fun x => 3 * x ^ 2 + 36 * x + 108 := by
    ext x
    -- unfold f
    rw [hf]
    -- d(x^3 + 18 x^2 + 108 x) = d(x^3) + d(18 x^2) + d(108 x)
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- d(x^3)
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- d(18 x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- d(108 x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- collect
    ring
    -- now the differentiability witnesses
    exact differentiableAt_pow (n := 3)
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow (n := 2)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 6 * x + 36 := by
    ext x
    -- unfold f'
    rw [h_deriv_f]
    -- d(3 x^2 + 36 x + 108) = d(3 x^2) + d(36 x) + d(108)
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- d(3 x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- d(36 x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- d(108)
    nth_rewrite 1 [deriv_const]
    -- collect
    ring
    -- differentiability witnesses
    exact differentiableAt_pow (n := 2)
    exact differentiableAt_id
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- assemble the desired ⟨…, …⟩
  constructor
  · -- f'(-6) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- f''(-6) = 0
    nth_rewrite 1 [h_deriv_deriv_f]
    ring

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 5 * x ^ 3 - 2635 * x - 376 * x ^ 2) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) < 0) := by
  -- 1) compute the first derivative
  have h_deriv_f : deriv f = fun x => 12 * x ^ 3 + 15 * x ^ 2 - 752 * x - 2635 := by
    ext x
    -- rewrite f to the polynomial and simp all the deriv rules
    rw [hf]
    simp [deriv, deriv_pow, deriv_const, deriv_mul, deriv_id]
  -- 2) compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 36 * x ^ 2 + 30 * x - 752 := by
    ext x
    rw [h_deriv_f]
    simp [deriv, deriv_pow, deriv_const, deriv_mul, deriv_id]
  -- 3) evaluate at x = -5
  constructor
  · -- first derivative at -5
    nth_rewrite 1 [h_deriv_f]
    norm_num
  · -- second derivative at -5
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intro hf
  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 24 := by
    ext x
    -- rewrite f to `2*x^2 - 24*x` and then `simp` knows deriv of
    -- constants, id, mul, pow, add and sub
    simp [hf]
  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun _ => 4 := by
    ext x
    -- rewrite deriv f to `4*x - 24` and simplify
    simp [h_deriv_f]
  -- finally plug in x = 6
  constructor
  · -- deriv f 6 = 4*6 - 24 = 0
    nth_rewrite 1 [h_deriv_f]; norm_num
  · -- deriv (deriv f) 6 = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 6 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  -- compute the first derivative
  have h1 : deriv f = fun x => 6 * x + 6 := by
    ext x
    simp [hf]
  -- compute the second derivative
  have h2 : deriv (deriv f) = fun _ => 6 := by
    ext x
    simp [h1]
  -- now plug in x = -1
  constructor
  · -- deriv f (-1) = 6 * (-1) + 6 = 0
    rw [h1]
    norm_num
  · -- deriv (deriv f) (-1) = 6 > 0
    rw [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  -- assume the definition of f
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 4 := by
    ext x
    -- unfold f
    rw [hf]
    -- d(2*x^2 - 4*x) = d(2*x^2) - d(4*x)
    nth_rewrite 1 [deriv_sub]
    -- d(2*x^2) = 2 * d(x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    -- d(x^2) = 2*x
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- d(4*x) = 4 * d(x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish by ring
    ring
    -- side-goals: differentiability proofs
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact differentiableAt_id

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    -- unfold deriv f
    rw [h_deriv_f]
    -- d(4*x - 4) = d(4*x) - d(4)
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id

  -- conclude at x = 1
  constructor
  · -- deriv f 1 = 4*1 - 4 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) 1 = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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
  intro hf

  -- compute the first derivative: f' x = 4*x + 12
  have h_deriv_f : deriv f = fun x => 4 * x + 12 := by
    ext x
    rw [hf]
    -- deriv (2*x^2 + 12*x) = deriv (2*x^2) + deriv (12*x)
    nth_rewrite 1 [deriv_add]
    -- deriv (2*x^2) = 2 * deriv (x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    -- deriv (x^2) = 2*x
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (12*x) = 12 * deriv x = 12
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    · exact differentiableAt_const _
    · exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    · exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- compute the second derivative: (f')' x = 4
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    rw [h_deriv_f]
    -- deriv (4*x + 12) = deriv (4*x) + deriv 12 = 4 + 0 = 4
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    · exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    · exact differentiableAt_const _
    · exact differentiableAt_const _

  -- now check at x = -3
  constructor
  · -- f'(-3) = 4 * (-3) + 12 = -12 + 12 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- (f')'(-3) = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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
  intro hf

  -- compute f'
  have h_deriv_f : deriv f = fun x => 4 * x + 8 := by
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
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id

  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
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
    exact differentiableAt_const _

  -- evaluate at x = -2
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

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
  intro hf
  -- now `hf` rewrites `f` into the concrete lambda
  -- `simp` knows `deriv_const`, `deriv_pow''`, `deriv_id''`, `deriv_mul` and `deriv_add`
  simp [hf]
  -- at this point Lean sees
  --   6 * (-4) ^ 2 + 44 * (-4) + 80 = 0
  -- and
  --   deriv (fun x => 6*x^2 + 44*x + 80) (-4) = 12 * (-4) + 44
  -- so `norm_num` finishes both the equality and the `< 0`.
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
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 10 * x^4 - 4 * x^3 - 4694 * x + 17720 := by
    ext x
    -- unfold f and use the deriv_* lemmas
    rw [hf]
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    -- the simplifier now sees 
    -- deriv (fun x => 2*x^5) = fun x => 2*5*x^(5-1) = 10*x^4
    -- deriv (fun x => x^4)   = fun x => 4*x^3
    -- deriv (fun x => 2347*x^2) = fun x => 2347*2*x = 4694*x
    -- deriv (fun x => 17720*x) = fun x => 17720
    ring

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 40 * x^3 - 12 * x^2 - 4694 := by
    ext x
    rw [h_deriv_f]
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring

  -- finally evaluate at x = 5
  constructor
  · -- deriv f 5 = 0
    nth_rewrite 1 [h_deriv_f]
    norm_num

  · -- deriv (deriv f) 5 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 9 * x ^ 2 + 27 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro hf
  -- compute the first derivative
  have h1 : deriv f = fun x => 3 * x ^ 2 - 18 * x + 27 := by
    ext x
    simp [hf]
  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 6 * x - 18 := by
    ext x
    simp [h1]
  -- conclude at x = 3
  constructor
  · nth_rewrite 1 [h1]; norm_num
  · nth_rewrite 1 [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intros hf
  -- compute f'
  have h_deriv_f : deriv f = fun x => 6 * x := by
    ext x
    rw [hf]
    -- deriv (fun x => 3 * x^2) = 3 * deriv (fun x => x^2)
    nth_rewrite 1 [deriv_mul]
    -- deriv_const : deriv (fun _ => 3) = 0
    nth_rewrite 1 [deriv_const]
    -- deriv_pow'': deriv (fun x => x^2) = fun x => 2 * x
    nth_rewrite 1 [deriv_pow'']
    -- deriv_id'': deriv (fun x => x) = fun _ => 1
    nth_rewrite 1 [deriv_id'']
    ring
    -- side—is differentiable
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 6 := by
    ext x
    rw [h_deriv_f]
    -- deriv (fun x => 6 * x) = 6
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    exact differentiableAt_const _
    exact differentiableAt_const _
  -- finish
  constructor
  -- f' 0 = 6 * 0 = 0
  nth_rewrite 1 [h_deriv_f]; ring
  -- f'' 0 = 6 > 0
  nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 + 9 * x ^ 2 + 12 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  -- rewrite `f` to the concrete polynomial, and simplify all the `deriv`‐calls
  simp [hf]
  -- the remaining goals are pure numeric checks
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
  -- compute the first derivative
  have Df : deriv f = fun x => 5*x^4 - 16*x^3 + 15*x^2 - 26*x + 40 := by
    ext x
    simp [hf] -- uses deriv_pow, deriv_mul, deriv_sub, deriv_add, deriv_const

  -- compute the second derivative
  have D2f : deriv (deriv f) = fun x => 20*x^3 - 48*x^2 + 30*x - 26 := by
    ext x
    simp [Df]

  -- now specialise at x = 2
  constructor
  · -- deriv f 2 = 0
    rwa [Df] at *
    norm_num
  · -- deriv (deriv f) 2 > 0
    rwa [D2f] at *
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
  intro hf
  -- 1) compute the first derivative
  have h_deriv_f :
    deriv f = fun x => 20 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2 + 16890 * x + 76176 := by
    ext x
    -- simp knows all the deriv_pow, deriv_mul, deriv_add, etc.
    simp [hf]
  -- 2) compute the second derivative
  have h_deriv_deriv_f :
    deriv (deriv f) = fun x => 80 * x ^ 3 + 12 * x ^ 2 + 6 * x + 16890 := by
    ext x
    simp [h_deriv_f]
  -- 3) conclude the two numerical facts at x = -6
  constructor
  · -- first derivative = 0
    rw [h_deriv_f]; norm_num
  · -- second derivative > 0
    rw [h_deriv_deriv_f]; norm_num; linarith

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 5 + x ^ 3 + 279 * x ^ 2 + 1242 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  -- get rid of the f by turning it into its definition
  rintro rfl
  -- simp knows deriv of x^n, deriv of constants, and does the arithmetic
  simp

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
  intro hf
  -- simp will unfold `deriv f` to `fun x => 25*x^4 + 4*x^3 + 6*x^2`
  -- and `deriv (deriv f)` to `fun x => 100*x^3 + 12*x^2 + 12*x`
  simp [hf]
  -- the two goals become
  --   (25*0^4 + 4*0^3 + 6*0^2 = 0) ∧ (100*0^3 + 12*0^2 + 12*0 = 0)
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 2 * x ^ 3 - 170 * x ^ 2 + 944 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  -- first compute the first derivative
  have Df : deriv f = fun x => 8 * x^3 - 6 * x^2 - 340 * x + 944 := by
    ext x
    -- rewrite the definition of `f` and simplify all derivative‐laws
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow]
    ring
  -- now compute the second derivative
  have DDf : deriv (deriv f) = fun x => 24 * x^2 - 12 * x - 340 := by
    ext x
    -- rewrite using the previously computed `Df`
    rw [Df]
    simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow]
    ring
  -- finally check at x = 4
  constructor
  · -- f′(4) = 0
    simp [Df]; norm_num
  · -- f″(4) < 0
    simp [DDf]; norm_num

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
f = fun x => 2*x^2 - 20*x

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
  -- assume the defining equation for f
  intro hf

  -- compute the first derivative
  have h1 : deriv f = fun x => 24 * x ^ 5 + 12 * x ^ 2 - 142 * x + 106 := by
    ext x
    -- by `simp [hf]` all the `deriv_add`, `deriv_mul`, `deriv_pow''`, … fire
    rw [hf]
    simp

  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 120 * x ^ 4 + 24 * x - 142 := by
    ext x
    -- use the already computed `h1`
    rw [h1]
    simp

  -- finally evaluate at x = 1
  constructor
  · -- deriv f (1) = 24*1^5 + 12*1^2 - 142*1 + 106 = 0
    rw [h1]
    norm_num

  · -- deriv (deriv f) (1) = 120*1^4 + 24*1 - 142 = 2 > 0
    rw [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 16 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 16 := by
    ext x
    rw [hf]
    -- deriv (2*x^2 - 16*x) = deriv (2*x^2) - deriv (16*x)
    nth_rewrite 1 [deriv_sub]
    -- deriv (2*x^2) = 2 * deriv (x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (16*x) = 16 * deriv x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- prove differentiability where needed
    all_goals
      simp only [differentiableAt_const, differentiableAt_id, differentiableAt_pow]

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    rw [h_deriv_f]
    -- deriv (4*x - 16) = deriv (4*x) - deriv 16 = 4*1 - 0 = 4
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    all_goals
      simp only [differentiableAt_const, differentiableAt_id]

  -- now evaluate at x = 4
  constructor
  · -- deriv f 4 = 0
    nth_rewrite 1 [h_deriv_f]; ring
  · -- deriv (deriv f) 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]; norm_num

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
  intro hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x ^ 3 - 6 * x ^ 2 + 2 := by
    ext x
    -- unfold f
    rw [hf]
    -- (x^4 - 2*x^3 + 2*x)' = (x^4)' - (2*x^3)' + (2*x)'
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    -- deriv x^4 = 4*x^3
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (2 * x^3) = 2 * 3 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (2 * x) = 2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- collect terms
    ring

    -- side‐conditions: differentiability
    all_goals
      simp only
        [differentiableAt_id, differentiableAt_const, differentiableAt_pow,
         DifferentiableAt.add, DifferentiableAt.sub, DifferentiableAt.mul]

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 12 * x ^ 2 - 12 * x := by
    ext x
    rw [h_deriv_f]
    -- (4*x^3 - 6*x^2 + 2)' = 4*(x^3)' - 6*(x^2)' + (2)'
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    -- deriv x^3 = 3*x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv x^2 = 2*x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv 2 = 0
    nth_rewrite 1 [deriv_const]
    -- collect
    ring

    -- differentiability side‐conditions again
    all_goals
      simp only
        [differentiableAt_id, differentiableAt_const, differentiableAt_pow,
         DifferentiableAt.add, DifferentiableAt.sub, DifferentiableAt.mul]

  -- finish the proof
  constructor
  · -- deriv f 1 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) 1 = 0
    nth_rewrite 1 [h_deriv_deriv_f]
    ring

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 + x ^ 3 - 27 * x ^ 2 - 37 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 20 * x ^ 3 + 3 * x ^ 2 - 54 * x - 37 := by
    ext x
    -- after rewriting f we simplify the whole derivation chain
    simp [hf]
  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 60 * x ^ 2 + 6 * x - 54 := by
    ext x
    simp [h_deriv_f]
  -- now plug in x = -1
  constructor
  · simp [h_deriv_f]; norm_num
  · simp [h_deriv_deriv_f]; norm_num

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
  intro hf

  -- first derivative
  have h1 : deriv f =
    fun x => 30 * x ^ 5 - 5 * x ^ 4 + 4 * x ^ 3 + 9 * x ^ 2 - 2328 * x + 3708 := by
    ext x
    -- replace f with the concrete lambda, then simp‐deriv
    rw [hf]
    simp only [deriv, deriv_const, deriv_pow, deriv_mul_const, deriv_id,
      deriv_add, deriv_sub, deriv_mul]

  -- second derivative
  have h2 : deriv (deriv f) =
    fun x => 150 * x ^ 4 - 20 * x ^ 3 + 12 * x ^ 2 + 18 * x - 2328 := by
    ext x
    -- replace (deriv f) with the lambda from h1, then simp‐deriv again
    rw [h1]
    simp only [deriv, deriv_const, deriv_pow, deriv_mul_const, deriv_id,
      deriv_add, deriv_sub, deriv_mul]

  -- finish off the two goals
  constructor
  -- deriv f 2 = 0
  nth_rewrite 1 [h1]; ring
  -- deriv (deriv f) 2 < 0
  nth_rewrite 1 [h2]; ring; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 + 18 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro hf

  -- compute the first derivative of `f`
  have df : deriv f = fun x => 6 * x + 18 := by
    -- turn `deriv f x` into `deriv (fun x => 3*x^2 + 18*x) x`
    ext x; rw [hf]
    -- let `simp` use the usual differentiation lemmas
    simp

  -- compute the second derivative of `f`
  have ddf : deriv (deriv f) = fun x => 6 := by
    ext x; rw [df]
    simp

  -- conclude the two numeric facts at `x = -3`
  constructor
  · -- `deriv f (-3) = (fun x => 6*x+18) (-3) = 6*(-3)+18 = 0`
    simp [df]; norm_num
  · -- `deriv (deriv f) (-3) = (fun x => 6) (-3) = 6 > 0`
    simp [ddf]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - x ^ 3 - 397 * x ^ 2 - 2104 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  -- reduce `deriv f` and `deriv (deriv f)` using the definition of `f`
  simp [hf, deriv]
  -- now split into the two goals
  constructor
  · -- first derivative at x = -4
    ring_nf; norm_num
  · -- second derivative at x = -4
    ring_nf; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 - x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 - 59958 * x ^ 2 - 575316 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  -- Compute the first derivative
  have h1 : deriv f = fun x => 18 * x^5 - 5 * x^4 - 8 * x^3 + 15 * x^2 - 119916 * x - 575316 := by
    ext x
    -- `simp` knows `deriv_add`, `deriv_mul`, `deriv_pow'`, `deriv_const`, `deriv_id`, etc.
    simp [hf]
  -- Compute the second derivative
  have h2 : deriv (deriv f) = fun x => 90 * x^4 - 20 * x^3 - 24 * x^2 + 30 * x - 119916 := by
    ext x
    simp [h1]
  -- Now evaluate at x = -6
  constructor
  · calc
      deriv f (-6)
        = (fun x => 18 * x^5 - 5 * x^4 - 8 * x^3 + 15 * x^2 - 119916 * x - 575316) (-6) := by simp [h1]
    _ = 0 := by norm_num
  · calc
      deriv (deriv f) (-6)
        = (fun x => 90 * x^4 - 20 * x^3 - 24 * x^2 + 30 * x - 119916) (-6) := by simp [h2]
    _ = 0 := by norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 + 11 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
  -- compute the first derivative
  have h1 : deriv f = fun x => 15 * x ^ 4 - 16 * x ^ 3 - 6 * x ^ 2 - 4 * x + 11 := by
    ext x
    simp [hf]
  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 60 * x ^ 3 - 48 * x ^ 2 - 12 * x - 4 := by
    ext x
    simp [h1]
  -- prove the two goals at x = 1
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 1200 * x ^ 2 + 3840 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) = 0) := by
deriv f = λ x, 5*x^6 - 1200*x^2 + 3840*x

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) > 0) := by
  intro hf

  -- 1) compute f' = 2*x
  have h_deriv_f : deriv f = fun x => 2 * x := by
    ext x
    -- rewrite the definition of f
    rw [hf]
    -- use the standard derivative of x^n
    simp [deriv_pow'']

  -- 2) compute f'' = 2
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    -- substitute the formula for f'
    rw [h_deriv_f]
    -- derivative of (fun x => 2 * x) is 2
    simp

  -- 3) finish by evaluating at 0
  constructor
  · -- f'(0) = 2*0 = 0
    rw [h_deriv_f]
    norm_num
  · -- f''(0) = 2 > 0
    rw [h_deriv_deriv_f]
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
  intro hf

  -- compute the first derivative
  have h_deriv_f :
    deriv f = fun x => 18*x^5 - 25*x^4 - 20*x^3 - 9*x^2 + 4*x := by
    ext x
    -- rewrite f
    rw [hf]
    -- unfold deriv, apply all the deriv_* lemmas, then tidy up
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring

  -- compute the second derivative
  have h_deriv₂_f :
    deriv (deriv f) = fun x => 90*x^4 - 100*x^3 - 60*x^2 - 18*x + 4 := by
    ext x
    -- rewrite the first‐derivative definition
    rw [h_deriv_f]
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring

  -- now evaluate at x = 0
  constructor
  · -- deriv f 0 = 0
    rw [h_deriv_f]
    simp
  · -- deriv (deriv f) 0 > 0
    rw [h_deriv₂_f]
    simp
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 10 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intros hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 2 * x + 10 := by
    ext x
    rw [hf]
    -- deriv (x^2 + 10 * x) = deriv (x^2) + deriv (10 * x)
    nth_rewrite 1 [deriv_add]
    -- deriv (x^2)
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (10 * x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    -- side‐conditions for differentiability
    exact differentiableAt_pow _
    exact differentiableAt_mul_const _

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    rw [h_deriv_f]
    -- deriv (2 * x + 10) = deriv (2 * x) + deriv 10
    nth_rewrite 1 [deriv_add]
    -- deriv (2 * x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    -- deriv (10)
    nth_rewrite 1 [deriv_const]
    ring
    -- side‐conditions again
    exact differentiableAt_mul_const _
    exact differentiableAt_const _

  -- conclude
  constructor
  · -- show deriv f (-5) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- show deriv (deriv f) (-5) > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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

  -- 1) compute f'
  have h_deriv_f : deriv f = fun x => 30 * x ^ 5 + 3 * x ^ 2 - 12126 * x - 29115 := by
    ext x
    -- rewrite f to its definition
    rw [hf]
    -- simplify the derivative using `simp`
    -- (this fires `deriv_add, deriv_mul, deriv_sub, deriv_pow, deriv_const, deriv_id` etc.)
    simp [deriv]
    ring

  -- 2) compute f''
  have h_deriv_deriv_f :
      deriv (deriv f) = fun x => 150 * x ^ 4 + 6 * x - 12126 := by
    ext x
    -- rewrite f' to its definition
    rw [h_deriv_f]
    -- simplify the derivative again
    simp [deriv]
    ring

  -- 3) conclude the two facts at x = -3
  constructor
  · -- f'(-3) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- f''(-3) > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 8 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro hf

  -- compute the first derivative
  have h_deriv : deriv f = fun x => 2 * x + 8 := by
    ext x
    -- rewrite f to x^2 + 8*x and then simp the derivative
    rw [hf]
    simp only [deriv_pow', deriv_mul_const, deriv_id, deriv_add, deriv_const]

  -- compute the second derivative
  have h_deriv₂ : deriv (deriv f) = fun x => 2 := by
    ext x
    -- rewrite deriv f to 2*x+8 and then simp again
    rw [h_deriv]
    simp only [deriv_add, deriv_mul_const, deriv_const, deriv_id]

  -- now plug in x = -4 and finish
  constructor
  · -- deriv f (-4) = 2 * (-4) + 8 = 0
    nth_rewrite 1 [h_deriv]
    norm_num
  · -- deriv (deriv f) (-4) = 2 > 0
    nth_rewrite 1 [h_deriv₂]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 57 * x ^ 2 + 360 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) < 0) := by

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 16 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) > 0) := by
  intro hf

  -- first derivative f'
  have h_deriv_f : deriv f = fun x => 4 * x + 16 := by
    ext x
    -- unfold f
    rw [hf]
    -- deriv (2*x^2 + 16*x) = deriv (2*x^2) + deriv (16*x)
    nth_rewrite 1 [deriv_add]
    -- deriv (2*x^2)  = 2 * deriv (x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    -- deriv (x^2) = 2 * x
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (16*x) = 16 * deriv x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- obligations for differentiability
    exact differentiableAt_const _
    exact differentiableAt_pow (2 : ℕ)
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id

  -- second derivative f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    -- unfold f'
    rw [h_deriv_f]
    -- deriv (4*x + 16) = deriv (4*x) + deriv 16
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability
    exact differentiableAt_mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  -- now evaluate at x = -4
  constructor
  · -- f'(-4) = 4*(-4) + 16 = 0
    nth_rewrite 1 [h_deriv_f]
    norm_num
  · -- f''(-4) = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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
  -- replace f by its defining λ-term
  subst hf
  -- simp knows about deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id
  simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  -- after simplification we get
  -- ⊢ (fun x : ℝ => 12 * x ^ 2 + 78 * x + 126) (-3) = 0
  --   ∧ (fun x : ℝ => 24 * x + 78) (-3) > 0
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 72 * x ^ 2 + 432 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro hf
  -- compute the first derivative
  have h1 : deriv f = fun x => 12 * x ^ 2 + 144 * x + 432 := by
    ext x
    -- rewrite f into the concrete cubic
    rw [hf]
    -- unfold `deriv (· + ·)`, `deriv (c * ·)`, `deriv (· ^ n)`, `deriv id`, `deriv (fun _ => c)`
    simp
    -- collect coefficients
    ring

  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 24 * x + 144 := by
    ext x
    rw [h1]
    simp
    ring

  -- now check at x = -6
  constructor
  · -- f'(-6) = 0
    rw [h1]
    norm_num
  · -- f''(-6) = 0
    rw [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 24 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  -- substitute the definition of f
  subst hf

  -- compute the first derivative:  d/dx (2*x^2 + 24*x) = 4*x + 24
  have h1 : deriv f = fun x => 4*x + 24 := by
    ext x
    -- `simp [deriv_add, deriv_mul, deriv_pow, deriv_id]` knows how to differentiate
    simp [deriv_add, deriv_mul, deriv_pow, deriv_id]

  -- compute the second derivative: d/dx (4*x + 24) = 4
  have h2 : deriv (deriv f) = fun _ => 4 := by
    ext x
    simp [deriv_add, deriv_mul, deriv_const, deriv_id]

  -- finally evaluate at x = -6
  constructor
  · -- first derivative at -6 is 4*(-6) + 24 = 0
    simp [h1]; norm_num
  · -- second derivative at -6 is 4 > 0
    simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 4 * x ^ 3 - 48 * x ^ 2 - 84 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) = 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 24 * x ^ 5 + 12 * x ^ 2 - 96 * x - 84 := by
    ext x
    -- unfold f and distribute deriv
    rw [hf]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
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
    -- all the differentiability side‐conditions
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 120 * x ^ 4 + 24 * x - 96 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- now evaluate at x = -1
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

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
  intro hf
  -- first derivative
  have h1 : deriv f = fun x => 12 * x^2 + 92 * x + 176 := by
    ext x; simp [hf]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 24 * x + 92 := by
    ext x; simp [h1]
  -- now the two numerical checks
  constructor
  · simpa [h1] using (by norm_num : deriv f (-4) = 0)
  · simpa [h2] using (by norm_num : deriv (deriv f) (-4) < 0)

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 + 4 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
  intro hf
  -- 1) compute deriv f
  have h_deriv_f : deriv f = fun x => 4 * x + 4 := by
    ext x
    -- rewrite f to 2*x^2 + 4*x
    rw [hf]
    -- derivative of sum
    nth_rewrite 1 [deriv_add]
    -- derivative of 2*x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- derivative of 4*x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- side-conditions: differentiability
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
  -- 2) compute deriv (deriv f)
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    -- rewrite deriv f to 4*x+4
    rw [h_deriv_f]
    -- derivative of sum
    nth_rewrite 1 [deriv_add]
    -- derivative of 4*x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- derivative of 4
    nth_rewrite 1 [deriv_const]
    ring
    -- side-conditions
    exact differentiableAt_id
    exact differentiableAt_const _
  -- 3) finish the ∧
  constructor
  · -- deriv f (-1) = 4*(-1) + 4 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) (-1) = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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
  intro hf

  -- First derivative
  have h_deriv_f : deriv f =
    fun x => 18 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3 - 15 * x ^ 2 - 108 * x - 76 := by
    ext x
    -- unfold f
    rw [hf]
    -- apply linearity and product‐powers
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- side‐conditions: all the pieces are differentiable
    all_goals
      try
        solve_by_elim
          [ differentiableAt_const
          , differentiableAt_id
          , differentiableAt_pow
          , differentiableAt_mul
          , differentiableAt_add
          , differentiableAt_sub ]

  -- Second derivative
  have h_deriv_deriv_f : deriv (deriv f) =
    fun x => 90 * x ^ 4 + 20 * x ^ 3 + 12 * x ^ 2 - 30 * x - 108 := by
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
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    all_goals
      try
        solve_by_elim
          [ differentiableAt_const
          , differentiableAt_id
          , differentiableAt_pow
          , differentiableAt_mul
          , differentiableAt_add
          , differentiableAt_sub ]

  -- Now evaluate at x = -1
  constructor
  · -- deriv f (-1) = 0
    nth_rewrite 1 [h_deriv_f]
    ring

  · -- deriv (deriv f) (-1) > 0
    nth_rewrite 1 [h_deriv_deriv_f]
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
open Real

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 21 * x ^ 2 + 36 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf

  -- first derivative of f
  have h_deriv_f : deriv f = fun x => 12 * x ^ 2 + 42 * x + 36 := by
    ext x
    rw [hf]
    -- 4*x^3 + (21*x^2 + 36*x)
    nth_rewrite 1 [deriv_add]
    -- deriv (4*x^3)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- plus deriv (21*x^2 + 36*x)
    nth_rewrite 1 [deriv_add]
    -- deriv (21*x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- plus deriv (36*x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- differentiability witnesses
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- second derivative of f
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 24 * x + 42 := by
    ext x
    rw [h_deriv_f]
    -- deriv (12*x^2 + (42*x + 36))
    nth_rewrite 1 [deriv_add]
    -- deriv (12*x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- plus deriv (42*x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- plus deriv (36) = 0
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability witnesses
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- conclude at x = -2
  constructor
  · -- deriv f (-2) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- second derivative at -2 is negative
    nth_rewrite 1 [h_deriv_deriv_f]
    ring
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 10 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  intro hf
  -- 1) compute the first derivative
  have h1 : deriv f = fun x => 2*x - 10 := by
    ext x
    rw [hf]
    simp [deriv_pow, deriv_mul, deriv_sub, deriv_id, deriv_const]
  -- 2) compute the second derivative
  have h2 : deriv (deriv f) = fun _ => 2 := by
    ext x
    rw [h1]
    simp [deriv_mul, deriv_const]
  -- 3) check the values at x = 5
  constructor
  · -- deriv f 5 = (2*5 - 10) = 0
    rw [h1]
    norm_num
  · -- deriv (deriv f) 5 = 2 > 0
    rw [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 46 * x ^ 2 + 235 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
  intro hf
  -- first derivative
  have h1 : deriv f = fun x => 9*x^2 - 92*x + 235 := by
    ext x
    simp [hf]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 18*x - 92 := by
    ext x
    simp [h1]
  -- now evaluate at x = 5
  constructor
  · simp [h1]; norm_num                           -- deriv f 5 = 9*25 - 92*5 + 235 = 0
  · simp [h2]; norm_num                           -- deriv (deriv f) 5 = 18*5 - 92 = -2 < 0

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 2 * x ^ 3 - 69 * x ^ 2 + 392 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro hf
  -- compute the first derivative
  have h1 : deriv f = fun x => 4*x^3 - 6*x^2 - 138*x + 392 := by
    ext x
    simp [hf]
  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 12*x^2 - 12*x - 138 := by
    ext x
    simp [h1]
  -- now plug in x = 4
  simp [h1, h2]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 - 4 * x ^ 2 + 5 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) < 0) := by
have h_deriv : deriv f = fun x => 3*x^2 - 8*x + 5

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 3 + 32 * x + 10 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) < 0) := by
  intro hf

  -- compute the first derivative
  have h1 : deriv f = fun x => 3 * x^2 + 20 * x + 32 := by
    ext x
    -- unfold f and then let `simp` do the rest
    rw [hf]
    simp

  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 6 * x + 20 := by
    ext x
    -- rewrite with h1, then `simp` again
    rw [h1]
    simp

  -- now evaluate at x = -4
  constructor
  · -- first derivative at -4
    simp [h1]; norm_num
  · -- second derivative at -4
    simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 - 48 * x ^ 2 - 128 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) = 0) := by
  -- first compute the first derivative
  have h1 : deriv f = fun x => 8 * x ^ 3 - 96 * x - 128 := by
    ext x
    simp [hf]
  -- now compute the second derivative
  have h2 : deriv (deriv f) = fun x => 24 * x ^ 2 - 96 := by
    ext x
    simp [h1]
  -- finally evaluate at x = -2
  constructor
  · -- deriv f (-2) = 0
    rw [h1]
    norm_num
  · -- deriv (deriv f) (-2) = 0
    rw [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 3 + 60 * x ^ 2 + 300 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 12 * x ^ 2 + 120 * x + 300 := by
    ext x
    rw [hf]
    -- deriv (4 * x^3)
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (60 * x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (300 * x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- differentiability witnesses
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 24 * x + 120 := by
    ext x
    rw [h_deriv_f]
    -- deriv (12 * x^2)
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (120 * x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- deriv (300)
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability witnesses
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- now evaluate at x = -5
  constructor
  nth_rewrite 1 [h_deriv_f]; ring
  nth_rewrite 1 [h_deriv_deriv_f]; ring
  norm_num

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
  -- substitute the definition of f
  subst hf
  -- compute the first and second derivatives
  norm_deriv
  -- evaluate at x = 5 and finish with simple numerics
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 + 4 * x ^ 5 + 5 * x ^ 4 - x ^ 3 - 105 * x - 69 * x ^ 2) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  -- first compute f'
  have h1 : deriv f = fun x => 30 * x ^ 5 + 20 * x ^ 4 + 20 * x ^ 3 - 3 * x ^ 2 - 138 * x - 105 := by
    ext x
    dsimp [deriv]
    rw [hf]
    ring
  -- then compute f''
  have h2 : deriv (deriv f) = fun x => 150 * x ^ 4 + 80 * x ^ 3 + 60 * x ^ 2 - 6 * x - 138 := by
    ext x
    dsimp [deriv]
    rw [h1]
    ring
  -- finally evaluate at x = -1
  split
  · dsimp [h1]; norm_num
  · dsimp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 - 4 * x ^ 5 - 3 * x ^ 4 - 4 * x ^ 3 + 289872 * x - 29520 * x ^ 2) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  -- assume the explicit form of f
  intro hf

  -- compute the first derivative
  have h₁ : deriv f = fun x => 12*x^5 - 20*x^4 - 12*x^3 - 12*x^2 - 59040*x + 289872 := by
    ext x
    -- rw the definition of f, then simp all the deriv_* lemmas
    simp [hf]

  -- compute the second derivative
  have h₂ : deriv (deriv f) = fun x => 60*x^4 - 80*x^3 - 36*x^2 - 24*x - 59040 := by
    ext x
    -- rw the above expression for deriv f, then simp again
    simp [h₁]

  -- finish by showing both are zero at x = 6
  constructor
  · -- deriv f 6 = 0
    simp [h₁]
  · -- deriv (deriv f) 6 = 0
    simp [h₂]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 4 := by
    ext x
    -- rewrite f
    rw [hf]
    -- d (2*x^2 - 4*x) = d(2*x^2) - d(4*x)
    nth_rewrite 1 [deriv_sub]
    -- d(2*x^2) = 2 * d(x^2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- d(4*x) = 4 * d(x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- differentiability side-goals
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact differentiableAt_id
      try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    -- rewrite deriv f
    rw [h_deriv_f]
    -- d(4*x - 4) = d(4*x) - d(4)
    nth_rewrite 1 [deriv_sub]
    -- d(4*x) = 4 * d(x)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- d(4) = 0
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability side-goals
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id

  -- conclude at x = 1
  constructor
  -- deriv f (1) = 4*1 - 4 = 0
  nth_rewrite 1 [h_deriv_f]; ring
  -- deriv (deriv f) (1) = 4 > 0
  nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 + 2 * x ^ 3 + 45 * x ^ 2 + 64 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  -- first derivative
  have h1 : deriv f = fun x => 20 * x ^ 4 + 6 * x ^ 2 + 90 * x + 64 := by
    ext x
    rw [hf]
    -- now all the usual `deriv_const`, `deriv_id`, `deriv_pow`, `deriv_mul`, `deriv_add` lemmas
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 80 * x ^ 3 + 12 * x + 90 := by
    ext x
    rw [h1]
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
  -- put it all together at x = -1
  constructor
  · rw [h1]; norm_num
  · rw [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - 4 * x ^ 4 - 2 * x ^ 3 + 9470 * x ^ 2 + 84480 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) > 0) := by
  -- first derivative
  have hf1 : deriv f = fun x => 20*x^4 - 16*x^3 - 6*x^2 + 18940*x + 84480 := by
    ext x
    simp [hf]
  -- second derivative
  have hf2 : deriv (deriv f) = fun x => 80*x^3 - 48*x^2 - 12*x + 18940 := by
    ext x
    simp [hf1]
  -- evaluate at x = -6
  constructor
  · simp [hf1]; norm_num
  · simp [hf2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 5 * x ^ 5 - 2 * x ^ 4 + 5 * x ^ 3 + 290 * x ^ 2 + 822 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  -- 1) compute f'
  have h1 : deriv f = fun x => 6 * x ^ 5 + 25 * x ^ 4 - 8 * x ^ 3 + 15 * x ^ 2 + 580 * x + 822 := by
    ext x
    -- now simp knows all the deriv‐rules for +, *, ^, constants, … 
    simp [hf]

  -- 2) compute f''
  have h2 : deriv (deriv f) = fun x => 30 * x ^ 4 + 100 * x ^ 3 - 24 * x ^ 2 + 30 * x + 580 := by
    ext x
    simp [h1]

  -- 3) evaluate at x = -3
  constructor
  · -- f'(-3) = 0
    nth_rewrite 1 [h1]
    norm_num

  · -- f''(-3) > 0
    nth_rewrite 1 [h2]
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
  -- compute f'
  have h_deriv_f : deriv f = fun x => 25*x^4 - 20*x^3 + 6*x^2 - 56*x + 45 := by
    ext x
    rw [hf]
    simp [deriv_const, deriv_id, deriv_pow, deriv_mul, deriv_add, deriv_sub]
  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 100*x^3 - 60*x^2 + 12*x - 56 := by
    ext x
    rw [h_deriv_f]
    simp [deriv_const, deriv_id, deriv_pow, deriv_mul, deriv_add, deriv_sub]
  -- now specialise at x = 1
  constructor
  · -- f' 1 = 25 - 20 + 6 - 56 + 45 = 0
    nth_rewrite 1 [h_deriv_f]
    norm_num
  · -- f'' 1 = 100 - 60 + 12 - 56 = -4 < 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 3 - 18 * x ^ 2 + 54 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  intro hf

  -- First derivative
  have h1 : deriv f = fun x => 6 * x ^ 2 - 36 * x + 54 := by
    ext x
    -- rewrite f into the concrete polynomial
    rw [hf]
    -- the following simp uses the lemmas deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id
    simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id]

  -- Second derivative
  have h2 : deriv (deriv f) = fun x => 12 * x - 36 := by
    ext x
    -- rewrite the formula for deriv f
    rw [h1]
    -- again simp handles deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]

  -- now evaluate at x = 3
  constructor
  · -- deriv f 3 = 6*3^2 - 36*3 + 54 = 0
    nth_rewrite 1 [h1]
    ring
  · -- deriv (deriv f) 3 = 12*3 - 36 = 0
    nth_rewrite 1 [h2]
    ring

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 - 38 * x ^ 2 + 160 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  -- 1) compute the first derivative
  have h_deriv_f : deriv f = fun x => 9*x^2 - 76*x + 160 := by
    ext x
    -- replace f with the explicit lambda and let `simp` do the work
    simp [hf]
  -- 2) compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 18*x - 76 := by
    ext x
    -- replace deriv f with the explicit lambda and let `simp` do the work
    simp [h_deriv_f]
  -- 3) finish by evaluating at x = 4
  constructor
  · -- f′(4) = 0
    nth_rewrite 1 [h_deriv_f]
    norm_num
  · -- f″(4) = -4 < 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 6 - 3 * x ^ 5 - 50624 * x ^ 2 - 403115 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  intro hf
  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 30 * x ^ 5 - 15 * x ^ 4 - 101248 * x - 403115 := by
    ext x
    -- rewrite f to its concrete lambda
    rw [hf]
    -- f = (5*x^6 - 3*x^5 - 50624*x^2) - 403115*x
    nth_rewrite 1 [deriv_sub]
    -- = deriv (5*x^6 - 3*x^5 - 50624*x^2) - deriv (403115*x)
    nth_rewrite 1 [deriv_sub]
    -- break 5*x^6 - 3*x^5
    nth_rewrite 1 [deriv_sub]
    -- deriv (5*x^6), deriv (3*x^5), deriv (50624*x^2), deriv (403115*x)
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    ring
    -- now discharge all the differentiability side‐conditions
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 150 * x ^ 4 - 60 * x ^ 3 - 101248 := by
    ext x
    -- rewrite to the concrete first‐derivative
    rw [h_deriv_f]
    -- (30*x^5 - 15*x^4 - 101248*x) - 403115
    nth_rewrite 1 [deriv_sub]
    -- deriv (30*x^5 - 15*x^4 - 101248*x) - deriv (403115)
    nth_rewrite 1 [deriv_sub]
    -- break 30*x^5 - 15*x^4
    nth_rewrite 1 [deriv_sub]
    -- now each piece
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- discharge side‐conditions again
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))

  -- now prove the two numerical facts
  constructor
  · -- f′(-5) = 0
    rw [h_deriv_f]
    norm_num
  · -- f″(-5) > 0
    rw [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 5 * x ^ 5 + x ^ 4 - 107 * x ^ 2 - 412 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  -- first compute f′
  have df : deriv f = fun x => 12 * x ^ 5 + 25 * x ^ 4 + 4 * x ^ 3 - 214 * x - 412 := by
    -- `simp [deriv]` knows all the lemmas
    -- @[simp] deriv_const, deriv_id, deriv_pow, deriv_mul_const, deriv_add, deriv_sub …
    simpa [hf] using by simp [deriv]
  -- then compute f″
  have ddf : deriv (deriv f) = fun x => 60 * x ^ 4 + 100 * x ^ 3 + 12 * x ^ 2 - 214 := by
    simpa [df] using by simp [deriv]
  -- now evaluate at x = -2
  simpa [df, ddf] using by norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - 55 * x ^ 2 + 222 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) < 0) := by
-- `simp [hf]` unfolds `deriv f` and `deriv (deriv f)` using the definitional lemmas
-- `deriv_pow`, `deriv_const`, `deriv_id`, `deriv_add` etc.,
-- and reduces the goal to a plain numeric statement
  simp [hf]
-- now `norm_num` computes
--    4*3^3 - 110*3 + 222 = 0
-- and
--    12*3^2 - 110 = -2 < 0
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
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 2 * x - 6 := by
    ext x
    rw [hf]
    -- ∂/∂x (x^2 - 6*x) = 2*x - 6
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    -- side‐conditions: differentiability
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    rw [h_deriv_f]
    -- ∂/∂x (2*x - 6) = 2
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    -- side‐conditions: differentiability
    exact differentiableAt_id
    exact differentiableAt_const _

  -- conclude at x = 3
  constructor
  · -- first derivative vanishes at 3
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- second derivative is 2 > 0 at 3
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
  intro hf
  -- 1) Compute deriv f
  have h_deriv_f : deriv f = fun x => 4 * x - 24 := by
    ext x
    -- rewrite f
    rw [hf]
    -- deriv (2*x^2) = 2 * (2*x) = 4*x, deriv (24*x) = 24
    simp [deriv_mul, deriv_pow'', deriv_const, deriv_id''] 
  -- 2) Compute deriv (deriv f)
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    rw [h_deriv_f]
    -- deriv (4*x) = 4, deriv (24) = 0
    simp [deriv_mul, deriv_const, deriv_id'']
  -- 3) Check at x = 6
  constructor
  · -- deriv f 6 = (4*6 - 24) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) 6 = 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 - 5 * x ^ 3 - 738 * x ^ 2 - 5724 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  intro hf
  -- first derivative
  have h1 : deriv f = fun x => 12*x^3 - 15*x^2 - 1476*x - 5724 := by
    ext x
    -- `simp` knows all the standard derivative rules and `hf` unfolds `f`
    simp [hf]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 36*x^2 - 30*x - 1476 := by
    ext x
    simp [h1]
  -- finally evaluate at x = -6
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

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
  intro hf

  -- first derivative
  have h₁ : deriv f = fun x => 24 * x ^ 5 - 10 * x ^ 4 - 4 * x ^ 3 := by
    ext x
    rw [hf]
    -- deriv (4 * x ^ 6) = 4 * 6 * x ^ 5
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (2 * x ^ 5) = 2 * 5 * x ^ 4
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (x ^ 4) = 4 * x ^ 3
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    ring
    -- side-proofs that everything is differentiable
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- second derivative
  have h₂ : deriv (deriv f) = fun x => 120 * x ^ 4 - 40 * x ^ 3 - 12 * x ^ 2 := by
    ext x
    rw [h₁]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_sub]
    -- deriv (24 * x ^ 5) = 24 * 5 * x ^ 4
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (10 * x ^ 4) = 10 * 4 * x ^ 3
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (4 * x ^ 3) = 4 * 3 * x ^ 2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    ring
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact differentiableAt_id

  -- conclude at x = 0
  constructor
  · nth_rewrite 1 [h₁]; ring
  · nth_rewrite 1 [h₂]; ring
  · norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 - 12 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 2 * x - 12 := by
    ext x
    -- rewrite the definition of f
    rw [hf]
    -- deriv (x^2 - 12*x) = deriv x^2 - 12 * deriv x
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_pow'']      -- deriv (x^2)
    nth_rewrite 1 [deriv_id'']       -- deriv x
    nth_rewrite 1 [deriv_mul]        -- deriv (12 * x)
    nth_rewrite 1 [deriv_const]      
    nth_rewrite 1 [deriv_id'']
    -- now do the algebra
    ring
    -- supply the needed differentiability facts
    exact differentiableAt_pow (2 : ℕ)
    exact (differentiableAt_const _).mul differentiableAt_id

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    -- rewrite with the first‐derivative formula
    rw [h_deriv_f]
    -- deriv (2*x - 12) = 2*deriv x - 0
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- finish the algebra
    ring
    -- differentiability
    exact differentiableAt_id
    exact differentiableAt_const _

  -- assemble the goal
  constructor
  · -- deriv f 6 = 2*6 - 12 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) 6 = 2 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 6 + 3 * x ^ 5 + 2 * x ^ 4 - 3 * x ^ 3 - 9828 * x ^ 2 - 63376 * x) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  -- we split the conjunction into two goals
  split
  -- first show deriv f (-4) = 0
  · simp [hf]; norm_num
  -- then show deriv (deriv f) (-4) = 0
  · simp [hf]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 5 * x ^ 4 - 4 * x ^ 3 - 253 * x ^ 2 + 740 * x) → (deriv f (2:ℝ) = 0 ∧ deriv (deriv f) (2:ℝ) > 0) := by
  -- assume f is the given quintic
  intro hf

  -- compute the first‐derivative
  have h_deriv_f : deriv f = fun x => 10*x^4 + 20*x^3 - 12*x^2 - 506*x + 740 := by
    ext x
    -- unfold f and differentiate term‐by‐term
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_id'', deriv_const]

  -- compute the second‐derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 40*x^3 + 60*x^2 - 24*x - 506 := by
    ext x
    -- unfold the first derivative and differentiate again
    rw [h_deriv_f]
    simp [deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_id'', deriv_const]

  -- now check the values at x = 2
  constructor
  · -- first derivative at 2 is zero
    rw [h_deriv_f]; norm_num

  · -- second derivative at 2 is positive
    rw [h_deriv_deriv_f]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 6 + 5 * x ^ 4 + 5 * x ^ 3 - 5175 * x ^ 2 + 24543 * x) → (deriv f (3:ℝ) = 0 ∧ deriv (deriv f) (3:ℝ) = 0) := by
  -- rewrite `f` into the explicit polynomial and expand all derivs
  simp [hf,
    deriv_add, deriv_sub,
    deriv_const_mul, deriv_mul_const,
    deriv_pow, deriv_id]
  -- now everything is a numeral, finish with norm_num
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 - 72 * x ^ 2 - 595 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) > 0) := by
  -- substitute the definition of f everywhere
  subst hf

  -- compute the first derivative explicitly
  have h1 : deriv (fun x => x^4 + 5*x^3 - 72*x^2 - 595*x) =
            fun x => 4*x^3 + 15*x^2 - 144*x - 595 := by
    ext x
    simp [deriv_pow, deriv_mul_const, deriv_add]

  -- compute the second derivative explicitly
  have h2 : deriv (fun x => 4*x^3 + 15*x^2 - 144*x - 595) =
            fun x => 12*x^2 + 30*x - 144 := by
    ext x
    simp [deriv_pow, deriv_mul_const, deriv_add]

  -- now prove the two numerical facts
  constructor
  · -- deriv f (-5) = 0
    nth_rewrite 1 [h1]
    norm_num

  · -- deriv (deriv f) (-5) > 0
    nth_rewrite 1 [h2]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  5 * x ^ 4 - 2 * x ^ 3 - 719 * x ^ 2 + 4840 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) > 0) := by
  -- replace f with its defining λ‐term
  subst hf

  -- compute the first derivative
  have h1 :
    deriv (fun x => 5*x^4 - 2*x^3 - 719*x^2 + 4840*x)
      = fun x => 20*x^3 - 6*x^2 - 1438*x + 4840 := by
    simp [deriv,
          deriv_add, deriv_sub,
          deriv_const_mul, deriv_mul_const,
          deriv_pow, deriv_id, deriv_const]

  -- compute the second derivative
  have h2 :
    deriv (fun x => 20*x^3 - 6*x^2 - 1438*x + 4840)
      = fun x => 60*x^2 - 12*x - 1438 := by
    simp [deriv,
          deriv_add, deriv_sub,
          deriv_const_mul, deriv_mul_const,
          deriv_pow, deriv_id, deriv_const]

  -- now plug in x = 5
  constructor
  · simp [h1]; norm_num                           -- deriv f 5 = 0
  · simp [h2]; norm_num                           -- deriv (deriv f) 5 = 2 > 0

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 2 + 2 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) > 0) := by
example (f : ℝ → ℝ) :
  (f = fun x => x^2 + 2*x) →
  (deriv f (-1) = 0 ∧ deriv (deriv f) (-1) > 0)

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
  intro hf'
  -- first compute the first derivative
  have h1 : deriv f = fun x => 24*x^5 - 20*x^4 - 12*x^3 + 6*x^2 - 171432*x - 818856 := by
    ext x
    -- `simp` automatically uses all the `deriv_add`, `deriv_mul`, `deriv_pow''`,
    -- `deriv_const`, `deriv_id''`, plus the differentiability lemmas
    simp [hf']
  -- now compute the second derivative
  have h2 : deriv (deriv f) = fun x => 120*x^4 - 80*x^3 - 36*x^2 + 12*x - 171432 := by
    ext x
    simp [h1]
  -- finish by rewriting with h1, h2 and using `norm_num`
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 4 * x) → (deriv f (1:ℝ) = 0 ∧ deriv (deriv f) (1:ℝ) > 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x - 4 := by
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
    -- side-conditions: differentiability
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact differentiableAt_id

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 4 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- side-conditions again
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- conclude the two goals
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 5 + 3 * x ^ 4 - 3 * x ^ 3 + 12896 * x - 2170 * x ^ 2) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  -- first compute the first derivative
  have h₁ : deriv f = fun x => 15*x^4 + 12*x^3 - 9*x^2 - 4340*x + 12896 := by
    ext x
    -- unfold `f` and use all the `deriv_add`, `deriv_mul_const`, `deriv_pow`, … lemmas
    simp [hf]
  -- now compute the second derivative
  have h₂ : deriv (deriv f) = fun x => 60*x^3 + 36*x^2 - 18*x - 4340 := by
    ext x
    simp [h₁]
  -- finally evaluate at x = 4
  constructor
  · simp [h₁]; norm_num
  · simp [h₂]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 - x ^ 3 - 3 * x ^ 2 ) → (deriv f (0:ℝ) = 0 ∧ deriv (deriv f) (0:ℝ) < 0) := by
  -- 1) rewrite f into its defining λ‐expression
  rw [hf]
  -- 2) compute the first derivative of x^4 - x^3 - 3*x^2
  have h1 : deriv (fun x => x^4 - x^3 - 3 * x^2) = fun x => 4 * x^3 - 3 * x^2 - 6 * x := by
    ext x
    -- `simp` automatically uses deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_const, deriv_id
    simp
  -- 3) compute the second derivative of 4*x^3 - 3*x^2 - 6*x
  have h2 : deriv (fun x => 4 * x^3 - 3 * x^2 - 6 * x) = fun x => 12 * x^2 - 6 * x - 6 := by
    ext x
    simp
  -- 4) now split the goal into the two conjuncts, rewrite with h1,h2, and finish by simp+norm_num
  constructor
  · -- deriv f 0 = 0
    simp [h1]
    norm_num
  · -- deriv (deriv f) 0 < 0
    simp [h1, h2]
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
  -- first compute f′
  have h_deriv_f : deriv f = fun x => 12 * x ^ 5 - 15354 * x + 49128 := by
    ext x
    -- unfold f
    rw [hf]
    -- (2 * x^6) + (49128 * x) - (7677 * x^2)
    --        ↑deriv_add
    nth_rewrite 1 [deriv_add]
    -- 2 * x^6   + 49128 * x   - 7677 * x^2
    --        ↑deriv_sub
    nth_rewrite 1 [deriv_sub]
    -- 2 * x^6   + 49128 * x
    --        ↑deriv_add
    nth_rewrite 1 [deriv_add]
    -- now three summands: 2*x^6, 49128*x, and -7677*x^2
    -- deriv of 2 * x^6
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv of 49128 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- deriv of - 7677 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- collect terms
    ring
    -- side‐conditions: differentiability
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- now compute (f′)′
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 60 * x ^ 4 - 15354 := by
    ext x
    rw [h_deriv_f]
    -- deriv of (12*x^5) - (15354*x) + 49128
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    -- deriv of 12 * x^5
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv of -15354 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- deriv of constant 49128
    nth_rewrite 1 [deriv_const]
    ring
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  -- now finish the two goals at x = 4
  constructor
  · -- deriv f 4 = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- deriv (deriv f) 4 > 0
    nth_rewrite 1 [h_deriv_deriv_f]
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 5 + 2 * x ^ 4 - x ^ 3 + 423 * x ^ 2 + 1971 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) = 0) := by
  -- replace `f` by the concrete lambda
  subst hf
  -- now `f = fun x => …`, so `deriv f` and `deriv (deriv f)` will be computed
  simp [deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_const, deriv_id]
  -- two numeric goals:
  --   (deriv f) (-3) = 0
  --   (deriv (deriv f)) (-3) = 0
  all_goals norm_num

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
  intro hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 6 * x - 18 := by
    ext x
    rw [hf]
    -- deriv (3 * x ^ 2 - 18 * x) = deriv (3 * x ^ 2) - deriv (18 * x)
    nth_rewrite 1 [deriv_sub]
    -- deriv (3 * x ^ 2) = 3 * deriv (x ^ 2)
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (18 * x) = 18 * 1
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- side-conditions: differentiability
    exact differentiableAt_mul (differentiableAt_const _) (differentiableAt_pow _)
    exact differentiableAt_mul (differentiableAt_const _) (differentiableAt_id)

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 6 := by
    ext x
    rw [h_deriv_f]
    -- deriv (6 * x - 18) = deriv (6 * x) - deriv 18
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- side-conditions
    exact differentiableAt_mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  -- finish
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

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
deriv f 6
deriv (deriv f) 6

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
  -- replace `f` by its defining λ‐abstraction
  subst hf

  -- compute the first derivative in one go
  have h1 : deriv f = fun x => 5*x^4 - 6*x^2 - 136*x + 216 := by
    ext x
    simp  -- uses all the deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_id, deriv_const, etc.

  -- compute the second derivative in one go
  have h2 : deriv (deriv f) = fun x => 20*x^3 - 12*x - 136 := by
    ext x
    rw [h1]
    simp

  -- now evaluate at x = 2
  constructor
  · simp [h1]  -- 5*2^4 - 6*2^2 - 136*2 + 216 = 0
  · simp [h2]  -- 20*2^3 - 12*2 - 136 = 0

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 6924 * x - 865 * x ^ 2) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) < 0) := by
  intro hf
  -- 1) compute f'
  have h1 : deriv f = fun x => 16 * x ^ 3 - 1730 * x - 6924 := by
    ext x
    simp [hf]
  -- 2) compute f''
  have h2 : deriv (deriv f) = fun x => 48 * x ^ 2 - 1730 := by
    ext x
    simp [h1]
  -- 3) evaluate at x = -6
  constructor
  · simp [h1]
  · simp [h2]; norm_num

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
  intro hf
  -- first derivative
  have h1 : deriv f = fun x => 6*x^5 - 10*x^4 + 4*x^3 - 15*x^2 - 3710*x - 8619 := by
    ext x
    simp [hf]
  -- second derivative
  have h2 : deriv (deriv f) = fun x => 30*x^4 - 40*x^3 + 12*x^2 - 30*x - 3710 := by
    ext x
    simp [h1]
  -- evaluate at x = -3
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 4 * x ^ 5 - 23752 * x ^ 2 + 187520 * x) → (deriv f (5:ℝ) = 0 ∧ deriv (deriv f) (5:ℝ) < 0) := by
f = fun x : ℝ => 2*x^6 + 4*x^5 - 23752*x^2 + 187520*x

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 2 - 24 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) > 0) := by
  intro hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 6 * x - 24 := by
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
    -- prove differentiability of each piece
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability again
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- now check at x = 4
  constructor
  -- deriv f 4 = 0
  nth_rewrite 1 [h_deriv_f]
  ring
  -- deriv (deriv f) 4 > 0
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 + 4 * x ^ 5 - 28080 * x ^ 2 + 264384 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) = 0) := by
  -- substitute the definition of f
  subst hf

  -- compute the first derivative
  have h1 : deriv (fun x => x^6 + 4*x^5 - 28080*x^2 + 264384*x) =
             fun x =>  6*x^5 + 20*x^4 - 56160*x + 264384 :=
  by
    ext x
    simp [deriv_pow, deriv_mul, deriv_add, deriv_sub, deriv_const]

  -- compute the second derivative
  have h2 : deriv (fun x => 6*x^5 + 20*x^4 - 56160*x + 264384) =
             fun x =>  30*x^4 +  80*x^3 - 56160 :=
  by
    ext x
    simp [deriv_pow, deriv_mul, deriv_add, deriv_sub, deriv_const]

  -- put it all together and evaluation at x=6
  simpa [h1, h2] using by norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 4 + 4 * x ^ 3 - 576 * x ^ 2 - 4752 * x) → (deriv f (-6:ℝ) = 0 ∧ deriv (deriv f) (-6:ℝ) = 0) := by
  -- replace `f` by its defining λ‐term
  subst hf
  -- `simp` knows all the derivative‐of‐pow/mul/add lemmas and does the arithmetic
  simp [deriv]

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 4 - 3 * x ^ 3 - 351 * x ^ 2 + 1928 * x) → (deriv f (4:ℝ) = 0 ∧ deriv (deriv f) (4:ℝ) < 0) := by
  -- compute f'
  have h_deriv_f : deriv f = fun x => 16 * x^3 - 9 * x^2 - 702 * x + 1928 := by
    ext x
    -- substitute the definition of f and simplify all derivatives
    rw [hf]
    simp
  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 48 * x^2 - 18 * x - 702 := by
    ext x
    -- substitute the previous result and simplify
    rw [h_deriv_f]
    simp
  -- now check at x = 4
  constructor
  · -- deriv f 4 = 0
    rw [h_deriv_f]; norm_num
  · -- deriv (deriv f) 4 < 0
    rw [h_deriv_deriv_f]; norm_num

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
  -- replace f by the explicit polynomial
  intro hf'
  rw [hf']  
  -- now f is literally fun x => …, and `simp` knows all the `deriv_*` lemmas
  constructor
  · simp; norm_num
  · simp; norm_num

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
  intro hf

  -- 1) compute deriv f
  have h_deriv_f : deriv f = fun x => 2 * x + 4 := by
    ext x
    -- rewrite the definition of f
    rw [hf]
    -- derivative of x^2 + 4*x
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_pow'']  -- deriv (x^2)
    nth_rewrite 1 [deriv_id'']   -- deriv x
    nth_rewrite 1 [deriv_mul]    -- deriv (4 * x)
    nth_rewrite 1 [deriv_const]  -- deriv 4
    ring
    -- provide differentiability facts
    all_goals
      try exact differentiableAt_pow _
      try exact differentiableAt_id
      try exact differentiableAt_const _

  -- 2) compute deriv (deriv f)
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    -- rewrite the formula for deriv f
    rw [h_deriv_f]
    -- deriv (2*x + 4) = 2
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    ring
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_const _

  -- 3) split the conjunction and finish
  constructor
  · -- deriv f (-2) = 2*(-2) + 4 = 0
    nth_rewrite 1 [h_deriv_f]; ring
  · -- deriv (deriv f) (-2) = 2 > 0
    nth_rewrite 1 [h_deriv_deriv_f]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 6 - 24576 * x - 3840 * x ^ 2) → (deriv f (-4:ℝ) = 0 ∧ deriv (deriv f) (-4:ℝ) = 0) := by
  -- compute the first derivative
  have h1 : deriv f = fun x => 6 * x^5 - 24576 - 7680 * x := by
    ext x
    -- replace f with the concrete λ‐term and simplify all derivs
    rw [hf]
    simp [deriv_pow, deriv_mul, deriv_const, deriv_sub, deriv_id]
    ring

  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 30 * x^4 - 7680 := by
    ext x
    -- replace deriv f by the concrete λ‐term we just found
    rw [h1]
    simp [deriv_mul, deriv_const, deriv_pow, deriv_sub, deriv_id]
    ring

  -- now evaluate at x = -4
  constructor
  · simp [h1]; norm_num   -- deriv f (-4) = 0
  · simp [h2]; norm_num   -- deriv (deriv f) (-4) = 0

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 4 + x ^ 3 - 97 * x ^ 2 - 393 * x) → (deriv f (-3:ℝ) = 0 ∧ deriv (deriv f) (-3:ℝ) > 0) := by
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 8 * x^3 + 3 * x^2 - 194 * x - 393 := by
    ext x
    -- unfold f
    rw [hf]
    -- derivative of 2*x^4 + x^3 - 97*x^2 - 393*x
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
    nth_rewrite 1 [deriv_id'']
    ring
    -- the various differentiability proofs
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 24 * x^2 + 6 * x - 194 := by
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
    ring
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- now check at x = -3
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; ring; norm_num

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
  -- compute f'
  have h_deriv_f : deriv f = fun x => 2 * x + 4 := by
    ext x
    -- unfold f
    rw [hf]
    -- deriv (x^2 + 4*x) = deriv x^2 + deriv (4*x)
    nth_rewrite 1 [deriv_add]
    -- deriv x^2 = 2*x
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- deriv (4*x) = 4 * 1
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- side‐conditions: differentiability
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
  -- compute f''
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 2 := by
    ext x
    rw [h_deriv_f]
    -- deriv (2*x + 4) = deriv (2*x) + deriv 4
    nth_rewrite 1 [deriv_add]
    -- deriv (2*x) = 2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- deriv 4 = 0
    nth_rewrite 1 [deriv_const]
    ring
    -- side‐conditions
    exact differentiableAt_const _
    exact differentiableAt_id
  -- finish
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 6 + 3 * x ^ 4 - 3 * x ^ 3 - 39471 * x ^ 2 + 378072 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
@[simp] lemma deriv_add  {E : Type*} [normed_field E] {f g : E → E} :
  deriv (fun x => f x + g x) = fun x => deriv f x + deriv g x
-- and similar simp‐lemmas for deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id, …

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
  intro hf

  -- compute the first derivative
  have h_deriv_f : deriv f = fun x => 9 * x ^ 2 + 88 * x + 215 := by
    ext x
    rw [hf]
    -- (3 * x^3)' + (44 * x^2)' + (215 * x)'
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- derive 3 * x^3
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- derive 44 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- derive 215 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- now discharge all `differentiableAt` obligations
    all_goals
      repeat
        solve_by_elim
          [ differentiableAt_const
          , differentiableAt_id
          , differentiableAt_pow
          , DifferentiableAt.mul
          ]

  -- compute the second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 18 * x + 88 := by
    ext x
    rw [h_deriv_f]
    -- (9 * x^2)' + (88 * x)' + (215)'
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- derive 9 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- derive 88 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- derive constant 215
    nth_rewrite 1 [deriv_const]
    ring
    -- again discharge `differentiableAt`
    all_goals
      repeat
        solve_by_elim
          [ differentiableAt_const
          , differentiableAt_id
          , differentiableAt_pow
          , DifferentiableAt.mul
          ]

  -- now prove the concrete numerical facts
  constructor
  · -- f'(-5) = 0
    nth_rewrite 1 [h_deriv_f]
    ring
  · -- f''(-5) < 0
    nth_rewrite 1 [h_deriv_deriv_f]
    ring
    norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2 - 16 * x) → (deriv f (-2:ℝ) = 0 ∧ deriv (deriv f) (-2:ℝ) < 0) := by
  intros hf

  -- first derivative
  have h_deriv_f : deriv f = fun x => 4 * x ^ 3 + 15 * x ^ 2 + 6 * x - 16 := by
    ext x
    -- expand f and apply the usual derivative rules
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
    ring
    -- differentiability side‐goals
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)

  -- second derivative
  have h_deriv_deriv_f : deriv (deriv f) = fun x => 12 * x ^ 2 + 30 * x + 6 := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_const]
    ring
    -- differentiability side‐goals
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  -- conclude at x = -2
  constructor
  · nth_rewrite 1 [h_deriv_f] ; ring
  · nth_rewrite 1 [h_deriv_deriv_f] ; ring ; norm_num

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
  -- the `simp` fires all the `deriv_pow`, `deriv_mul`, `deriv_const`,…
  simp [hf]
  -- now there are just two concrete real arithmetic goals
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  2 * x ^ 2 - 24 * x) → (deriv f (6:ℝ) = 0 ∧ deriv (deriv f) (6:ℝ) > 0) := by
  intros hf

  -- compute the first derivative: f' x = 4*x - 24
  have h_deriv_f : deriv f = fun x => 4 * x - 24 := by
    ext x
    rw [hf]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]    -- deriv (2 * x^2)
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]    -- deriv (24 * x)
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- differentiability side-conditions
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_id

  -- compute the second derivative: f'' x = 4
  have h_deriv_deriv_f : deriv (deriv f) = fun x => (4 : ℝ) := by
    ext x
    rw [h_deriv_f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_mul]    -- deriv (4 * x)
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]  -- deriv 24
    ring
    -- differentiability side-conditions
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_const _

  -- conclude at x = 6
  constructor
  · nth_rewrite 1 [h_deriv_f]; ring
  · nth_rewrite 1 [h_deriv_deriv_f]; norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  4 * x ^ 5 - x ^ 4 - 4 * x ^ 3 + 31 * x ^ 2 + 50 * x) → (deriv f (-1:ℝ) = 0 ∧ deriv (deriv f) (-1:ℝ) < 0) := by
  -- first compute f'
  have h1 : deriv f = fun x ↦ 20*x^4 - 4*x^3 - 12*x^2 + 62*x + 50 := by
    ext x
    simp [hf]
  -- then compute f''
  have h2 : deriv (deriv f) = fun x ↦ 80*x^3 - 12*x^2 - 24*x + 62 := by
    ext x
    simp [h1]
  -- now plug in x = -1
  simp [h1, h2]
  norm_num

example (f:ℝ→ℝ) : (f = fun x:ℝ =>  3 * x ^ 3 + 45 * x ^ 2 + 225 * x) → (deriv f (-5:ℝ) = 0 ∧ deriv (deriv f) (-5:ℝ) = 0) := by
  -- compute the first derivative
  have h1 : deriv f = fun x => 9 * x ^ 2 + 90 * x + 225 := by
    ext x
    simp [hf]
  -- compute the second derivative
  have h2 : deriv (deriv f) = fun x => 18 * x + 90 := by
    ext x
    simp [h1]
  -- finish by evaluating at x = -5
  constructor
  · simp [h1]; norm_num
  · simp [h2]; norm_num

