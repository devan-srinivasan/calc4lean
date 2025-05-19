import Mathlib
open Real

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 3 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  -- abbreviate f and the domain
  let f := λ x => 17 * x ^ 7 + 3 * x ^ 2
  let D := Icc (0:ℝ) 3

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0:ℝ) 3

  -- the derivative is strictly positive on the interior (0,3)
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    dsimp [f]
    -- compute deriv f x = 17*7*x^6 + 3*2*x = 119*x^6 + 6*x
    have deriv_eq : deriv f x = 119 * x ^ 6 + 6 * x := by
      simp [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
      ring
    rw [deriv_eq]
    -- both terms are > 0 because x > 0
    have h1 : 0 < 119 * x ^ 6 := by
      apply mul_pos (by norm_num) (pow_pos hx.1)
    have h2 : 0 < 6 * x := by
      apply mul_pos (by norm_num) hx.1
    linarith

  -- f is continuous on D (it is a polynomial)
  have hf : ContinuousOn f D := by
    dsimp [f]
    continuity

  -- strict monotonicity on a convex set follows from derivative > 0
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 13 * x ^ 6 + 8 * x ^ 5 + 19 * x ^ 4 + 15 * x ^ 3 + 8 * x ^ 2 + 19 * x + 5) (Icc (0: ℝ) (1: ℝ)) := by
  let f := fun x : ℝ => 5*x^7 + 13*x^6 + 8*x^5 + 19*x^4 + 15*x^3 + 8*x^2 + 19*x + 5
  let D := Icc (0 : ℝ) 1

  -- D is convex:
  have hconv : Convex ℝ D := convex_Icc (0 : ℝ) 1

  -- f is continuous on D:
  have hcont : ContinuousOn f D := by continuity

  -- compute the derivative and show it is strictly positive on the interior
  have hpos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- simp out the derivative
    have : deriv f x = 35*x^6 + 78*x^5 + 40*x^4 + 76*x^3 + 45*x^2 + 16*x + 19 := by
      simp [f, deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    -- reduce to a sum of positive terms
    simp only [this]
    -- each x^k > 0 because 0 < x (interior D = (0,1))
    have pow_pos : ∀ k : ℕ, 0 < x ^ k := fun _ => pow_pos hx.1
    -- now the sum is strictly positive
    linarith [pow_pos 6, pow_pos 5, pow_pos 4, pow_pos 3, pow_pos 2, pow_pos 1]

  -- finish by the standard strict-mono‐on‐of-deriv-pos theorem
  exact (strictMonoOn_of_deriv_pos hconv hcont hpos).monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 8 * x ^ 6 + 4 * x ^ 5 + 16 * x ^ 4 + 12 * x ^ 2 + 20
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 20 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 112 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 9 * x ^ 3 + 12 * x ^ 2 + 2 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 4 + 19 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 4 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 4 + 19 * x ^ 3 + 4 * x ^ 2
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 57 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 25 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 2 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 20 * x ^ 7 + 2 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 19 * x + 12
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 19 := by linarith [hx.1]
    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 8 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 140 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 18 * x ^ 6 + 5 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  -- abbreviate the function and domain
  let f := λ x:ℝ, 12*x^7 + 18*x^6 + 5*x^5 + 20*x^2
  let D := Icc (0:ℝ) 10

  -- the domain is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    dsimp [f]; continuity

  -- the derivative is strictly positive on the interior of D
  have hder_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- compute the derivative
    have : deriv f x = 84*x^6 + 108*x^5 + 25*x^4 + 40*x := by
      simp [deriv_add, deriv_mul, deriv_pow]
    rw [this]; clear this

    -- unwrap the interior and show positivity
    rw [interior_Icc] at hx
    have h0 : 0 < x := hx.1
    have p6 : 0 < x ^ 6 := pow_pos h0 _
    have p5 : 0 < x ^ 5 := pow_pos h0 _
    have p4 : 0 < x ^ 4 := pow_pos h0 _
    have p1 : 0 < x     := h0

    -- combine to conclude strict positivity
    linarith

  -- conclude monotonicity from strict positivity of the derivative
  exact (strictMonoOn_of_deriv_pos hD hcont hder_pos).monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 18 * x ^ 6 + 2 * x ^ 5 + 17 * x ^ 3 + 7 * x) (Icc (0: ℝ) (4: ℝ)) := by
  let f := fun x : ℝ => 11 * x ^ 7 + 18 * x ^ 6 + 2 * x ^ 5 + 17 * x ^ 3 + 7 * x
  let D := Icc (0 : ℝ) 4

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 4

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    dsimp [f]; continuity

  -- the derivative is strictly positive on the interior of D
  have hder : ∀ x (hx : x ∈ interior D), 0 < deriv f x := by
    intro x hx
    -- unfold f and compute deriv f x
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const] 
      -- now the goal is of the form deriv f x = _; we finish by `ring`
    ring
    -- rewrite to expose the explicit polynomial
    -- `deriv f x = 77*x^6 + 108*x^5 + 10*x^4 + 51*x^2 + 7`
    -- and now show that this is > 0 when 0 < x < 4
    let eqn := by
      dsimp [f]; simp [deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const]; ring
    rw [eqn]
    -- interior_Icc tells us 0 < x < 4
    have ⟨hx0, _hx4⟩ := (interior_Icc _ _).1 hx
    -- all monomials are strictly positive
    have p6 : 0 < x ^ 6 := pow_pos hx0 6
    have p5 : 0 < x ^ 5 := pow_pos hx0 5
    have p4 : 0 < x ^ 4 := pow_pos hx0 4
    have p2 : 0 < x ^ 2 := pow_pos hx0 2
    -- now finish by linarith, constants 77, 108, 10, 51, 7 are all > 0
    linarith

  -- assemble the strict monotonicity proof
  show MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 18 * x ^ 6 + 11 * x ^ 5 + 14 * x ^ 4 + 20 * x ^ 3 + 13 * x ^ 2 + 5 * x + 8) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 7 + 18 * x ^ 6 + 11 * x ^ 5 + 14 * x ^ 4
                      + 20 * x ^ 3 + 13 * x ^ 2 + 5 * x + 8
  let D := Icc (0 : ℝ) (10 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (0 : ℝ) (10 : ℝ)

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- expand deriv
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- now 70*x^6 + 108*x^5 + 55*x^4 + 56*x^3 + 60*x^2 + 26*x + 5 > 0
    rw [interior_Icc] at hx
    have p6 : 0 < x ^ 6 := by apply pow_pos; exact hx.1
    have p5 : 0 < x ^ 5 := by apply pow_pos; exact hx.1
    have p4 : 0 < x ^ 4 := by apply pow_pos; exact hx.1
    have p3 : 0 < x ^ 3 := by apply pow_pos; exact hx.1
    have p2 : 0 < x ^ 2 := by apply pow_pos; exact hx.1
    have h1 : 0 < 70  * x ^ 6 := by linarith [p6]
    have h2 : 0 < 108 * x ^ 5 := by linarith [p5]
    have h3 : 0 < 55  * x ^ 4 := by linarith [p4]
    have h4 : 0 < 56  * x ^ 3 := by linarith [p3]
    have h5 : 0 < 60  * x ^ 2 := by linarith [p2]
    have h6 : 0 < 26  * x     := by linarith [pow_pos (hx.1 : 0 < x)]
    have h7 : 0 < 5           := by norm_num
    linarith [h1, h2, h3, h4, h5, h6, h7]

    -- the differentiability chain
    exact differentiableAt_const _
    repeat
      (exact differentiableAt_id <|> exact differentiableAt_const _ <|>
       exact differentiableAt_pow _ <|>
       exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add
      (DifferentiableAt.add (DifferentiableAt.add
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
      (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))

  -- continuity on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.add
                   (Continuous.add
                     (Continuous.add
                       (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                       (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
                     (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
             (Continuous.mul continuous_const continuous_id)
           ).continuousOn

  -- conclude monotonicity
  apply strictMonoOn_of_deriv_pos hD hf hf'.monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 3 + 15 * x ^ 2 + 8 * x) (Icc (0: ℝ) (8: ℝ)) := by

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 15 * x ^ 6 + 9 * x ^ 4 + 8 * x ^ 2 + 17 * x + 15) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 15 * x ^ 6 + 9 * x ^ 4 + 8 * x ^ 2 + 17 * x + 15
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 17 := by linarith [hx.1]
    have h2: 0 < 16 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 36 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 8 * x ^ 5 + 15 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  -- abbreviate
  let f := fun x : ℝ => 8*x^6 + 8*x^5 + 15*x^2
  let D := Icc 0 6
  -- [0,6] is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- compute f' and show it is > 0 on the interior (0,6)
  have hderiv : ∀ x hx, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- simplify the 3-term sum of derivatives
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    -- now the goal is: 48*x^5 + 40*x^4 + 30*x > 0
    -- factor out x
    have fact : 48*x^5 + 40*x^4 + 30*x = x * (48*x^4 + 40*x^3 + 30) := by ring
    rw [fact]
    -- on the interior x>0
    have xpos : 0 < x := hx.1
    -- show 48*x^4 + 40*x^3 + 30 > 0
    have A : 0 < 48*x^4 := by
      apply mul_pos (by norm_num) (pow_pos xpos 4)
    have B : 0 ≤ 40*x^3 := by
      apply mul_nonneg (by norm_num) (pow_nonneg _ x.zero_le)
    have C : 0 < (30 : ℝ) := by norm_num
    have sumpos : 0 < 48*x^4 + 40*x^3 + 30 := by linarith [A, B, C]
    -- conclude
    exact mul_pos xpos sumpos
  -- f is continuous on [0,6]
  have hcont : ContinuousOn f D := by
    continuity
  -- now apply the standard theorem
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 6 * x ^ 2 + 5 * x + 4) (Icc (0: ℝ) (10: ℝ)) := by
  -- abbreviate the function and the domain
  let f := λ x => 12 * x ^ 6 + 6 * x ^ 2 + 5 * x + 4
  let D := Icc (0 : ℝ) (10 : ℝ)

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x
    simp [f, deriv_add, deriv_mul, deriv_pow, deriv_const] at *
    -- deriv f x = 72 * x ^ 5 + 12 * x + 5
    -- each term is positive on (0, 10)
    have h1 : 0 < 72 * x ^ 5 := by linarith [pow_pos hx.1]
    have h2 : 0 < 12 * x     := by linarith [hx.1]
    have h3 : 0 < (5 : ℝ)     := by norm_num
    linarith [h1, h2, h3]

  -- f is continuous (it's a polynomial)
  have cont_f : Continuous f := by continuity
  have hf  : ContinuousOn f D := cont_f.continuousOn

  -- conclude monotonicity via the strict‐mono‐on‐of‐deriv‐pos lemma
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 11 * x ^ 6 + 2 * x ^ 4 + 19 * x ^ 2) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 11 * x ^ 6 + 2 * x ^ 4 + 19 * x ^ 2
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 38 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 8 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 66 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 112 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 7 * x ^ 6 + 13 * x ^ 5 + 13 * x ^ 3) (Icc (0: ℝ) (2: ℝ)) := by

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 3 * x ^ 6 + 17 * x ^ 4 + 13 * x ^ 3 + 2 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ => 6 * x ^ 7 + 3 * x ^ 6 + 17 * x ^ 4 + 13 * x ^ 3 + 2 * x ^ 2 + 18 * x + 13
  let D := Icc (0 : ℝ) (2 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (2 : ℝ)

  -- deriv f x = 42*x^6 + 18*x^5 + 68*x^3 + 39*x^2 + 4*x + 18, and this is positive on (0,2)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x
    unfold f
    -- apply the usual deriv rules
    repeat
      (nth_rewrite 1 [deriv_add] ;
       nth_rewrite 1 [deriv_mul] ;
       nth_rewrite 1 [deriv_const] ;
       nth_rewrite 1 [deriv_pow''] ;
       nth_rewrite 1 [deriv_id''])
    ring
    -- now derive positivity
    rwa [interior_Icc] at hx
    have h0 : 0 < x := hx.1
    -- each monomial coefficient · x^n is positive
    have h1 : 0 < 42 * x ^ 6 := by linarith [pow_pos h0 (Nat.succ_pos 5)]
    have h2 : 0 < 18 * x ^ 5 := by linarith [pow_pos h0 (Nat.succ_pos 4)]
    have h3 : 0 < 68 * x ^ 3 := by linarith [pow_pos h0 (Nat.succ_pos 2)]
    have h4 : 0 < 39 * x ^ 2 := by linarith [pow_pos h0 (Nat.succ_pos 1)]
    have h5 : 0 < 4  * x     := by linarith [pow_pos h0 (Nat.succ_pos 0)]
    have h6 : 0 < 18        := by norm_num
    linarith [h1, h2, h3, h4, h5, h6]

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.add
              (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
              (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
            (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
          (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
        (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
      (Continuous.add
        (Continuous.mul continuous_const continuous_id)
        continuous_const)).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 3 + 11 * x + 4) (Icc (0: ℝ) (6: ℝ)) := by
  let f := fun x => 2 * x^3 + 11 * x + 4
  let D := Icc (0:ℝ) 6
  -- convexity of the interval
  have hD : Convex ℝ D := convex_Icc 0 6
  -- compute the derivative
  have hder : ∀ x ∈ interior D, deriv f x = 6 * x^2 + 11 := by
    intro x hx
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]
  -- strictly positive on the interior (0 < x < 6)
  have hpos : ∀ x ∈ interior D, deriv f x > 0 := by
    intro x hx
    rw [hder x hx]
    -- 6*x^2 > 0 since x>0, and 11>0
    have h1 : 0 < 6 * x^2 := by
      apply mul_pos; norm_num; apply pow_pos; exact hx.1
    have h2 : 0 < (11 : ℝ) := by norm_num
    linarith
  -- continuity of f on D by the `continuity` tactic
  have hf : ContinuousOn f D := by continuity
  -- finish
  exact (strictMonoOn_of_deriv_pos hD hf hpos).monotoneOn

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 14 * x ^ 3 + 2 * x ^ 2 + 18 * x + 19) (Icc (0: ℝ) (10: ℝ)) := by
f x = 14*x^7 + 3*x^5 + 6*x^4 + 14*x^3 + 2*x^2 + 18*x + 19

example: MonotoneOn (λ x ↦ 9 * x ^ 4 + 3 * x ^ 2 + 19 * x + 12) (Icc (0: ℝ) (5: ℝ)) := by
  -- let f be our polynomial
  let f := fun x => 9 * x^4 + 3 * x^2 + 19 * x + 12
  let D := Icc (0 : ℝ) 5

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 5

  -- f is continuous on D
  have hf : ContinuousOn f D := by continuity

  -- compute the derivative once and for all
  have hderiv : ∀ x, deriv f x = 36 * x^3 + 6 * x + 19 := by
    intro x
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]

  -- show the derivative is strictly positive on the interior of D
  have hpos : ∀ x ∈ interior D, 0 < deriv f x := by
    rintro x ⟨hx, hx'⟩
    -- plug in our formula for deriv f x
    simp [hderiv x, interior_Icc] at hx'
    -- now x ≥ 0, so x^3 ≥ 0, hence 36*x^3 ≥ 0, and 6*x ≥ 0, so the sum +19 > 0
    nlinarith [pow_nonneg (le_of_lt hx'), mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hx')),
               mul_nonneg (by norm_num) (le_of_lt hx')]

  -- conclude by the standard theorem
  apply (strictMonoOn_of_deriv_pos hD hf hpos).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 14 * x ^ 6 + 3 * x ^ 3 + 20 * x ^ 2 + 13 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 7 + 14 * x ^ 6 + 3 * x ^ 3 + 20 * x ^ 2 + 13 * x
  let D := Icc (0: ℝ) (5: ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0: ℝ) (5: ℝ)

  -- On the interior of D, the derivative is strictly positive
  have hf' : ∀ x h : x ∈ interior D, 0 < deriv f x := by
    intro x hx
    unfold f
    -- compute deriv termwise
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
    ring
    -- now show each summand > 0
    rw [interior_Icc] at hx
    have h1 : 0 < 13 := by linarith
    have h2 : 0 < 40 * x ^ 1 := by
      have p : 0 < x ^ 1 := pow_pos hx.1
      linarith [p]
    have h3 : 0 < 9 * x ^ 2 := by
      have p : 0 < x ^ 2 := pow_pos hx.1
      linarith [p]
    have h4 : 0 < 84 * x ^ 5 := by
      have p : 0 < x ^ 5 := pow_pos hx.1
      linarith [p]
    have h5 : 0 < 14 * x ^ 6 := by
      have p : 0 < x ^ 6 := pow_pos hx.1
      linarith [p]
    linarith [h1, h2, h3, h4, h5]

    -- and justify the steps computing deriv
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact DifferentiableAt.add _ _

  -- f is continuous on D (sum of continuous terms)
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.add (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                         (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
        (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
      (Continuous.add
        (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
        (Continuous.mul continuous_const continuous_id))
    ).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 2 + 6) (Icc (0: ℝ) (4: ℝ)) := by
  -- define f and the domain D
  let f : ℝ → ℝ := λ x ↦ 15 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 2 + 6
  let D := Icc (0 : ℝ) (4 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (4 : ℝ)

  -- on the interior of D, the derivative of f is strictly positive
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    -- after simplification we get
    -- deriv f x = 105 * x ^ 6 + 20 * x ^ 4 + 18 * x
    ring_nf
    -- interior D = {x | 0 < x ∧ x < 4}, so in particular x > 0
    rw [interior_Icc] at hx
    -- show each term is positive
    have h1 : 0 < 105 * x ^ 6 := by
      apply mul_pos (by norm_num) (pow_pos hx.1 sixPos).2
    have h2 : 0 < 20 * x ^ 4 := by
      apply mul_pos (by norm_num) (pow_pos hx.1 fourPos).2
    have h3 : 0 < 18 * x := by
      apply mul_pos (by norm_num) hx.1
    -- conclude positivity of the sum
    linarith

  -- f is continuous on D (being a polynomial)
  have hcont : ContinuousOn f D := by
    simp [f]
    apply ( Continuous.add
              (Continuous.add
                (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                (Continuous.mul continuous_const (Continuous.pow continuous_id 5))
              )
              (Continuous.add
                (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
                continuous_const
              )
            ).continuousOn

  -- conclude strict monotonicity hence monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 6 * x ^ 2 + 12 * x + 4) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ => 15 * x ^ 6 + 6 * x ^ 2 + 12 * x + 4
  let D := Icc (0 : ℝ) (7 : ℝ)

  -- The domain is a convex set
  have hD : Convex ℝ D := by
    apply convex_Icc (0 : ℝ) (7 : ℝ)

  -- The derivative f' is strictly positive on the interior (0,7)
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    -- compute the derivative
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- 15 * x^6
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- 6 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- 12 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- + 4
    nth_rewrite 1 [deriv_const]
    ring
    -- now prove positivity on the open interval
    rw [interior_Icc] at hx  -- interior D = (0,7)
    have h_const : 0 < (12 : ℝ) := by linarith
    have h_lin   : 0 < 12 * x := by linarith [hx.1]
    have h_pow   : 0 < 90 * x ^ 5 := by
      have px : 0 < x ^ 5 := pow_pos hx.1
      linarith [px]
    linarith [h_const, h_lin, h_pow]
    -- provide the differentiability witnesses
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add
      (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
      (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add
      (DifferentiableAt.add
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)))
      (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _

  -- f is continuous on [0,7] since it is a polynomial
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.mul continuous_const (Continuous.pow continuous_id 6))
            (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
          (Continuous.mul continuous_const continuous_id))
        continuous_const)
      .continuousOn

  -- conclude monotonicity from strict positivity of the derivative
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 11 * x ^ 5 + 19 * x + 10) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 6 + 11 * x ^ 5 + 19 * x + 10
  let D := Icc (0 : ℝ) (6 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (6 : ℝ)

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    -- compute deriv (8*x^6 + 11*x^5 + 19*x + 10) x
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- deriv of each term
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
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
    -- now deriv f x = 48*x^5 + 55*x^4 + 19
    rw [interior_Icc] at hx
    have h1 : 0 < 48 * x ^ 5 := by
      have pp : 0 < x ^ 5 := pow_pos hx.1
      linarith [pp]
    have h2 : 0 < 55 * x ^ 4 := by
      have pp : 0 < x ^ 4 := pow_pos hx.1
      linarith [pp]
    have h3 : 0 < 19 := by linarith
    linarith [h1, h2, h3]
    -- side goals: differentiability at x
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
                              (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.add (‹_›) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact DifferentiableAt.add (‹_›) (differentiableAt_const _)

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 6))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 18 * x ^ 5 + 9 * x ^ 3 + 4 * x ^ 2 + 3 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 18 * x ^ 5 + 9 * x ^ 3 + 4 * x ^ 2 + 3 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 3 := by linarith [hx.1]
    have h1: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 90 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 19 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 18) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 19 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 18
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 114 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 11 * x ^ 5 + 17 * x ^ 4 + 5 * x ^ 3 + 18 * x ^ 2 + 13 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := fun x => 12*x^6 + 11*x^5 + 17*x^4 + 5*x^3 + 18*x^2 + 13*x
  let D := Icc (0 : ℝ) 1

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- f is continuous on D
  have hf : ContinuousOn f D := by continuity

  -- f' (x) > 0 on the interior (0,1)
  have hder : ∀ x ∈ interior D, deriv f x > 0 := by
    intro x hx
    -- compute the derivative in one go
    have deriv_eq :
      deriv f x = 72*x^5 + 55*x^4 + 68*x^3 + 15*x^2 + 36*x + 13 := by
      simp [f]; ring
    -- all the monomials for x > 0 are positive, and 13 > 0, so the sum is > 0
    simpa [deriv_eq] using by
      have xpos : 0 < x := hx.1
      -- all these follow from pow_pos
      have h5 : 0 < x^5 := pow_pos xpos
      have h4 : 0 < x^4 := pow_pos xpos
      have h3 : 0 < x^3 := pow_pos xpos
      have h2 : 0 < x^2 := pow_pos xpos
      -- now linarith sees that
      --   72*x^5 > 0, 55*x^4 > 0, 68*x^3 > 0, 15*x^2 > 0, 36*x > 0, 13 > 0
      linarith

  -- apply the standard fact that positive derivative on a convex set
  -- gives strict mono, hence mono
  exact (strictMonoOn_of_deriv_pos hD hf hder).monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 7 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 4 + 9 * x ^ 2 + 16 * x) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 7 + 7 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 4 + 9 * x ^ 2 + 16 * x
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h0: 0 < 16 := by linarith [hx.1]
    have h1: 0 < 18 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 36 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 85 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 105 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 6 + 4 * x ^ 5 + 20 * x ^ 4 + 11 * x ^ 3 + 2 * x ^ 2 + 9 * x + 7) (Icc (0: ℝ) (3: ℝ)) := by
  -- set up
  let f := fun x => 18*x^6 + 4*x^5 + 20*x^4 + 11*x^3 + 2*x^2 + 9*x + 7
  let D := Icc (0:ℝ) 3
  have hD : Convex ℝ D := convex_Icc (0:ℝ) 3

  -- compute the derivative
  have hderiv : ∀ x ∈ interior D, deriv f x = 108*x^5 + 20*x^4 + 80*x^3 + 33*x^2 + 4*x + 9 := by
    intro x hx
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow]  -- uses deriv_pow for x^n
    ring

  -- show the derivative is strictly positive on (0,3)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    rw [hderiv x hx]
    -- each term is ≥ 0 and at least the constant term 9 > 0
    nlinarith [pow_pos hx.1]

  -- f is a polynomial, hence continuous
  have hf : Continuous f := by continuity
  have hf_on : ContinuousOn f D := hf.continuousOn

  -- conclude strict monotonicity on the closed interval
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf_on hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 10 * x ^ 6 + 20 * x ^ 5 + 8 * x ^ 3 + 15 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
  -- abbreviate
  let f := λ x : ℝ => 4*x^7 + 10*x^6 + 20*x^5 + 8*x^3 + 15*x^2 + 19*x
  let D := Icc (0:ℝ) 3

  -- the domain is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute the derivative and show it is > 0 on the interior
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- first compute deriv f x
    have : deriv f x = 28*x^6 + 60*x^5 + 100*x^4 + 24*x^2 + 30*x + 19 := by
      dsimp [f]
      simp only
        [ deriv_add, deriv_mul, deriv_pow'', deriv_const, deriv_id'' ]
      ring
    -- rewrite to get the closed form
    rw [this]
    -- now interior (Icc 0 3) = {x | 0 < x ∧ x < 3}
    rw [interior_Icc] at hx
    -- all terms 28*x^6, 60*x^5, …, 19 are ≥ 19 since x > 0,
    -- so the sum is strictly positive
    linarith [pow_pos hx.1 6, pow_pos hx.1 5, pow_pos hx.1 4, pow_pos hx.1 2, hx.1]

  -- f is continuous on the closed interval
  have hcont : ContinuousOn f D := by
    continuity

  -- apply the standard theorem
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 17 * x ^ 6 + 10 * x ^ 2 + 12 * x + 13) (Icc (0: ℝ) (3: ℝ)) := by
  let f : ℝ → ℝ := λ x => 8 * x ^ 7 + 17 * x ^ 6 + 10 * x ^ 2 + 12 * x + 13
  let D := Icc (0 : ℝ) 3
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 3
  -- f is a polynomial, hence continuous on D
  have hf : ContinuousOn f D := by
    -- `continuity` knows that polynomial expressions are continuous
    continuity
  -- compute f′ and show it is strictly positive on interior D = (0,3)
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- unfold all the little deriv lemmas and simplify
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring_nf  -- now `deriv f x = 56*x^6 + 102*x^5 + 20*x + 12`
    -- interior D = {x | 0 < x ∧ x < 3}
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    -- each term of 56*x^6 + 102*x^5 + 20*x + 12 is positive
    have h1 : 0 < 56 * x ^ 6 := by
      have p := pow_pos hx0 6
      linarith
    have h2 : 0 < 102 * x ^ 5 := by
      have p := pow_pos hx0 5
      linarith
    have h3 : 0 < 20 * x := by linarith [hx0]
    have h4 : 0 < 12 := by linarith
    -- sum of positives is positive
    linarith [h1, h2, h3, h4]
  -- conclude strict monotonicity ⇒ monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hder).monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 8 * x + 14) (Icc (0: ℝ) (7: ℝ)) := by
example : MonotoneOn (λ x => 11 * x ^ 7 + 8 * x + 14) (Icc (0 : ℝ) 7)

example: MonotoneOn (λ x ↦ 6 * x ^ 4 + 20 * x ^ 3 + 5 * x ^ 2 + 19 * x) (Icc (0: ℝ) (3: ℝ)) := by
def f (x : ℝ) := 6*x^4 + 20*x^3 + 5*x^2 + 19*x
def D : Set ℝ := Icc (0:ℝ) 3

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 15 * x ^ 6 + 8 * x ^ 5 + 2 * x ^ 4 + 7 * x ^ 2 + 18 * x + 13) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x => 17*x^7 + 15*x^6 + 8*x^5 + 2*x^4 + 7*x^2 + 18*x + 13
  let D := Icc 0 4

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 4

  -- compute f' and show it's positive on interior D = (0,4)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold and simplify the derivative
    simp [f,
      deriv_add, deriv_mul, deriv_const, deriv_pow''] at *
    -- now the goal is
    --   0 < 119*x^6 + 90*x^5 + 40*x^4 + 8*x^3 + 14*x + 18
    ring
    -- all coefficients and powers of x>0 on (0,4) are strictly positive
    nlinarith [pow_pos (by simpa [interior_Icc] using hx).1]

  -- f is continuous on D
  have hf : ContinuousOn f D := by continuity

  -- conclude monotonicity from positivity of the derivative
  apply (strictMonoOn_of_deriv_pos hD hf hf').MonotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 7 + 7 * x ^ 5 + 19 * x ^ 3 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by

example: MonotoneOn (λ x ↦ 8 * x ^ 4 + 15 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 4 + 15 * x ^ 2 + 18 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    have h0: 0 < 18 := by linarith [hx.1]
    have h1: 0 < 30 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 32 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 6 + 14 * x ^ 5 + 14 * x ^ 4) (Icc (0: ℝ) (5: ℝ)) := by
  let f := fun x => 3*x^6 + 14*x^5 + 14*x^4
  let D := Icc 0 5
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 5
  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- each monomial is continuous
    simp [f]; continuity
  -- the derivative is positive on the interior of D
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    -- unfold f and fire the deriv‐simp lemmas
    simp [f, deriv_add, deriv_mul_const, deriv_pow, deriv_id]
    -- now `deriv f x = 3*6*x^5 + 14*5*x^4 + 14*4*x^3`,
    -- which simplifies to `18*x^5 + 70*x^4 + 56*x^3`
    simp only [mul_comm]  at *
    -- on `interior_Icc.1 hx` we have `0 < x`
    have hx0 : 0 < x := (interior_Icc.1 hx).1
    -- each power is strictly positive
    have p3 : 0 < x^3 := pow_pos hx0
    have p4 : 0 < x^4 := pow_pos hx0
    have p5 : 0 < x^5 := pow_pos hx0
    -- now a linear combination of strictly positive terms is > 0
    linarith
  -- conclude monotonicity from the strict‐derivative criterion
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 6 * x ^ 5 + 3 * x ^ 4 + 6 * x ^ 3 + 16 * x + 14) (Icc (0: ℝ) (4: ℝ)) := by
  let f := λ x : ℝ ↦ 19 * x ^ 7 + 6 * x ^ 5 + 3 * x ^ 4 + 6 * x ^ 3 + 16 * x + 14
  let D := Icc (0: ℝ) (4: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (4: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 16 := by linarith [hx.1]
    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 12 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 30 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 133 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 15 * x ^ 6 + 20 * x ^ 5 + 17 * x ^ 4 + 4 * x ^ 2) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 15 * x ^ 6 + 20 * x ^ 5 + 17 * x ^ 4 + 4 * x ^ 2
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 100 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 84 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 5 + 3 * x ^ 3 + 6 * x ^ 2 + 17 * x + 6) (Icc (0: ℝ) (1: ℝ)) := by
  let f := fun x : ℝ ↦ 10*x^5 + 3*x^3 + 6*x^2 + 17*x + 6
  let D := Icc (0 : ℝ) (1 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- the derivative is strictly positive on the interior
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold the definition and compute deriv f x
    unfold f
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_id'', deriv_const]
    ring
    -- now f' x = 50*x^4 + 9*x^2 + 12*x + 17
    -- each term is nonnegative and at least one is strictly positive
    -- in fact all four are strictly > 0 when 0 < x < 1 (and 17 > 0 unconditionally)
    have h1 : 0 < 50 * x^4 := by
      apply mul_pos (by norm_num : 0 < 50) (pow_pos hx.1 4)
    have h2 : 0 < 9 * x^2 := by
      apply mul_pos (by norm_num : 0 < 9) (pow_pos hx.1 2)
    have h3 : 0 < 12 * x := by
      apply mul_pos (by norm_num : 0 < 12) hx.1
    have h4 : 0 < 17 := by norm_num
    linarith [h1, h2, h3, h4]
  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- one can just invoke the continuity tactic here
    continuity
  -- now conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 5 + 17 * x ^ 4 + 9 * x ^ 3 + 12 * x + 18) (Icc (0: ℝ) (5: ℝ)) := by
  let f := fun x : ℝ => 20 * x ^ 7 + 11 * x ^ 5 + 17 * x ^ 4 + 9 * x ^ 3 + 12 * x + 18
  let D := Icc (0 : ℝ) 5
  have hD : Convex ℝ D := convex_Icc 0 5

  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x in one step
    have hder : deriv f x =
        140 * x ^ 6 + 55 * x ^ 4 + 68 * x ^ 3 + 27 * x ^ 2 + 12 := by
      unfold f
      simp [deriv_add, deriv_mul, deriv_pow'', deriv_id'', deriv_const]
      ring
    -- rewrite and show each term is strictly positive on (0,5)
    rw [hder]
    have A : 0 < 140 * x ^ 6 := mul_pos (by decide) (pow_pos hx.1 6)
    have B : 0 < 55  * x ^ 4 := mul_pos (by decide) (pow_pos hx.1 4)
    have C : 0 < 68  * x ^ 3 := mul_pos (by decide) (pow_pos hx.1 3)
    have Dm: 0 < 27  * x ^ 2 := mul_pos (by decide) (pow_pos hx.1 2)
    have E : 0 < 12 := by decide
    linarith

  -- continuity of a polynomial is trivial by `continuity`
  have cf : Continuous f := by continuity
  have hf : ContinuousOn f D := cf.continuousOn

  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 9 * x ^ 6 + 3 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 18 * x) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ, 12 * x ^ 7 + 9 * x ^ 6 + 3 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 18 * x
  let D := Icc (0 : ℝ) 6

  -- the domain is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 6

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x h : x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- expand the derivative
    unfold f
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]
    ring
    -- now deriv f x = 84*x^6 + 54*x^5 + 12*x^3 + 24*x^2 + 24*x + 18
    -- in the interior x ∈ (0,6), so x > 0
    rw [interior_Icc] at hx
    let hpos : 0 < x := hx.1
    have p1 : 0 < 84 * x ^ 6 := by simpa using mul_pos (by norm_num : 0 < (84 : ℝ)) (pow_pos hpos 6)
    have p2 : 0 < 54 * x ^ 5 := by simpa using mul_pos (by norm_num : 0 < (54 : ℝ)) (pow_pos hpos 5)
    have p3 : 0 < 12 * x ^ 3 := by simpa using mul_pos (by norm_num : 0 < (12 : ℝ)) (pow_pos hpos 3)
    have p4 : 0 < 24 * x ^ 2 := by simpa using mul_pos (by norm_num : 0 < (24 : ℝ)) (pow_pos hpos 2)
    have p5 : 0 < 24 * x     := by simpa using mul_pos (by norm_num : 0 < (24 : ℝ)) (pow_pos hpos 1)
    have p6 : 0 < (18 : ℝ)   := by norm_num
    linarith [p1, p2, p3, p4, p5, p6]

  -- a polynomial is continuous on a closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.add
                   (Continuous.add
                     (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                     (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
             (Continuous.mul continuous_const continuous_id)).continuousOn

  -- finally invoke the usual theorem
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 12 * x ^ 6 + 14 * x ^ 5 + 13 * x ^ 4 + 18 * x ^ 3 + 5 * x ^ 2 + 18 * x) (Icc (0: ℝ) (5: ℝ)) := by
  -- abbreviations
  let f : ℝ → ℝ := λ x => 5 * x ^ 7 + 12 * x ^ 6 + 14 * x ^ 5 + 13 * x ^ 4 + 18 * x ^ 3 + 5 * x ^ 2 + 18 * x
  let D := Icc (0 : ℝ) 5

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 5

  -- f is differentiable on D
  have hdiff : DifferentiableOn ℝ f D := by
    dsimp [f]
    continuity

  -- the derivative is strictly positive on the interior of D
  have hderiv : ∀ x ∈ interior D, deriv f x > 0 := by
    intro x hx
    dsimp [f]
    -- expand the derivative
    simp [deriv_add, deriv_mul, deriv_pow', deriv_id, deriv_const] at *
    ring_nf
    -- now the goal is
    --   35 * x^6 + 72 * x^5 + 70 * x^4 + 52 * x^3 + 54 * x^2 + 10 * x + 18 > 0
    have h1 : 35 * x ^ 6 > 0 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h2 : 72 * x ^ 5 > 0 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h3 : 70 * x ^ 4 > 0 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h4 : 52 * x ^ 3 > 0 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h5 : 54 * x ^ 2 > 0 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h6 : 10 * x     > 0 := mul_pos (by norm_num) hx.1
    have h7 : 18         > 0 := by norm_num
    linarith [h1, h2, h3, h4, h5, h6, h7]

  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hdiff.continuousOn hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 4 * x ^ 6 + 19 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 4 * x ^ 2) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 4 * x ^ 6 + 19 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 4 * x ^ 2
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h0: 0 < 8 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 30 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 40 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 95 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 24 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 13 * x ^ 6 + 9 * x ^ 5 + 16 * x ^ 4 + 15 * x ^ 3 + 5 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 7 + 13 * x ^ 6 + 9 * x ^ 5 + 16 * x ^ 4 + 15 * x ^ 3 + 5 * x ^ 2
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h0: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 45 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 91 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 5 + 15 * x ^ 3 + 20 * x ^ 2) (Icc (0: ℝ) (1: ℝ)) := by
  -- abbreviate
  let f := λ x : ℝ => 5 * x ^ 5 + 15 * x ^ 3 + 20 * x ^ 2
  let D := Icc (0 : ℝ) 1

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 1

  -- the derivative is everywhere positive on the interior
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    dsimp [f]
    -- simplify the derivative of 5*x^5 + 15*x^3 + 20*x^2
    simp [ deriv_add, deriv_const_mul, deriv_pow, deriv_id ]
    -- now `deriv f x = 25*x^4 + 45*x^2 + 40*x`
    norm_num
    -- each term is ≥ 0 and in fact > 0 since x > 0
    have hxpos : 0 < x := hx.1
    have h4 : 0 < x ^ 4 := pow_pos hxpos (by norm_num : 4 ≥ 1)
    have h2 : 0 < x ^ 2 := pow_pos hxpos (by norm_num : 2 ≥ 1)
    -- now conclude
    linarith [h4, h2, hxpos]

  -- f is continuous on the closed interval
  have hf : ContinuousOn f D := by
    dsimp [f]; continuity

  -- finish by the standard result
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 12 * x ^ 5 + 15 * x ^ 4 + 4 * x ^ 2 + 11 * x + 4) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x => 8*x^7 + 12*x^5 + 15*x^4 + 4*x^2 + 11*x + 4
  let D := Icc (0 : ℝ) 5
  -- 1) D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 5
  -- 2) f is continuous on D
  have hcont : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
            (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
          (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.add (Continuous.mul continuous_const continuous_id)
                           continuous_const))).continuousOn
  -- 3) The derivative is strictly positive on the interior
  have hder_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- simplify the derivative
    simp [f] at *
    -- interior_Icc 0 5 says 0 < x ∧ x < 5
    rw [interior_Icc] at hx
    let hx0 : 0 < x := hx.1
    -- after simp, deriv f x = 56*x^6 + 60*x^4 + 60*x^3 + 8*x + 11
    have t1 : 56 * x^6 > 0 := mul_pos (by norm_num) (pow_pos hx0 _)
    have t2 : 60 * x^4 > 0 := mul_pos (by norm_num) (pow_pos hx0 _)
    have t3 : 60 * x^3 > 0 := mul_pos (by norm_num) (pow_pos hx0 _)
    have t4 : 8 * x     > 0 := mul_pos (by norm_num) hx0
    have t5 : 11        > 0 := by norm_num
    linarith
  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hder_pos).monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 4 + 6 * x ^ 3 + 2 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
example : MonotoneOn (fun x : ℝ => 17 * x^4 + 6 * x^3 + 2 * x^2 + 7 * x) (Icc (0 : ℝ) 5) := …

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 10 * x ^ 5 + 13 * x ^ 4 + 3 * x) (Icc (0: ℝ) (9: ℝ)) := by
  let f := fun x => 18*x^7 + 10*x^5 + 13*x^4 + 3*x
  let D := Icc (0:ℝ) 9

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 9

  -- the derivative of f on the interior of D is strictly positive
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- simplify the derivation in one shot
    have : deriv f x = 126*x^6 + 50*x^4 + 52*x^3 + 3 := by
      -- f has four terms, simp unfolds them all
      simp [f]
    -- rewrite and prove positivity by linarith
    rw [this]
    have h6 : 0 < 126 * x^6 := by
      apply mul_pos; norm_num; apply pow_pos hx.1
    have h4 : 0 < 50 * x^4 := by
      apply mul_pos; norm_num; apply pow_pos hx.1
    have h3 : 0 < 52 * x^3 := by
      apply mul_pos; norm_num; apply pow_pos hx.1
    -- now the sum of strictly positive terms is strictly positive
    linarith

  -- f is continuous on D (actually on all ℝ)
  have hcont : ContinuousOn f D := by
    -- easiest: continuity on ℝ by `continuity`, then restrict to D
    have : Continuous f := by continuity
    simpa [f] using this.continuousOn (subset_univ _)

  -- conclude strict monotonicity hence monotonicity on D
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 12 * x ^ 5 + 14 * x ^ 4 + 12 * x ^ 2 + 7 * x) (Icc (0: ℝ) (6: ℝ)) := by
  -- name the function and the domain
  let f := λ x => 7*x^7 + 12*x^5 + 14*x^4 + 12*x^2 + 7*x
  let D := Icc (0:ℝ) 6

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0:ℝ) 6

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- unfold f and compute the derivative
    unfold f
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_id'', deriv_const]
    ring
    -- now x ∈ interior D, so 0 < x < 6
    rw [interior_Icc] at hx
    -- deriv f x = 49*x^6 + 60*x^4 + 56*x^3 + 24*x + 7, each term is positive
    have h2 : 0 < 49*x^6 := by
      apply mul_pos; norm_num; exact pow_pos hx.1 six_pos
    have h3 : 0 < 60*x^4 := by
      apply mul_pos; norm_num; exact pow_pos hx.1 four_pos
    have h4 : 0 < 56*x^3 := by
      apply mul_pos; norm_num; exact pow_pos hx.1 three_pos
    have h5 : 0 < 24*x   := by
      apply mul_pos; norm_num; exact hx.1
    have h6 : 0 < 7      := by norm_num
    linarith

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp [f]; continuity

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 7 + 12 * x ^ 4 + 18 * x ^ 3 + 8) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 7 + 12 * x ^ 4 + 18 * x ^ 3 + 8
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 54 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 42 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 9 * x ^ 5 + 5 * x ^ 3) (Icc (0: ℝ) (3: ℝ)) := by
  let f := fun x : ℝ ↦ 5 * x ^ 7 + 9 * x ^ 5 + 5 * x ^ 3
  let D := Icc (0:ℝ) (3:ℝ)

  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc
    norm_num

  -- compute f′ and show it is strictly positive on interior D
  have hf' : ∀ x hx, 0 < deriv f x := by
    intros x hx
    -- expand the definition of f and its derivative
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- first summand: 5 * x^7
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- second summand: 9 * x^5
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- third summand: 5 * x^3
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- collect terms
    ring

    -- now show each monomial‐term is > 0 on (0,3)
    rw [interior_Icc] at hx
    -- 35 * x^6 > 0
    have h1 : 0 < 35 * x ^ 6 := by
      have pp : 0 < x ^ 6 := pow_pos hx.1
      linarith
    -- 45 * x^4 > 0
    have h2 : 0 < 45 * x ^ 4 := by
      have pp : 0 < x ^ 4 := pow_pos hx.1
      linarith
    -- 15 * x^2 > 0
    have h3 : 0 < 15 * x ^ 2 := by
      have pp : 0 < x ^ 2 := pow_pos hx.1
      linarith

    -- combine
    linarith [h1, h2, h3]

    -- provide the differentiability witnesses for `deriv`
    all_goals
      try
        exact differentiableAt_id
      <|> try exact differentiableAt_const _
      <|> try exact differentiableAt_pow _
      <|> try exact (differentiableAt_const _).mul (differentiableAt_pow _)

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    -- f = 5·x^7 + 9·x^5 + 5·x^3 is a sum of continuous functions
    simp [f]
    apply ( Continuous.add
              (Continuous.add
                (Continuous.mul (continuous_const : Continuous fun _ => 5)
                                 (Continuous.pow continuous_id 7))
                (Continuous.mul (continuous_const : Continuous fun _ => 9)
                                 (Continuous.pow continuous_id 5)))
              (Continuous.mul (continuous_const : Continuous fun _ => 5)
                               (Continuous.pow continuous_id 3))
            ).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 19 * x ^ 7 + 15 * x ^ 5 + 15 * x ^ 3 + 15 * x ^ 2 + 7 * x + 3) (Icc (0: ℝ) (10: ℝ)) := by
  -- abbreviations
  let f : ℝ → ℝ := λ x => 19 * x ^ 7 + 15 * x ^ 5 + 15 * x ^ 3 + 15 * x ^ 2 + 7 * x + 3
  let D := Icc (0 : ℝ) 10

  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc 0 10

  -- the derivative on the interior is strictly positive
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute `deriv f x`
    unfold f
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring
    -- now `deriv f x = 133 * x^6 + 75 * x^4 + 45 * x^2 + 30 * x + 7`
    -- use `0 < x` from interior and positivity of all coefficients
    rw [interior_Icc] at hx
    have h0 : 0 < 7 := by norm_num
    have h1 : 0 < 30 * x := by
      have : 0 < x := hx.1
      linarith [mul_pos (by norm_num) this]
    have h2 : 0 < 45 * x ^ 2 := by
      have : 0 < x ^ 2 := pow_pos hx.1 2
      linarith [mul_pos (by norm_num) this]
    have h3 : 0 < 75 * x ^ 4 := by
      have : 0 < x ^ 4 := pow_pos hx.1 4
      linarith [mul_pos (by norm_num) this]
    have h4 : 0 < 133 * x ^ 6 := by
      have : 0 < x ^ 6 := pow_pos hx.1 6
      linarith [mul_pos (by norm_num) this]
    linarith [h0, h1, h2, h3, h4]

    -- finally supply the differentiability proofs needed by `deriv`
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact differentiableAt_pow _
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    repeat exact DifferentiableAt.add?  -- combine all the summands

  -- continuity on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.add
                   (Continuous.add
                     (Continuous.mul continuous_const (Continuous.pow continuous_id _))
                     (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
                   (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
               (Continuous.mul continuous_const (Continuous.id)))
             continuous_const).continuousOn

  -- conclude monotonicity from positivity of the derivative
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 7 + 11 * x ^ 6 + 13 * x ^ 5 + 8 * x ^ 4 + 5 * x ^ 3 + 8 * x ^ 2 + 7 * x
  let D := Icc (0 : ℝ) (2 : ℝ)

  -- The domain is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- The derivative is strictly positive on the interior (0, 2)
  have hf' : ∀ x hx, 0 < deriv f x :=
    by
    intro x hx
    -- compute the derivative
    unfold f
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring
    -- interior_Icc: hx.1 : 0 < x, hx.2 : x < 2
    rw [interior_Icc] at hx
    -- build positivity of each term
    have h1 : 0 < 84 * x ^ 6 := by linarith [pow_pos hx.1]
    have h2 : 0 < 66 * x ^ 5 := by linarith [pow_pos hx.1]
    have h3 : 0 < 65 * x ^ 4 := by linarith [pow_pos hx.1]
    have h4 : 0 < 32 * x ^ 3 := by linarith [pow_pos hx.1]
    have h5 : 0 < 15 * x ^ 2 := by linarith [pow_pos hx.1]
    have h6 : 0 < 16 * x     := by linarith [hx.1]
    have h7 : 0 < 7         := by linarith
    -- conclude strict positivity of the sum
    linarith [h1, h2, h3, h4, h5, h6, h7]

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp only [f]
    apply
      (Continuous.add
         (Continuous.add
            (Continuous.add
               (Continuous.add
                  (Continuous.add
                     (Continuous.add
                        (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                        (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
                     (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
                  (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
               (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
            (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
         (Continuous.mul continuous_const continuous_id)).continuousOn

  -- apply the criterion: convex domain, continuity, and strictly positive derivative
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 9 * x ^ 3 + 18 * x ^ 2 + 12 * x + 16) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 6 + 7 * x ^ 5 + 12 * x ^ 4 + 9 * x ^ 3 + 18 * x ^ 2 + 12 * x + 16
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h1: 0 < 12 := by linarith [hx.1]
    have h2: 0 < 36 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 27 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 48 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 35 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h6: 0 < 48 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 7 + 6 * x ^ 6 + 17 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 7 + 6 * x ^ 6 + 17 * x ^ 3 + 12 * x ^ 2 + 9 * x
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 9 := by linarith [hx.1]
    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 36 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 105 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 12 * x ^ 6 + 12 * x ^ 5 + 3 * x ^ 4 + 7 * x) (Icc (0: ℝ) (8: ℝ)) := by
 …

example: MonotoneOn (λ x ↦ 15 * x ^ 6 + 5 * x ^ 3 + 16 * x ^ 2 + 7) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 15 * x ^ 6 + 5 * x ^ 3 + 16 * x ^ 2 + 7
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 32 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 90 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 7 + 20 * x ^ 4 + 4 * x ^ 2 + 18 * x + 15) (Icc (0: ℝ) (5: ℝ)) := by
  -- set up
  let f := λ x : ℝ ↦ 16 * x ^ 7 + 20 * x ^ 4 + 4 * x ^ 2 + 18 * x + 15
  let D := Icc (0 : ℝ) 5
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) 5

  -- prove f′(x) > 0 on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold derivative
    dsimp [f]
    -- there are four additions
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- now each term: 16*x^7, 20*x^4, 4*x^2, 18*x, 15
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const]; nth_rewrite 1 [deriv_id'']
    -- simplify to the polynomial 112*x^6 + 80*x^3 + 8*x + 18
    ring

    -- now show positivity on (0,5)
    rw [interior_Icc] at hx
    -- term by term
    have h1 : 0 < 112 * x ^ 6 := by
      apply mul_pos
      norm_num
      apply pow_pos hx.1
    have h2 : 0 < 80 * x ^ 3 := by
      apply mul_pos
      norm_num
      apply pow_pos hx.1
    have h3 : 0 < 8 * x := by
      apply mul_pos
      norm_num
      exact hx.1
    have h4 : 0 < 18 := by norm_num
    linarith [h1, h2, h3, h4]

    -- supply differentiability facts for `deriv`
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try apply DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try apply DifferentiableAt.add

  -- continuity on the closed interval
  have hf : ContinuousOn f D := by
    dsimp [f]
    -- sum of continuous functions
    apply (Continuous.add
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
            (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
        (Continuous.mul continuous_const continuous_id))
      continuous_const
    ).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 7 + 19 * x ^ 5 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x:ℝ ↦ 2*x^7 + 19*x^5 + 4*x^3 + 20*x
  let D := Icc (0:ℝ) (7:ℝ)
  have hD : Convex ℝ D := by apply convex_Icc (0:ℝ) (7:ℝ)

  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    -- compute deriv f x
    unfold f
    -- three additions
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- deriv(2*x^7)
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const];
      nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    -- deriv(19*x^5)
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const];
      nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    -- deriv(4*x^3)
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_const];
      nth_rewrite 1 [deriv_pow'']; nth_rewrite 1 [deriv_id'']
    -- deriv(20*x)
    nth_rewrite 1 [deriv_mul]; nth_rewrite 1 [deriv_id'']
    ring
    -- now prove positivity on (0,7)
    rw [interior_Icc] at hx
    have h1 : 0 < 14 * x ^ 6 := by
      have p := pow_pos hx.1
      linarith [p]
    have h2 : 0 < 95 * x ^ 4 := by
      have p := pow_pos hx.1
      linarith [p]
    have h3 : 0 < 12 * x ^ 2 := by
      have p := pow_pos hx.1
      linarith [p]
    have h4 : 0 < 20 := by norm_num
    linarith [h1, h2, h3, h4]

    -- discharge the differentiability hypotheses used by the nth_rewrite’s
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

  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.mul continuous_const (Continuous.pow continuous_id _))
            (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
          (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
        (Continuous.mul continuous_const continuous_id)).continuousOn

  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 5 * x ^ 6 + 12 * x ^ 5 + 17 * x ^ 4 + 8 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
  let f := fun x => 17 * x ^ 7 + 5 * x ^ 6 + 12 * x ^ 5 + 17 * x ^ 4 + 8 * x ^ 3
  let D := Icc (0 : ℝ) 6
  -- 1) D is convex
  have hD : Convex ℝ D := convex_Icc 0 6
  -- 2) f is continuous on D
  have hcont : ContinuousOn f D := by continuity
  -- 3) the derivative is strictly positive on the interior
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring                -- now we have
                         --   deriv f x = 119*x^6 + 30*x^5 + 60*x^4 + 68*x^3 + 24*x^2
    -- from 0 < x < 6 we get x > 0, hence each monomial is positive
    rw [interior_Icc] at hx
    have p1 : 119 * x^6 > 0 := mul_pos (by norm_num) (pow_pos hx.1 six_le_two := by decide)
    have p2 : 30  * x^5 > 0 := mul_pos (by norm_num) (pow_pos hx.1)
    have p3 : 60  * x^4 > 0 := mul_pos (by norm_num) (pow_pos hx.1)
    have p4 : 68  * x^3 > 0 := mul_pos (by norm_num) (pow_pos hx.1)
    have p5 : 24  * x^2 > 0 := mul_pos (by norm_num) (pow_pos hx.1)
    linarith
  -- 4) assemble with the strict–monotonicity‐by‐derivative lemma
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 6 + 13 * x ^ 5 + 17 * x ^ 4 + 17 * x ^ 3 + 7 * x ^ 2 + 10 * x + 2) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 13 * x ^ 6 + 13 * x ^ 5 + 17 * x ^ 4 + 17 * x ^ 3 + 7 * x ^ 2 + 10 * x + 2
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h1: 0 < 10 := by linarith [hx.1]
    have h2: 0 < 14 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 51 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 68 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 65 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h6: 0 < 78 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 11 * x ^ 4 + 8 * x ^ 2 + 20 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := fun x => 9*x^5 + 11*x^4 + 8*x^2 + 20*x
  let D := Icc (0 : ℝ) 5
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 5

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- the `continuity` tactic knows how to handle polynomials
    continuity

  -- the derivative of f is strictly positive on the interior of D
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- expand deriv f x
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const]
    ring
    -- interior D = Ioo 0 5, so x > 0
    rwa [interior_Icc] at hx
    let ⟨hx0, _⟩ := hx
    -- now show each term in the sum is positive
    have A : 0 < (45 : ℝ) * x^4 := mul_pos (by norm_num) (pow_pos hx0)
    have B : 0 < (44 : ℝ) * x^3 := mul_pos (by norm_num) (pow_pos hx0)
    have C : 0 < (16 : ℝ) * x   := mul_pos (by norm_num) hx0
    have D₁ : 0 < (20 : ℝ)     := by norm_num
    linarith [A, B, C, D₁]

  -- now apply the strict‐monotonicity criterion
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 6 + 4 * x ^ 4 + 11 * x ^ 2 + 19 * x + 3) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 6 + 4 * x ^ 4 + 11 * x ^ 2 + 19 * x + 3
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    have h1: 0 < 19 := by linarith [hx.1]
    have h2: 0 < 22 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 16 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 12 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 5 + 14 * x ^ 4 + 12 * x + 10) (Icc (0: ℝ) (2: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 5 + 14 * x ^ 4 + 12 * x + 10
  let D := Icc (0: ℝ) (2: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (2: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    have h1: 0 < 12 := by linarith [hx.1]
    have h2: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 4 * x ^ 5 + 8 * x ^ 4 + 3 * x ^ 3 + 20 * x ^ 2 + 8 * x) (Icc (0: ℝ) (9: ℝ)) := by
  -- 1) setup
  let f : ℝ → ℝ := fun x => 20 * x ^ 6 + 4 * x ^ 5 + 8 * x ^ 4 + 3 * x ^ 3 + 20 * x ^ 2 + 8 * x
  let D := Icc (0 : ℝ) (9 : ℝ)
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (9 : ℝ)

  -- 2) show deriv f > 0 on interior D
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- simplify the definition of the derivative
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_id'', deriv_const] 
      with
        deriv_simps
    -- now we have `deriv f x = 120*x^5 + 20*x^4 + 32*x^3 + 9*x^2 + 40*x + 8`
    ring_nf at * 
    -- interior D = (0,9)
    rw [interior_Icc] at hx
    -- each monomial is strictly positive on x>0
    have h1 : 0 < 120 * x ^ 5 := mul_pos (by norm_num) (pow_pos hx.1 five_pos)
    have h2 : 0 < 20  * x ^ 4 := mul_pos (by norm_num) (pow_pos hx.1 four_pos)
    have h3 : 0 < 32  * x ^ 3 := mul_pos (by norm_num) (pow_pos hx.1 three_pos)
    have h4 : 0 < 9   * x ^ 2 := mul_pos (by norm_num) (pow_pos hx.1 two_pos)
    have h5 : 0 < 40  * x     := mul_pos (by norm_num) hx.1
    have h6 : 0 < 8          := by norm_num
    linarith [h1, h2, h3, h4, h5, h6]

  -- 3) continuity is clear for a polynomial
  have hcont : ContinuousOn f D := by
    simp only [continuous_on_add, continuous_on_mul, continuous_on_pow, continuous_on_const, continuous_on_id]
    refine continuous_on_id.add_const.mul_const.add_const.mul_const.add_const.mul_const.add_const.mul_const.add_const

  -- conclude
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 5 + 16 * x ^ 4) (Icc (0: ℝ) (10: ℝ)) := by
  -- abbreviate
  let f := fun x => 20 * x ^ 5 + 16 * x ^ 4
  let D := Icc (0:ℝ) (10:ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0:ℝ) (10:ℝ)

  -- compute the derivative and show it is positive on the interior (0,10)
  have hder : ∀ x hx, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- rewrite with the two terms
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id] at *
    -- now `deriv f x` is `100 * x ^ 4 + 64 * x ^ 3`
    ring_nf
    -- use that x > 0 to show each summand is positive
    rw [interior_Icc] at hx
    have h1 : 0 < 100 * x ^ 4 := mul_pos (by norm_num) (pow_pos hx.1 _)
    have h2 : 0 <  64 * x ^ 3 := mul_pos (by norm_num) (pow_pos hx.1 _)
    linarith

  -- polynomials are continuous
  have hcont : ContinuousOn f D := by continuity

  -- conclude monotonicity from strict monotonicity
  apply (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 4 * x ^ 5 + 9 * x ^ 3 + 20 * x ^ 2 + 17 * x + 8) (Icc (0: ℝ) (1: ℝ)) := by
  -- abbreviate the function and the domain
  let f := λ x : ℝ => 4*x^7 + 4*x^5 + 9*x^3 + 20*x^2 + 17*x + 8
  let D := Icc (0 : ℝ) (1 : ℝ)

  -- the interval [0,1] is convex
  have hD : Convex ℝ D := convex_Icc 0 1

  -- compute the derivative and show it is strictly positive on (0,1)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    unfold f
    -- break up the sum
    repeat (nth_rewrite 1 [deriv_add])
    -- each term of the form c * x^n
    repeat (nth_rewrite 1 [deriv_mul])
    repeat (nth_rewrite 1 [deriv_const])
    repeat (nth_rewrite 1 [deriv_pow''])
    repeat (nth_rewrite 1 [deriv_id''])
    -- simplify to get 28*x^6 + 20*x^4 + 27*x^2 + 40*x + 17
    ring
    -- reduce the goal to positivity of each summand
    rw [interior_Icc] at hx
    have h1 : 0 < 28 * x^6 := by
      have hp : 0 < x^6 := pow_pos hx.1
      linarith [hp]
    have h2 : 0 < 20 * x^4 := by
      have hp : 0 < x^4 := pow_pos hx.1
      linarith [hp]
    have h3 : 0 < 27 * x^2 := by
      have hp : 0 < x^2 := pow_pos hx.1
      linarith [hp]
    have h4 : 0 < 40 * x := by
      have hp : 0 < x := hx.1
      linarith [hp]
    have h5 : 0 < 17 := by linarith
    -- conclude the derivative is > 0
    linarith [h1, h2, h3, h4, h5]

    -- now supply the differentiability proofs
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact DifferentiableAt.add _ _

  -- f is a sum of continuous monomials, hence continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.add
            (Continuous.add
              (Continuous.add
                (Continuous.mul continuous_const (Continuous.pow continuous_id _))
                (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
              (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
            (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
          (Continuous.mul continuous_const (Continuous.pow continuous_id _)))
        (Continuous.mul continuous_const continuous_id)).continuousOn

  -- by the derivative test we get strict monotonicity, hence MonotoneOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 16 * x ^ 4 + 10 * x ^ 3 + 13 * x ^ 2) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x => 16 * x^4 + 10 * x^3 + 13 * x^2
  let D := Icc (0 : ℝ) 9

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute the derivative
  have hderiv : ∀ x ∈ interior D, deriv f x = 64 * x^3 + 30 * x^2 + 26 * x := by
    intro x hx
    simp [f]            -- unfolds f and uses deriv_add, deriv_mul, deriv_pow, etc.
    ring                -- bundles all the add/mul arithmetic

  -- show it is strictly positive on (0,9)
  have hpos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    rw [hderiv x hx]
    -- interior (Icc 0 9) is {x | 0 < x ∧ x < 9}
    rw [interior_Icc] at hx
    have h0 : 0 < x := hx.1
    have h2 : 0 < x^2 := pow_pos h0
    have h3 : 0 < x^3 := pow_pos h0
    -- 64*x^3 + 30*x^2 + 26*x > 0 by linear combination of positives
    linarith [h3, h2]

  -- f is continuous on D (polynomial on ℝ)
  have hcont : ContinuousOn f D := by continuity

  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hpos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 6 * x ^ 4 + 7 * x ^ 3 + 12 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 6 * x ^ 4 + 7 * x ^ 3 + 12 * x ^ 2 + 6 * x
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 6 := by linarith [hx.1]
    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 24 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 18 * x ^ 7 + 5 * x ^ 6 + 15 * x ^ 4 + 3 * x ^ 2 + 7 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x => 18*x^7 + 5*x^6 + 15*x^4 + 3*x^2 + 7*x
  let D := Icc (0:ℝ) (5:ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0:ℝ) (5:ℝ)
  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    continuity
  -- f′(x) = 126*x^6 + 30*x^5 + 60*x^3 + 6*x + 7 > 0 on (0,5)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    rintro x ⟨hx0, _⟩
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const]
    -- prove each summand is > 0
    have h1 : 0 < 126*x^6 := mul_pos (by norm_num) (pow_pos hx0)
    have h2 : 0 < 30*x^5  := mul_pos (by norm_num) (pow_pos hx0)
    have h3 : 0 < 60*x^3  := mul_pos (by norm_num) (pow_pos hx0)
    have h4 : 0 < 6*x     := mul_pos (by norm_num) hx0
    have h5 : 0 < 7       := by norm_num
    linarith [h1, h2, h3, h4, h5]
  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 10 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 28 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 20 * x ^ 2 + 14 * x + 20) (Icc (0: ℝ) (3: ℝ)) := by
  -- abbreviate the function and the domain
  let f := fun x : ℝ => 5 * x ^ 7 + 3 * x ^ 5 + 6 * x ^ 4 + 20 * x ^ 2 + 14 * x + 20
  let D := Icc (0 : ℝ) 3

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute the derivative and show it's strictly positive on the interior (0, 3)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- interior D is (0, 3)
    rw [interior_Icc] at hx
    -- compute deriv f x
    have : deriv f x = 35 * x ^ 6 + 15 * x ^ 4 + 24 * x ^ 3 + 40 * x + 14 := by
      dsimp [f]
      simp only [deriv_add, deriv_mul, deriv_pow'', deriv_const, deriv_id'']
      ring
    rw [this]
    -- each term is > 0 because x ∈ (0, 3)
    have h₁ : 35 * x ^ 6 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; linarith
    have h₂ : 15 * x ^ 4 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; linarith
    have h₃ : 24 * x ^ 3 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; linarith
    have h₄ : 40 * x > 0 := by
      apply mul_pos; norm_num; exact hx.1
    have h₅ : 14 > 0 := by norm_num
    linarith

  -- f is continuous on D (polynomials are continuous)
  have hcont : ContinuousOn f D := by
    continuity

  -- apply the theorem that a function with positive derivative on a convex set is strictly
  -- monotone, hence monotone
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 16 * x ^ 4 + 5 * x ^ 3 + 19 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 6 + 16 * x ^ 4 + 5 * x ^ 3 + 19 * x ^ 2
  let D := Icc (0: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 38 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h1: 0 < 15 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 64 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 5 + 19 * x ^ 4 + 6 * x ^ 3 + 12 * x + 14) (Icc (0: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 5 + 19 * x ^ 4 + 6 * x ^ 3 + 12 * x + 14
  let D := Icc (0: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h1: 0 < 12 := by linarith [hx.1]
    have h2: 0 < 18 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 76 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 15 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h6: 0 < 70 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 7 + 3 * x ^ 5 + 8 * x ^ 4 + 4 * x ^ 3 + 20 * x) (Icc (0: ℝ) (4: ℝ)) := by
  -- abbreviate
  let f := λ x : ℝ ↷ 12 * x ^ 7 + 3 * x ^ 5 + 8 * x ^ 4 + 4 * x ^ 3 + 20 * x
  let D := Icc (0 : ℝ) (4 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (0 : ℝ) (4 : ℝ)
  -- derivative strictly positive on the interior
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    -- differentiate term‐by‐term
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- now handle each monomial
    nth_rewrite 1 [deriv_mul]
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
    -- collect
    ring
    -- interior D means 0 < x < 4
    rw [interior_Icc] at hx
    -- show each summand is strictly positive
    have h1 : 0 < 84 * x ^ 6 := by
      have p := pow_pos hx.1
      linarith [p]
    have h2 : 0 < 15 * x ^ 4 := by
      have p := pow_pos hx.1
      linarith [p]
    have h3 : 0 < 32 * x ^ 3 := by
      have p := pow_pos hx.1
      linarith [p]
    have h4 : 0 < 12 * x ^ 2 := by
      have p := pow_pos hx.1
      linarith [p]
    have h5 : 0 < 20 := by linarith
    linarith [h1, h2, h3, h4, h5]
    -- register differentiability of each piece
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
  -- continuity on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.add
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
               (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
             (Continuous.mul continuous_const continuous_id)).continuousOn
  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 2 * x ^ 6 + 9 * x ^ 5 + 10 * x + 13) (Icc (0: ℝ) (9: ℝ)) := by
  let f := fun x : ℝ => 5*x^7 + 2*x^6 + 9*x^5 + 10*x + 13
  let D := Icc (0 : ℝ) (9 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (9 : ℝ)

  -- The derivative of f on the interior of D is strictly positive
  have hf' : ∀ x (hx : x ∈ interior D), 0 < deriv f x := by
    intro x hx
    -- unfold the definition and compute the derivative
    dsimp [f]
    ring
    -- interior of Icc (0,9) is (0,9)
    rw [interior_Icc] at hx
    -- each term of 35*x^6 + 12*x^5 + 45*x^4 + 10 is > 0 when x ∈ (0,9)
    have t1 : 0 < 35 * x^6 := mul_pos (by norm_num) (pow_pos hx.1)
    have t2 : 0 < 12 * x^5 := mul_pos (by norm_num) (pow_pos hx.1)
    have t3 : 0 < 45 * x^4 := mul_pos (by norm_num) (pow_pos hx.1)
    have t4 : 0 < 10        := by norm_num
    -- combine them
    linarith [t1, t2, t3, t4]

  -- f is continuous on D (a sum of continuous functions)
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.add
                 (Continuous.add
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
                   (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
                 (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- conclude monotonicity by the usual derivative test on a convex set
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 11 * x ^ 5 + 20 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 12 * x + 3) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 11 * x ^ 5 + 20 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 12 * x + 3
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h1: 0 < 12 := by linarith [hx.1]
    have h2: 0 < 12 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 21 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 80 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 55 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h6: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 15 * x ^ 4 + 19 * x + 13) (Icc (0: ℝ) (7: ℝ)) := by
  -- we set up notation
  set f := fun x : ℝ => 15 * x ^ 4 + 19 * x + 13
  let D := Icc (0:ℝ) 7
  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc 0 7
  -- compute the derivative and show it is strictly positive on the interior
  have hderiv : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- unfold definition and simplify derivative by linearity and standard rules
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]
    -- now deriv f x = 15 * 4 * x ^ 3 + 19
    -- i.e. 60 * x^3 + 19
    have hpos₁ : 0 < 60 * x ^ 3 := by
      -- 60 > 0 and x^3 > 0 on (0,7)
      have : 0 < 60 := by norm_num
      have : 0 < x ^ 3 := pow_pos hx.1 (by norm_num : 0 < 3)
      linarith
    -- 19 > 0
    have hpos₂ : 0 < (19 : ℝ) := by norm_num
    -- conclude
    linarith
  -- f is continuous on the closed interval
  have hcont : ContinuousOn f D := by
    continuity
  -- apply the standard criterion: strictly positive deriv ⇒ strictly monotone ⇒ monotone
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 4 + 6 * x ^ 3 + 14 * x ^ 2 + 6) (Icc (0: ℝ) (5: ℝ)) := by
  -- abbreviate the function and the domain
  let f := fun x => 7*x^4 + 6*x^3 + 14*x^2 + 6
  let D := Icc (0 : ℝ) 5

  -- the interval [0,5] is convex
  have hD : Convex ℝ D := convex_Icc 0 5

  -- f is continuous on [0,5]
  have hcont : ContinuousOn f D := by
    -- `continuity` solves this for polynomials
    continuity

  -- show the derivative is strictly positive on the interior (0,5)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold the definition of f and compute the derivative
    unfold f
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id] at *
    -- now `deriv f x` is `7*4*x^3 + 6*3*x^2 + 14*2*x + 0`
    ring_nf
    -- interior [0,5] is (0,5)
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hx.1
    -- each term is positive
    have t1 : 0 < 28 * x^3 := mul_pos (by norm_num) (pow_pos hx0 3)
    have t2 : 0 < 18 * x^2 := mul_pos (by norm_num) (pow_pos hx0 2)
    have t3 : 0 < 28 * x   := mul_pos (by norm_num) hx0
    -- sum is positive
    linarith [t1, t2, t3]

  -- apply the standard strict‐mono‐on‐of‐deriv‐pos lemma
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 9 * x ^ 5 + 14 * x ^ 4 + 3 * x ^ 2 + 17) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 6 + 9 * x ^ 5 + 14 * x ^ 4 + 3 * x ^ 2 + 17
  let D := Icc (0: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    rw [interior_Icc] at hx
    have h1: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 45 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 60 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 11 * x ^ 7 + 14 * x ^ 4 + 18 * x ^ 3 + 3 * x ^ 2 + 8 * x) (Icc (0: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 11 * x ^ 7 + 14 * x ^ 4 + 18 * x ^ 3 + 3 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]
    have h1: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 54 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 56 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 77 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 19 * x ^ 5 + 13 * x ^ 4 + 4 * x ^ 2 + 8 * x + 12) (Icc (0: ℝ) (10: ℝ)) := by
  let f := λ x => 3*x^7 + 19*x^5 + 13*x^4 + 4*x^2 + 8*x + 12
  let D := Icc (0 : ℝ) 10

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    continuity

  -- the derivative is strictly positive on the interior of D
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    -- unfold f and let simp compute the deriv
    dsimp [f]
    simp [deriv_add, deriv_const_mul, deriv_pow']
    -- now we see
    --   deriv f x = 21*x^6 + 95*x^4 + 52*x^3 + 8*x + 8
    ring

    -- interior (Icc 0 10) = Ioo 0 10
    rw [interior_Icc] at hx

    -- each term is strictly positive because x ∈ (0,10)
    have h1 : 0 < 21 * x^6 := by linarith [pow_pos hx.1]
    have h2 : 0 < 95 * x^4 := by linarith [pow_pos hx.1]
    have h3 : 0 < 52 * x^3 := by linarith [pow_pos hx.1]
    have h4 : 0 < 8  * x   := by linarith [pow_pos hx.1]
    have h5 : 0 < 8       := by norm_num

    linarith [h1, h2, h3, h4, h5]

  -- conclude by the standard strict-monotonicity‐from‐positive‐derivative lemma
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 2 + 12 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := fun x => 13 * x ^ 2 + 12 * x
  let D := Icc (0 : ℝ) 8

  -- [0,8] is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute deriv f x and show it is > 0 on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- first show deriv f x = 26 * x + 12
    have hder : deriv f x = 26 * x + 12 := by
      dsimp [f]
      -- deriv (13*x^2 + 12*x) = deriv (13*x^2) + deriv (12*x)
      rw [deriv_add,
          deriv_const_mul,      -- deriv (13 * x^2) = 13 * deriv (x^2)
          deriv_pow 2,          -- deriv (x^2) = 2 * x
          deriv_id,             -- deriv id = 1
          deriv_const_mul,      -- deriv (12 * x) = 12 * deriv x
          deriv_id]
      ring
    -- replace and use the interior inequalities 0 < x < 8
    rw [hder]
    rw [interior_Icc] at hx
    -- 26*x + 12 > 0 because x ≥ 0
    linarith

  -- f is (polynomial so) continuous on [0,8]
  have hf : ContinuousOn f D := by
    dsimp [f]
    continuity

  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 7 + 13 * x ^ 6 + 18 * x ^ 5 + 15 * x ^ 4 + 9 * x ^ 3 + 17 * x ^ 2 + 6 * x) (Icc (0: ℝ) (1: ℝ)) := by
  let f := fun x => 3*x^7 + 13*x^6 + 18*x^5 + 15*x^4 + 9*x^3 + 17*x^2 + 6*x
  let D := Icc (0:ℝ) 1

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0:ℝ) 1

  -- The derivative of f is strictly positive on the interior (0,1).
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- expand deriv f x into a sum of monomials
    unfold f
    -- we have 6 summands + one linear term
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- now each piece
    nth_rewrite 1 [deriv_mul]
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
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- at this point `deriv f x` is
    --   21 * x^6 + 78 * x^5 + 90 * x^4 + 60 * x^3 + 27 * x^2 + 34 * x + 6
    ring
    -- use hx : 0 < x < 1
    rw [interior_Icc] at hx
    -- each term is strictly positive
    have h6   : 0 < (6 : ℝ) := by decide
    have h34  : 0 < 34 * x := by linarith [pow_pos (lt_of_lt_of_le hx.1 (by norm_num : x ≤ 1))] 
    have h27  : 0 < 27 * x^2 := by linarith [pow_pos hx.1]
    have h60  : 0 < 60 * x^3 := by linarith [pow_pos hx.1]
    have h90  : 0 < 90 * x^4 := by linarith [pow_pos hx.1]
    have h78  : 0 < 78 * x^5 := by linarith [pow_pos hx.1]
    have h21  : 0 < 21 * x^6 := by linarith [pow_pos hx.1]
    linarith [h6, h34, h27, h60, h90, h78, h21]

    -- finally discharge all the differentiability assumptions
    all_goals
      try exact differentiableAt_id
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
      try exact (DifferentiableAt.add (differentiableAt_const _) (differentiableAt_const _))

  -- f is continuous on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add
           (Continuous.add (Continuous.add (Continuous.add
             (Continuous.mul continuous_const (Continuous.pow continuous_id 7))
             (Continuous.mul continuous_const (Continuous.pow continuous_id 6)))
             (Continuous.mul continuous_const (Continuous.pow continuous_id 5)))
             (Continuous.mul continuous_const (Continuous.pow continuous_id 4)))
             (Continuous.mul continuous_const (Continuous.pow continuous_id 3)))
             (Continuous.mul continuous_const (Continuous.pow continuous_id 2)))
             (Continuous.mul continuous_const continuous_id)).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 20 * x ^ 6 + 14 * x ^ 5 + 3 * x ^ 4 + 13 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  -- abbreviate the function and the domain
  let f : ℝ → ℝ := λ x => 20*x^6 + 14*x^5 + 3*x^4 + 13*x^2
  let D := Icc (0:ℝ) (6:ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- show f′(x) > 0 on the interior (0,6)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intros x hx
    -- compute the derivative
    unfold f
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_const, deriv_id''] 
    -- now the goal is 120*x^5 + 70*x^4 + 12*x^3 + 26*x > 0
    ring
    -- reduce the interval‐condition
    rw [interior_Icc] at hx
    -- each monomial is strictly positive on (0,6)
    have h1 : 0 < 120 * x^5 :=
      by simpa using mul_pos (by norm_num : 0 < 120) (pow_pos (zero_lt_iff.mpr hx.1) _)
    have h2 : 0 < 70  * x^4 :=
      by simpa using mul_pos (by norm_num : 0 < 70)  (pow_pos (zero_lt_iff.mpr hx.1) _)
    have h3 : 0 < 12  * x^3 :=
      by simpa using mul_pos (by norm_num : 0 < 12)  (pow_pos (zero_lt_iff.mpr hx.1) _)
    have h4 : 0 < 26  * x   :=
      by simpa using mul_pos (by norm_num : 0 < 26)  (zero_lt_iff.mpr hx.1)
    linarith [h1, h2, h3, h4]

    -- discharge the differentiability‐at facts
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _

  -- f is continuous on [0,6]
  have hf : ContinuousOn f D := by
    simp [f]
    apply ( Continuous.add
              (Continuous.add
                (Continuous.mul continuous_const (Continuous.pow continuous_id 6))
                (Continuous.mul continuous_const (Continuous.pow continuous_id 5)) )
              (Continuous.add
                (Continuous.mul continuous_const (Continuous.pow continuous_id 4))
                (Continuous.mul continuous_const (Continuous.pow continuous_id 2))) ).continuousOn

  -- conclude monotonicity from strict‐positivity of the derivative
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 7 + 8 * x ^ 5 + 3 * x ^ 3 + 18 * x ^ 2 + 2 * x) (Icc (0: ℝ) (7: ℝ)) := by
  -- abbreviate the function and the interval
  let f := fun x : ℝ => 7 * x ^ 7 + 8 * x ^ 5 + 3 * x ^ 3 + 18 * x ^ 2 + 2 * x
  let D := Icc (0 : ℝ) 7

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 7

  -- compute the derivative
  have h_deriv : ∀ x hx, deriv f x = 49 * x ^ 6 + 40 * x ^ 4 +  9 * x ^ 2 + 36 * x + 2 := by
    intro x hx
    dsimp [f]
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_id'']
    ring

  -- show the derivative is strictly positive on the interior (0,7)
  have h_pos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- rewrite to the closed form
    have : deriv f x = 49 * x ^ 6 + 40 * x ^ 4 + 9 * x ^ 2 + 36 * x + 2 := by
      simpa using h_deriv x hx
    -- each term is nonnegative, and the constant 2 makes it strictly positive
    have A : 49 * x ^ 6 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; exact hx.1
    have B : 40 * x ^ 4 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; exact hx.1
    have C : 9 * x ^ 2 > 0 := by
      apply mul_pos; norm_num; apply pow_pos; exact hx.1
    have D' : 36 * x > 0 := by
      apply mul_pos; norm_num; exact hx.1
    have E : 2 > 0 := by norm_num
    linarith [this, A, B, C, D', E]

  -- f is continuous on D
  have h_cont : ContinuousOn f D := by
    continuity

  -- conclude monotonicity by the usual strict‐derivative test
  exact (strictMonoOn_of_deriv_pos hD h_cont h_pos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 2 + 8 * x + 7) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 7 + 7 * x ^ 6 + 3 * x ^ 2 + 8 * x + 7
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    have h1: 0 < 8 := by linarith [hx.1]
    have h2: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 42 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 28 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 13 * x ^ 7 + 4 * x ^ 6 + 16 * x ^ 5 + 11 * x ^ 4 + 5 * x ^ 3 + 15 * x ^ 2 + 20) (Icc (0: ℝ) (1: ℝ)) := by

example: MonotoneOn (λ x ↦ 18 * x ^ 4 + 14 * x ^ 3 + 8 * x ^ 2 + 13 * x + 11) (Icc (0: ℝ) (1: ℝ)) := by
  -- abbreviations
  let f := fun x : ℝ => 18 * x ^ 4 + 14 * x ^ 3 + 8 * x ^ 2 + 13 * x + 11
  let D := Icc (0 : ℝ) 1

  -- convexity of the domain
  have hD : Convex ℝ D := convex_Icc 0 1

  -- the key derivative‐positive lemma
  have hder_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative in one go
    have : deriv f x = 72 * x ^ 3 + 42 * x ^ 2 + 16 * x + 13 := by
      -- unfold the definition of f and simplify all deriv_*
      unfold f
      simp [deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const]
      ring
    -- rewrite and now show the resulting polynomial is > 0 on (0,1)
    rw [this]
    -- interior_Icc at tells us x ∈ (0,1)
    rcases interior_Icc.1 hx with ⟨h0, h1⟩
    -- each of the first three terms is ≥ 0, the last is +13 > 0
    have h2 : 0 ≤ 72 * x ^ 3 := mul_nonneg (by norm_num) (pow_nonneg h0 _)
    have h3 : 0 ≤ 42 * x ^ 2 := mul_nonneg (by norm_num) (pow_nonneg h0 _)
    have h4 : 0 ≤ 16 * x     := mul_nonneg (by norm_num) (le_of_lt h0)
    linarith  -- sums the nonnegatives and +13 to get strict positivity

  -- continuity on the closed interval is automatic for polynomials
  have hcont : ContinuousOn f D := by
    continuity

  -- now apply the standard strict‐deriv implies strictly monotone theorem
  exact (strictMonoOn_of_deriv_pos hD hcont hder_pos).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 7 + 10 * x ^ 6 + 11 * x ^ 4 + 10 * x ^ 3 + 13) (Icc (0: ℝ) (1: ℝ)) := by

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 17 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 2 + 2 * x + 10) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ => 5 * x ^ 7 + 17 * x ^ 6 + 12 * x ^ 5 + 6 * x ^ 2 + 2 * x + 10
  let D := Icc (0 : ℝ) (1 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (0 : ℝ) (1 : ℝ)
  -- show f′(x) > 0 on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    simp [f]
      -- now `deriv f x = 35*x^6 + 102*x^5 + 60*x^4 + 12*x + 2`
    ring
    -- interior Icc (0,1) is (0,1)
    rw [interior_Icc] at hx
    -- all terms are strictly positive for 0 < x < 1
    linarith [pow_pos hx.1 (6 : ℕ),
              pow_pos hx.1 (5 : ℕ),
              pow_pos hx.1 (4 : ℕ),
              pow_pos hx.1 (1 : ℕ)]
  -- f is continuous on D
  have hf : ContinuousOn f D := by
    have : Continuous f := by continuity
    exact this.continuousOn
  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 6 + 12 * x ^ 5 + 20 * x ^ 2) (Icc (0: ℝ) (6: ℝ)) := by
  -- We will apply strictMonoOn_of_deriv_pos,
  -- so we need (1) convexity of the domain,
  -- (2) continuity on the domain,
  -- (3) deriv f x > 0 on the interior.
  refine (strictMonoOn_of_deriv_pos _ _ _).monotoneOn
  -- (1) [0,6] is convex
  · apply convex_Icc (0:ℝ) 6
  -- (2) the polynomial is continuous on [0,6]
  · continuity
  -- (3) compute the derivative and show it is > 0 on (0,6)
  intro x hx
  dsimp only
  -- unfold the definition of deriv for this polynomial
  have hder : deriv (fun x => 10*x^6 + 12*x^5 + 20*x^2) x = 60*x^5 + 60*x^4 + 40*x := by
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]; ring
  rw [hder]
  -- now each term is strictly positive because x > 0
  have hx_pos : 0 < x := hx.1
  have t1 : 0 < 60 * x^5 := mul_pos (by norm_num) (pow_pos hx_pos _)
  have t2 : 0 < 60 * x^4 := mul_pos (by norm_num) (pow_pos hx_pos _)
  have t3 : 0 < 40 * x   := mul_pos (by norm_num) hx_pos
  linarith

example: MonotoneOn (λ x ↦ 5 * x ^ 7 + 6 * x ^ 6 + 6 * x ^ 5 + 10 * x ^ 4 + 2 * x ^ 3 + 12 * x ^ 2 + 9 * x) (Icc (0: ℝ) (8: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 7 + 6 * x ^ 6 + 6 * x ^ 5 + 10 * x ^ 4 + 2 * x ^ 3 + 12 * x ^ 2 + 9 * x
  let D := Icc (0: ℝ) (8: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (8: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
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
    rw [interior_Icc] at hx
    have h0: 0 < 9 := by linarith [hx.1]
    have h1: 0 < 24 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 6 * x ^ 2 := by
      have power_pos: 0 < x ^ 2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 40 * x ^ 3 := by
      have power_pos: 0 < x ^ 3 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h4: 0 < 30 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h5: 0 < 36 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h6: 0 < 35 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3, h4, h5, h6]
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
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 12 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 2 + 8 * x) (Icc (0: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 12 * x ^ 6 + 17 * x ^ 5 + 9 * x ^ 2 + 8 * x
  let D := Icc (0: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    have h0: 0 < 8 := by linarith [hx.1]
    have h1: 0 < 18 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h2: 0 < 85 * x ^ 4 := by
      have power_pos: 0 < x ^ 4 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    have h3: 0 < 72 * x ^ 5 := by
      have power_pos: 0 < x ^ 5 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1, h2, h3]
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
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))) (Continuous.mul (continuous_const) (continuous_id))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 14 * x ^ 7 + 15 * x ^ 5 + 5 * x ^ 4 + 4 * x ^ 3) (Icc (0: ℝ) (6: ℝ)) := by
f x = 14*x^7 + 15*x^5 + 5*x^4 + 4*x^3
D   = Icc (0:ℝ) (6:ℝ)
​

example: MonotoneOn (λ x ↦ 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11) (Icc (0: ℝ) (6: ℝ)) := by
  -- abbreviations
  let f := λ x : ℝ => 20 * x ^ 7 + 11 * x ^ 6 + 16 * x ^ 3 + 17 * x ^ 2 + 18 * x + 11
  let D := Icc (0 : ℝ) 6

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 0 6

  -- compute the derivative explicitly
  have deriv_f : ∀ x, deriv f x = 140 * x ^ 6 + 66 * x ^ 5 + 48 * x ^ 2 + 34 * x + 18 := by
    intro x
    unfold f
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring

  -- show the derivative is strictly positive on the interior (0, 6)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- rewrite using our explicit formula
    rw [deriv_f x]
    -- all powers of x are positive when x > 0
    have h6 := pow_pos hx.1 (by norm_num : 6 = 6)
    have h5 := pow_pos hx.1 (by norm_num : 5 = 5)
    have h2 := pow_pos hx.1 (by norm_num : 2 = 2)
    -- linarith finishes: 140*x^6 + 66*x^5 + 48*x^2 + 34*x + 18 > 0
    linarith

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    continuity

  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 1600) (Icc (10: ℝ) (13: ℝ)) := by
  -- set up
  let f := λ x : ℝ => 4 * x ^ 2 - 80 * x + 1600
  let D := Icc (10:ℝ) (13:ℝ)
  have hD : Convex ℝ D := convex_Icc 10 13

  -- show the derivative is strictly positive on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- unfold deriv
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_id, deriv_const]
    -- now the goal is `8 * x - 80 > 0`
    linarith [hx.1]

  -- f is obviously continuous on D
  have hf : ContinuousOn f D := by
    continuity

  -- conclude monotonicity from strict positivity of the derivative
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 64) (Icc (4: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 32 * x + 64
  let D := Icc (4 : ℝ) (13 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 4 13

  -- compute f' and show it is > 0 on the interior (4,13)
  have hderiv : ∀ x ∈ interior D, deriv f x > 0 := by
    intro x hx
    -- interior Icc 4 13 = Ioo 4 13
    rw [interior_Icc] at hx
    cases hx with h₁ h₂

    -- compute the derivative
    have : deriv f x = 8 * x - 32 := by
      dsimp [f]
      simp [deriv_add, deriv_mul_const, deriv_mul, deriv_pow, deriv_id, deriv_const, deriv_sub]
      ring
    -- reduce the goal `deriv f x > 0` to `8*x - 32 > 0`
    rw [this]
    -- now 8 * x - 32 > 0 because x > 4
    linarith

  -- f is continuous on the closed interval D
  have hf : ContinuousOn f D := by
    simp [f]
    -- f = (4 * x^2) + (−32 * x) + 64
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- now apply the strict-monotonicity‐from‐positive‐derivative lemma
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 625) (Icc (5: ℝ) (6: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 50 * x + 625
  let D := Icc (5: ℝ) (6: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (6: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 200) (Icc (5: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 40 * x + 200
  let D := Icc (5: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (15: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 162 * x + 6561) (Icc (9: ℝ) (10: ℝ)) := by
  let f := fun x : ℝ => 9 * x^2 - 162 * x + 6561
  let D := Icc (9 : ℝ) 10
  -- The domain is convex
  have hD : Convex ℝ D := convex_Icc 9 10

  -- On the interior (9,10), the derivative is positive
  have h_deriv : ∀ x hx, 0 < deriv f x
  · intro x hx
    -- unfold f and compute the derivative
    simp [f, deriv_add, deriv_mul, deriv_const, deriv_pow''] at *
    -- now `deriv f x = 18 * (x - 9)`
    simp at *
    -- interior_Icc tells us hx : 9 < x ∧ x < 10
    rw [interior_Icc] at hx
    -- hence x - 9 > 0
    linarith

  -- f is continuous on [9,10]
  have h_cont : ContinuousOn f D := by
    simpa [f] using (continuous_const.mul (continuous_id.pow 2)).sub
      ((continuous_const.mul continuous_id).add (continuous_const)).continuousOn

  -- Strict monotonicity follows, hence monotonicity
  show MonotoneOn f D
  simpa using (strictMonoOn_of_deriv_pos hD h_cont h_deriv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 700) (Icc (10: ℝ) (19: ℝ)) := by
  -- abbreviate
  let f := fun x => 7 * x^2 - 140 * x + 700
  let D := Icc (10 : ℝ) (19 : ℝ)

  -- the domain Icc[10,19] is convex
  have hD : Convex ℝ D :=
    convex_Icc (10 : ℝ) (19 : ℝ)

  -- compute the derivative
  have hderiv : deriv f = fun x => 14 * x - 140 := by
    ext x
    simp [f]

  -- on the interior (10,19) we have 14*x - 140 > 14*10 - 140 = 0
  have hpos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- hx : x ∈ interior D, i.e. 10 < x ∧ x < 19
    rw [hderiv]
    linarith [hx.1]

  -- f is a polynomial, hence continuous
  have cont_f : Continuous f := by continuity
  have cont_on : ContinuousOn f D := cont_f.continuousOn

  -- now apply the strict‐monotonicity criterion
  apply (strictMonoOn_of_deriv_pos hD cont_on hpos).monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 54 * x + 486) (Icc (9: ℝ) (16: ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ 3 * x^2 - 54 * x + 486
  let D := Icc (9 : ℝ) (16 : ℝ)

  -- [9,16] is convex
  have hD : Convex ℝ D := by
    apply convex_Icc; norm_num

  -- f is a polynomial ⇒ continuous on ℝ ⇒ continuous on D
  have hf_cont : Continuous f := by continuity
  have hf_cont_on : ContinuousOn f D := hf_cont.continuousOn

  -- compute f′(x) = 6x - 54 and show it is > 0 on (9,16)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and use the deriv-builders and ring to see deriv f x = 6*x - 54
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring
    -- now 6*x - 54 > 6*9 - 54 = 0 whenever x > 9
    rw [interior_Icc] at hx
    linarith

  -- strict monotonicity follows from derivative > 0
  exact (strictMonoOn_of_deriv_pos hD hf_cont_on hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 108 * x + 3402) (Icc (9: ℝ) (12: ℝ)) := by
  let f := λ x, 6*x^2 - 108*x + 3402
  let D := Icc (9:ℝ) 12
  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- f is continuous on D
  have hcont : ContinuousOn f D := by continuity
  -- the derivative is 12*x - 108, and on the interior (9,12) this is > 0
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    dsimp only [f]
    -- compute deriv: use `simp` with the standard lemmas for deriv
    simp [deriv_pow'', deriv_mul, deriv_const, deriv_id''] at *
    -- now `deriv f x = 12*x - 108`; since 9 < x we get 12*9 < 12*x and hence 0 < 12*x - 108
    linarith [mul_lt_mul_of_pos_left hx.1 (by norm_num : (0:ℝ) < 12)]
  -- conclude by the strict‐mono‐on‐of‐deriv‐pos lemma
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 30 * x + 270) (Icc (3: ℝ) (5: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 30 * x + 270
  let D := Icc (3: ℝ) (5: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (5: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 36 * x + 972) (Icc (9: ℝ) (13: ℝ)) := by
  -- define the function and the domain
  let f : ℝ → ℝ := λ x => 2 * x^2 - 36 * x + 972
  let D := Icc (9:ℝ) (13:ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (9:ℝ) (13:ℝ)

  -- the derivative is positive on the interior (9, 13)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- compute the derivative
    simp only [deriv_const, deriv_mul, deriv_pow, deriv_id] 
    ring
    -- now we have to show 0 < 4*x - 36, using hx : 9 < x ∧ x < 13
    linarith [hx.1]

  -- f is continuous on D (polynomials are continuous)
  have hf : ContinuousOn f D := by continuity

  -- conclude monotonicity from strict-monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 270) (Icc (3: ℝ) (4: ℝ)) := by
example : MonotoneOn (fun x : ℝ => 3 * x^2 - 18 * x + 270) (Icc (3:ℝ) 4) := …

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 576) (Icc (6: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 4 * x ^ 2 - 48 * x + 576
  let D := Icc (6: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (14: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 160) (Icc (2: ℝ) (9: ℝ)) := by
 …

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 126 * x + 3528) (Icc (7: ℝ) (9: ℝ)) := by
  -- abbreviate
  let f := fun x : ℝ => 9 * x ^ 2 - 126 * x + 3528
  let D := Icc (7 : ℝ) (9 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 7 9

  -- the derivative is positive on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute  deriv f x = 18 * x - 126
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring
    -- interior_Icc says x ∈ (7,9)
    rw [interior_Icc] at hx
    -- 18*x - 126 > 18*7 - 126 = 0
    linarith [hx.1]

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (16: ℝ)) := by
  -- apply the standard monotonicity‐from‐positive‐derivative theorem
  refine (strictMonoOn_of_deriv_pos _ _ _).monotoneOn
  -- convexity of [7,16]
  · exact convex_Icc (7 : ℝ) 16
  -- continuity of our polynomial on [7,16]
  · continuity
  -- show ∀ x ∈ interior [7,16], deriv f x > 0
  · rintro x ⟨h₁, h₂⟩
    -- compute deriv (5*x^2 - 70*x + 245) = 10*x - 70
    dsimp
    simp
    -- on the interior we have 7 < x, so 10*x - 70 > 0
    linarith [h₁]

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 72 * x + 324) (Icc (9: ℝ) (16: ℝ)) := by
  -- abbreviations for the function and the interval
  let f := λ x : ℝ => 4 * x ^ 2 - 72 * x + 324
  let D := Icc (9 : ℝ) 16

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- the derivative of f is > 0 on the interior of D
  have hft : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    dsimp [f]
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_id, deriv_const]
    ring
    -- now deriv f x = 8*x - 72, and on (9,16) this is positive
    rw [interior_Icc] at hx
    linarith [hx.1]

  -- f is continuous on D
  have hfc : ContinuousOn f D := by
    dsimp [f]
    continuity

  -- conclude monotonicity from strictMonoOn_of_deriv_pos
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hfc hft).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 28) (Icc (1: ℝ) (10: ℝ)) := by
  -- set up
  let f := fun x : ℝ => 7 * x ^ 2 - 14 * x + 28
  let D := Icc (1 : ℝ) 10
  have hD : Convex ℝ D := convex_Icc _ _
  -- compute and show the derivative is positive on the interior
  have hder : ∀ x ∈ interior D, deriv f x = 14 * (x - 1) := by
    intro x hx
    dsimp [f]
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_id'', deriv_const]
    ring
  have hpos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    rw [hder x hx]
    -- on (1,10), x - 1 > 0
    have : 0 < x - 1 := by
      rw [interior_Icc] at hx
      exact sub_pos.2 hx.1
    linarith
  -- establish continuity
  have hcont : ContinuousOn f D := by
    dsimp [f]; apply
      (Continuous.add
         (Continuous.sub
           (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
           (Continuous.mul continuous_const continuous_id))
         continuous_const).continuousOn
  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hpos).monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 96 * x + 768) (Icc (8: ℝ) (15: ℝ)) := by
  let f : ℝ → ℝ := fun x => 6 * x^2 - 96 * x + 768
  let D := Icc (8 : ℝ) (15 : ℝ)
  -- 1) D is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- 2) compute the derivative in one line
  have hder : ∀ x ∈ interior D, deriv f x = 12 * x - 96 := by
    intros x hx
    dsimp [f]
    -- deriv (6*x^2) = 6 * 2 * x, deriv (-96*x) = -96, deriv (const) = 0
    -- mathlib4 proves all that in the single lemma `deriv_pow`
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow]
    ring
  -- 3) show this derivative is positive on (8,15)
  have hder_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    rw [hder x hx]
    -- now 12*x - 96 > 0 because x > 8
    simp only [sub_pos] at *
    -- 12*x > 96 ↔ x > 8 by `norm_num`
    calc
      12 * x > 12 * 8   := mul_lt_mul_of_pos_left hx.1 (by norm_num)
      _     = 96        := by norm_num
  -- 4) f is continuous on D (polynomials are continuous)
  have hcont : ContinuousOn f D := by
    dsimp [f]; continuity
  -- 5) finish with the standard slope criterion
  exact (strictMonoOn_of_deriv_pos hD hcont hder_pos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 700) (Icc (5: ℝ) (9: ℝ)) := by
  let f := fun x => 4*x^2 - 40*x + 700
  let D := Icc (5:ℝ) 9
  -- The domain is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- Compute the derivative and show it is strictly positive on the interior (5,9)
  have hf' : ∀ x (hx : x ∈ interior D), 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- `simp` knows how to differentiate +, -, constants and `x^2`
    simp [deriv_add, deriv_mul, deriv_pow', deriv_sub, deriv_const, deriv_id]
    -- now `deriv f x` is `8*x - 40`
    ring
    -- interior of `Icc 5 9` is `(5 < x ∧ x < 9)`
    rwa [interior_Icc] at hx
    -- on `(5,9)` we clearly have `8*x - 40 > 0`
    linarith
  -- Polynomials are continuous, so `f` is continuous on `Icc 5 9`
  have hf : ContinuousOn f D := by continuity
  -- Now apply the standard derivative test for strict monotonicity on a convex set
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 72 * x + 1008) (Icc (4: ℝ) (6: ℝ)) := by
  -- abbreviate
  let f := fun x => 9*x^2 - 72*x + 1008
  let D := Icc (4 : ℝ) (6 : ℝ)

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc (4 : ℝ) (6 : ℝ)

  -- f is continuous on D (a polynomial!)
  have hf_cont : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
        (Continuous.mul continuous_const continuous_id))
      continuous_const).continuousOn

  -- the derivative is deriv f x = 18*x - 72, which is >0 on (4,6)
  have hf_deriv_pos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    unfold f
    -- compute deriv step by step
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- now use 4 < x coming from interior_Icc
    rw [interior_Icc] at hx
    cases hx with hlow _   -- hlow : 4 < x
    linarith [hlow]

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf_cont hf_deriv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 80 * x + 3600) (Icc (10: ℝ) (19: ℝ)) := by
  let f := fun x => 4 * x ^ 2 - 80 * x + 3600
  let D := Icc (10 : ℝ) (19 : ℝ)

  -- The interval is convex
  have hD : Convex ℝ D := convex_Icc 10 19

  -- Compute the derivative and show it is positive on the interior (10,19)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and compute deriv f x
    dsimp [f]
    have : deriv f x = 8 * x - 80 := by
      dsimp [f]
      -- split into derivs of the three pieces
      simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id]
      ring
    -- rewrite the derivative into 8*x - 80
    rw [this]
    -- interior_Icc tells us x ∈ (10,19), so x > 10
    rwa [← show 0 < 8 * x - 80 ↔ 80 < 8 * x by simp] at hx.1
    -- equivalently: linarith [hx.1]

  -- f is a polynomial, hence continuous on ℝ, thus on D
  have hcont : ContinuousOn f D := by
    dsimp [f]; continuity

  -- Now apply the standard monotonicity criterion
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 1000) (Icc (5: ℝ) (15: ℝ)) := by
  let f := fun x => 8 * x ^ 2 - 80 * x + 1000
  let D := Icc (5 : ℝ) (15 : ℝ)
  have hD : Convex ℝ D := convex_Icc (5 : ℝ) (15 : ℝ)
  have hf : ContinuousOn f D := by continuity
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    simp
    -- now deriv f x = 16*x - 80, and on the interior we have 5 < x
    linarith [hx.1]
  -- combine convexity + continuity + deriv_pos to get monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 1344) (Icc (8: ℝ) (11: ℝ)) := by

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 2205) (Icc (7: ℝ) (11: ℝ)) := by
  -- Let f be our polynomial and D the interval [7,11].
  let f := λ x : ℝ => 5 * x ^ 2 - 70 * x + 2205
  let D := Icc (7: ℝ) (11: ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 7 11

  -- Show the derivative is strictly positive on the interior (7,11).
  have hder : ∀ x hx, 0 < deriv f x := by
    intro x hx
    unfold f
    -- differentiate term‐by‐term
    nth_rewrite 1 [deriv_add]   -- deriv (5*x^2 - 70*x + 2205) = deriv (5*x^2 - 70*x) + deriv 2205
    nth_rewrite 1 [deriv_add]   -- deriv (5*x^2 - 70*x)       = deriv (5*x^2)       + deriv (-70*x)
    nth_rewrite 1 [deriv_mul]   -- deriv (5*x^2)     = 5 * deriv (x^2)
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow''] -- deriv (x^2)      = 2 * x
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]   -- deriv (-70*x)    = -70 * deriv x
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring                        -- now we have 10*x - 70
    -- on the interior x ∈ (7,11), so x > 7 and hence 10*x - 70 > 0
    rw [interior_Icc] at hx
    linarith

  -- f is continuous on D (being a polynomial)
  have hcont : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- Now we apply the usual strict‐monotonicity‐by‐positive‐derivative result
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 216) (Icc (3: ℝ) (10: ℝ)) := by
  let f := fun x => 8 * x^2 - 48 * x + 216
  let D := Icc (3:ℝ) 10

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (3:ℝ) 10

  -- deriv f x = 16*x - 48, hence ≥ 0 on the interior (3,10)
  have hderiv : ∀ x ∈ interior D, 0 ≤ deriv f x := by
    intro x hx
    -- simplify the definition of f and compute the derivative
    simp [f]
    have : deriv f x = 16 * x - 48 := by
      simp [f]; ring
    rw [this]
    -- interior of Icc a b is (a,b)
    rw [interior_Icc] at hx
    -- finish by a quick linarith
    linarith

  -- f is a polynomial, hence continuous on D
  have hc : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const).continuousOn

  -- now apply the mean‐value‐theorem lemma
  exact monotoneOn_of_deriv_nonneg hD hderiv hc

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 1152) (Icc (4: ℝ) (7: ℝ)) := by
  -- abbreviations
  let f := fun x => 8*x^2 - 64*x + 1152
  let D := Icc 4 7

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (4 : ℝ) 7

  -- the derivative f' x = 16*x - 64, which is > 0 on the interior (4,7)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    dsimp [f]
    have A : deriv f x = 16*x - 64 := by ring
    rw [A]
    -- interior of [4,7] is (4,7)
    rw [interior_Icc] at hx
    -- on (4,7), x > 4, so 16*x - 64 > 16*4 - 64 = 0
    linarith

  -- f is a polynomial, hence continuous on ℝ and thus on D
  have hcont : ContinuousOn f D := by
    -- the `continuity` tactic solves `ContinuousOn` by combining the facts
    -- that `id`, `pow`, `mul`, `sub`, `add`, and `constant` are continuous
    continuity

  -- apply the standard monotonicity criterion
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 448) (Icc (4: ℝ) (6: ℝ)) := by
let f := λ x : ℝ, 7 * x ^ 2 - 56 * x + 448
let D := Icc (4 : ℝ) (6 : ℝ)

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 45) (Icc (1: ℝ) (6: ℝ)) := by
  -- abbreviate
  let f := fun x : ℝ => 5 * x^2 - 10 * x + 45
  let D := Icc (1 : ℝ) (6 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (1 : ℝ) (6 : ℝ)

  -- compute f' and show it is positive on the interior (1,6)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- simp‐compute the derivative
    dsimp [f]
    -- the tactic `deriv` will unfold deriv and compute
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id''] 
    -- now `deriv f x = 10 * x - 10`
    ring
    -- interior Icc gives 1 < x < 6
    rw [interior_Icc] at hx
    -- conclude positivity
    calc
      0 < 10 * x - 10 := by linarith [hx.1]

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    dsimp [f]
    -- f = (5) * x^2 + (−10) * x + 45
    apply ( Continuous.add
             ( Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id) )
             continuous_const
           ).continuousOn

  -- finally apply the standard theorem
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 40 * x + 240) (Icc (2: ℝ) (10: ℝ)) := by
  -- set up
  let f := λ x : ℝ ↦ 10 * x ^ 2 + (-40) * x + 240
  let D := Icc (2 : ℝ) (10 : ℝ)
  have hD : Convex ℝ D := by
    apply convex_Icc (2 : ℝ) (10 : ℝ)
  -- show the derivative is strictly positive on the interior
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    -- compute deriv f x
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- interior Icc (2, 10) is (2, 10)
    rw [interior_Icc] at hx
    -- for x > 2 we have 20 * x - 40 > 0
    linarith [hx.1]
    -- now discharge the differentiability proofs used by `nth_rewrite`
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _
    exact DifferentiableAt.add
      (DifferentiableAt.add
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))
      (differentiableAt_const _)
  -- show continuity on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
        (Continuous.mul continuous_const continuous_id))
      continuous_const
    ).continuousOn
  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 60 * x + 810) (Icc (3: ℝ) (13: ℝ)) := by
  let f : ℝ → ℝ := λ x => 10 * x^2 - 60 * x + 810
  let D := Icc (3:ℝ) (13:ℝ)
  have hD : Convex ℝ D := convex_Icc 3 13
  have hf_cont : Continuous f := by continuity
  have hf : ContinuousOn f D := hf_cont.continuousOn
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    have deriv_eq : deriv f x = 20 * x - 60 := by
      simp [f]; ring
    rw [deriv_eq]
    -- interior (Icc 3 13) = Ioo 3 13
    rw [interior_Icc] at hx
    rcases hx with ⟨h3, h13⟩
    -- now 20 * x - 60 > 0 because x > 3
    linarith
  -- apply the standard monotonicity‐by‐derivative lemma
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 60) (Icc (2: ℝ) (9: ℝ)) := by
  -- abbreviate the function and domain
  let f := λ x : ℝ => 3 * x ^ 2 - 12 * x + 60
  let D := Icc (2 : ℝ) (9 : ℝ)

  -- the domain is convex
  have hD : Convex ℝ D := convex_Icc 2 9

  -- compute the derivative and show it is strictly positive on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold the definition of f and simplify `deriv f x`
    unfold f
    simp
    -- the interior of `[2, 9]` is `(2, 9)`
    rw [interior_Icc] at hx
    -- now `hx.1 : 2 < x`, so `0 < 6 * x - 12` by linarith
    linarith [hx.1]

  -- f is continuous on D because it is a polynomial
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.sub
        (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
        (Continuous.mul continuous_const continuous_id))
      continuous_const).continuousOn

  -- conclude monotonicity from strict positivity of the derivative
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 4) (Icc (1: ℝ) (11: ℝ)) := by
  let f : ℝ → ℝ := fun x => 4 * x ^ 2 - 8 * x + 4
  let D := Icc (1 : ℝ) 11

  -- [1,11] is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- derivative f' x = 8*x - 8, which is > 0 on the interior 1 < x < 11
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp only [f]
    -- simplify the derivative
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id''] 
    -- now we have `deriv f x = 8*x - 8`
    linarith [lt_of_lt_of_le hx.1 (by norm_num : 11 ≤ 11)]

  -- f is continuous, hence continuous on D
  have hcont : ContinuousOn f D := by
    have : Continuous f := by continuity
    exact this.continuousOn

  -- conclude by the strict‐monotonicity‐of‐positive‐derivative theorem
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 144 * x + 2592) (Icc (9: ℝ) (19: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 144 * x + 2592
  let D := Icc (9: ℝ) (19: ℝ)

  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (9: ℝ) (19: ℝ)

  -- the derivative is positive on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv (8*x^2 - 144*x + 2592)
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    -- first term 8 * x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- second term -144 * x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- third term  + 2592
    nth_rewrite 1 [deriv_const]
    -- now simplify
    ring
    -- use 9 < x < 19
    rw [interior_Icc] at hx
    linarith [hx.1]

    -- discharge the differentiability hypotheses generated by the deriv_... rewrites
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) differentiableAt_id
    exact differentiableAt_const _

  -- f is continuous on D (polynomial)
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const
      ).continuousOn

  -- conclude
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 112 * x + 3136) (Icc (8: ℝ) (10: ℝ)) := by
  let f := λ x => 7 * x ^ 2 - 112 * x + 3136
  let D := Icc (8 : ℝ) (10 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 8 10
  -- compute the derivative once and for all
  have hderiv : ∀ x, deriv f x = 14 * x - 112 := by
    intro x
    dsimp [f]
    derivative
  -- show the derivative is strictly positive on the interior (8,10)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- rewrite using the above
    rw [hderiv]
    -- on the interior we know x > 8
    have h₁ : x > 8 := hx.1
    linarith
  -- f is continuous on D
  have hf : ContinuousOn f D := by
    continuity
  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 80 * x + 200) (Icc (5: ℝ) (14: ℝ)) := by
  -- abbreviate the function and the domain
  let f := fun x : ℝ => 8 * x ^ 2 - 80 * x + 200
  let D := Icc (5:ℝ) (14:ℝ)

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc (5:ℝ) (14:ℝ)

  -- compute the derivative on the interior and show it is strictly positive
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and simplify the deriv
    dsimp [f]
    simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow''] 
    -- now `deriv f x` is `16 * x - 80`
    ring
    -- use `5 < x < 14` from `hx : x ∈ interior D`
    rwa [interior_Icc] at hx
    linarith

  -- f is a polynomial, hence continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    -- 8*x^2 is continuous, 80*x is continuous, +200 is continuous
    apply (Continuous.add
             (Continuous.sub
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 16 * x + 48) (Icc (2: ℝ) (10: ℝ)) := by
  let f := fun x => 4*x^2 - 16*x + 48
  let D := Icc (2:ℝ) 10
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (2:ℝ) 10
  -- f is continuous on D
  have hcont : ContinuousOn f D := by continuity
  -- the derivative is 8*x - 16, which is > 0 on (2,10)
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- unfold deriv
    simp [deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_id, deriv_const]
    -- now `deriv f x = 8*x - 16`
    ring
    -- since x > 2, 8*x - 16 > 0
    linarith [hx.1]
  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 48 * x + 432) (Icc (3: ℝ) (8: ℝ)) := by
  -- abbreviations
  let f := fun x => 8 * x ^ 2 - 48 * x + 432
  let D := Icc (3 : ℝ) (8 : ℝ)

  -- [3,8] is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute deriv f and show it is >0 on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intros x hx
    dsimp [f]
    -- deriv (8 * x^2) + deriv (−48 * x) + deriv 432
    nth_rewrite 1 [deriv_add]                           -- split `8*x^2 + _`
    nth_rewrite 1 [deriv_add]                           -- split `_ + (−48*x) + 432`
    nth_rewrite 1 [deriv_mul]                           -- deriv (8*x^2)
    nth_rewrite 1 [deriv_const]                         -- the `8` is constant
    nth_rewrite 1 [deriv_pow'']                         -- deriv (x^2) = 2*x
    nth_rewrite 1 [deriv_id'']                          -- deriv id = 1
    nth_rewrite 1 [deriv_mul]                           -- deriv (−48*x)
    nth_rewrite 1 [deriv_const]                         -- the `-48` is constant
    nth_rewrite 1 [deriv_id'']                          -- deriv id = 1
    nth_rewrite 1 [deriv_const]                         -- deriv 432 = 0
    ring                                                -- now we get `16*x - 48`
    -- on the interior x>3, so 16*x-48 > 0
    linarith [hx.1]

  -- f is a polynomial, hence continuous on [3,8]
  have hf : ContinuousOn f D := by continuity

  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 84 * x + 252) (Icc (6: ℝ) (16: ℝ)) := by
  -- introduce abbreviations
  let f := λ x : ℝ ↦ 7 * x^2 - 84 * x + 252
  let D := Icc (6 : ℝ) (16 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 6 16

  -- show the derivative is strictly positive on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    unfold f
    -- compute deriv f x = 14*x - 84
    simp only [deriv_add, deriv_mul, deriv_pow'', deriv_const, deriv_id''] at *
    ring at *
    -- now 14*x - 84 = 14*(x-6), and on the interior x>6
    rw [interior_Icc] at hx
    have : 0 < 14 * (x - 6) := by
      linarith [hx.1]
    -- convert back to 14*x - 84 > 0
    linarith

    -- discharge the side‐conditions generated by `deriv_mul` and `deriv_pow''`
    -- (in effect we need: differentiableAt_const, differentiableAt_pow, differentiableAt_id)
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact (DifferentiableAt.mul (differentiableAt_const _) differentiableAt_id)

  -- f is continuous on D (it is a polynomial)
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.sub
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const).continuousOn

  -- finish by the standard `strictMonoOn_of_deriv_pos`
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 40 * x + 400) (Icc (10: ℝ) (16: ℝ)) := by
  -- set up
  let f := fun x : ℝ => 2 * x ^ 2 - 40 * x + 400
  let D := Icc (10 : ℝ) 16
  have hD : Convex ℝ D := convex_Icc _ _
  -- show f′(x) > 0 on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute the derivative of f
    dsimp [f]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    ring
    -- now show 4*x - 40 > 0 when x ∈ (10, 16)
    rw [interior_Icc] at hx
    have : 0 < 4 * x - 40 := by
      linarith [hx.1]
    simpa only [deriv] using this
    -- discharge differentiability obligations
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_id
      try exact differentiableAt_pow _
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact DifferentiableAt.sub (differentiableAt_mul_const _) (differentiableAt_mul_const _)
  -- continuity on D
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const
           ).continuousOn
  -- conclude
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
  -- We will apply the standard theorem: if D is convex,
  -- f is continuous on D and f′ > 0 on interior D, then f is strictly
  -- monotone on D, hence monotone on D.
  refine (strictMonoOn_of_deriv_pos (convex_Icc 3 7) (by continuity) fun x hx => _) .monotoneOn
  -- compute the derivative and show it is positive on (3,7)
  simp [deriv]                         -- `deriv (fun x => 6*x^2 - 36*x + 324) x = 12*x - 36`
  linarith [hx.1]                     -- since 3 < x, 12*x - 36 > 0

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 112 * x + 2744) (Icc (7: ℝ) (13: ℝ)) := by
f x = 8 * x^2 - 112 * x + 2744

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (15: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 160 * x + 4000
  let D := Icc (10: ℝ) (15: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (10: ℝ) (15: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 648) (Icc (6: ℝ) (7: ℝ)) := by
example : MonotoneOn (fun x => 2*x^2 - 24*x + 648) (Icc (6:ℝ) (7:ℝ)) := …

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 70 * x + 245) (Icc (7: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 70 * x + 245
  let D := Icc (7: ℝ) (17: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (17: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 48 * x + 432) (Icc (6: ℝ) (7: ℝ)) := by
example : MonotoneOn (λ x => 4 * x ^ 2 - 48 * x + 432) (Icc (6 : ℝ) 7) := …

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (8: ℝ)) := by
  -- set up
  let f := fun x => 9 * x ^ 2 - 36 * x + 108
  let D := Icc (2:ℝ) (8:ℝ)

  -- convexity of the interval
  have hD : Convex ℝ D := convex_Icc (2:ℝ) (8:ℝ)

  -- the derivative is strictly positive on the interior (2,8)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and compute deriv
    dsimp [f]
    simp only [deriv_sub, deriv_add, deriv_const_mul, deriv_pow, deriv_mul, deriv_id,
               deriv_const]
    -- now we have deriv f x = 18*x - 36
    linarith [hx.1]

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    dsimp [f]
    continuity

  -- conclude monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 24 * x + 360) (Icc (6: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 24 * x + 360
  let D := Icc (6: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (6: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 40 * x + 320) (Icc (4: ℝ) (14: ℝ)) := by
  let f := fun x : ℝ => 5 * x ^ 2 - 40 * x + 320
  let D := Icc (4 : ℝ) (14 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 4 14
  -- Show the derivative is strictly positive on the interior (4,14)
  have hderiv : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    simp only [f]
    dsimp
    have : deriv (fun y => 5 * y ^ 2 - 40 * y + 320) x = 10 * x - 40 := by
      simp [deriv_add, deriv_mul, deriv_pow'', deriv_const, deriv_id'']; ring
    rw [this]
    -- interior_Icc 4 14 is {x | 4 < x ∧ x < 14}
    rw [interior_Icc] at hx
    -- on (4,14) we have 10*x - 40 > 0
    linarith
  -- f is continuous on D (polynomials are continuous)
  have hcont : ContinuousOn f D := by
    simp [f]; continuity
  -- apply the standard theorem
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 140 * x + 4410) (Icc (7: ℝ) (16: ℝ)) := by
  -- the interval is convex
  have hconvex : Convex ℝ (Icc (7:ℝ) 16) := convex_Icc _ _

  -- compute the derivative in closed‐form
  have hderiv : ∀ x, deriv (fun x => 10*x^2 - 140*x + 4410) x = 20*x - 140 := by
    intro x; simp

  -- show the derivative is strictly positive on the *interior* (7,16)
  have hpos :
    ∀ x ∈ interior (Icc (7:ℝ) 16), 0 < deriv (fun x => 10*x^2 - 140*x + 4410) x := by
  intro x hx
  -- by `hderiv` the lhs is `20*x - 140`, and on (7,16) that is > 20*7 - 140 = 0
  simpa [hderiv x] using by linarith [hx.1]

  -- f is a polynomial, hence continuous on the closed interval
  have hcont : ContinuousOn (fun x => 10*x^2 - 140*x + 4410) (Icc (7:ℝ) 16) := by
    continuity

  -- assemble into the usual monotonicity lemma
  exact (strictMonoOn_of_deriv_pos hconvex hcont hpos).MonotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 24 * x + 48) (Icc (2: ℝ) (12: ℝ)) := by
  let f := fun x => 6*x^2 - 24*x + 48
  let D := Icc (2:ℝ) 12

  -- The domain is convex
  have hD : Convex ℝ D := convex_Icc (2:ℝ) 12

  -- Compute the derivative and show it's strictly positive on the interior
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    -- Unfold f and simplify the derivative
    unfold f
    simp [deriv_sub, deriv_add, deriv_mul, deriv_pow]
    -- Now the goal is `12 * x - 24 > 0`
    ring
    -- Interior of Icc [2,12] is Ioo (2,12)
    rw [interior_Icc] at hx
    -- From 2 < x we conclude 12*x - 24 > 0
    nlinarith [ (Set.mem_Ioo.1 hx).1 ]

  -- f is continuous on D (polynomials are continuous)
  have hf : ContinuousOn f D := by continuity

  -- Finally apply the standard theorem
  exact (strictMonoOn_of_deriv_pos hD hf hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 32 * x + 64) (Icc (2: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 32 * x + 64
  let D := Icc (2: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (9: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 160 * x + 4000) (Icc (10: ℝ) (17: ℝ)) := by
  let f := fun x => 8*x^2 - 160*x + 4000
  let D := Icc 10 17
  -- D is convex
  have hconv : Convex ℝ D := convex_Icc _ _
  -- f is continuous on D (polynomials are continuous)
  have hcont : ContinuousOn f D := by continuity
  -- compute the derivative and show it is strictly positive on (10,17)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    rintro x ⟨h₀, h₁⟩
    dsimp [f]
    -- simp will use deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id
    simp [deriv]
    -- now the goal is 16 * x - 160 > 0
    linarith [h₀]
  -- conclude monotonicity
  exact (strictMonoOn_of_deriv_pos hconv hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 48) (Icc (2: ℝ) (3: ℝ)) := by
  -- abbreviate the function and the domain
  let f := λ x : ℝ => 3 * x ^ 2 - 12 * x + 48
  let D := Icc (2 : ℝ) 3

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc (2 : ℝ) 3

  -- the derivative is strictly positive on the interior
  have hf' : ∀ x h : x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and compute the derivative
    unfold f
    -- break up the derivative
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- now we have deriv f x = 6 * x - 12
    ring
    -- use that x ∈ (2,3) so x > 2
    rw [interior_Icc] at hx
    linarith [hx.1]

    -- these last lines discharge all the differentiability side‐goals
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
                           (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))

  -- f is continuous on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.mul continuous_const (Continuous.pow continuous_id _))
        (Continuous.mul continuous_const (Continuous.id)))
      continuous_const).continuousOn

  -- now apply the strict‐monotonicity‐from‐derivative theorem
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 36 * x + 108) (Icc (3: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 6 * x ^ 2 - 36 * x + 108
  let D := Icc (3: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (3: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 224) (Icc (2: ℝ) (6: ℝ)) := by
  let f := fun x => 7 * x^2 - 28 * x + 224
  let D := Icc (2 : ℝ) (6 : ℝ)
  have hD : Convex ℝ D := convex_Icc _ _
  have hcont : ContinuousOn f D := by continuity
  have hderiv : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- unfold f and compute deriv f x = 14*x - 28
    dsimp [f]
    simp [deriv_mul, deriv_pow'', deriv_const, deriv_id'', deriv_neg]
    ring
    -- on the interior we have 2 < x, so 14*x - 28 = 14*(x - 2) > 0
    have : 14*x - 28 = 14 * (x - 2) := by ring
    simpa [this] using mul_pos (by norm_num) (sub_pos.2 (hx.1 : 2 < x))
  -- strict positivity of the derivative on a convex set gives strict monotonicity,
  -- hence monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 2025) (Icc (9: ℝ) (10: ℝ)) := by
example : MonotoneOn (λ x => 5 * x ^ 2 - 90 * x + 2025) (Icc (9: ℝ) (10: ℝ)) := …

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 36 * x + 108) (Icc (2: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 36 * x + 108
  let D := Icc (2: ℝ) (10: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (10: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 1176) (Icc (7: ℝ) (11: ℝ)) := by
  -- Define the function and the domain
  let f := fun x : ℝ => 6 * x ^ 2 - 84 * x + 1176
  let D := Icc (7:ℝ) (11:ℝ)

  -- The interval is convex
  have hD : Convex ℝ D := convex_Icc 7 11

  -- Compute the derivative and show it is strictly positive on the interior of D
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- Unfold f and compute deriv f x
    unfold f
    have : deriv f x = 12 * x - 84 := by
      simp only [deriv_add, deriv_add, deriv_mul, deriv_pow'', deriv_id'', deriv_const]
      ring
    -- Rewrite and use the fact that x ∈ (7,11)
    rw [this]
    rw [interior_Icc] at hx
    -- 12*x - 84 > 12*7 - 84 = 0
    linarith

  -- f is a polynomial, hence continuous on D
  have hf : ContinuousOn f D := by
    continuity

  -- Conclude monotonicity from strict positivity of the derivative
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 54 * x + 162) (Icc (3: ℝ) (10: ℝ)) := by
  let f := λ x => 9*x^2 - 54*x + 162
  let D := Icc (3:ℝ) 10

  -- the domain is a convex set
  have hD : Convex ℝ D := convex_Icc 3 10

  -- compute the derivative once and for all
  have hder : ∀ x, deriv f x = 18*x - 54 := by
    intro x; dsimp [f]; ring

  -- prove the derivative is strictly positive on the interior (3,10)
  have hpos : ∀ x hx, 0 < deriv f x := fun x hx => by
    -- rewrite down to 18*x - 54 and use x>3
    rw [hder x]
    have : x > 3 := hx.1
    linarith

  -- f is continuous on the closed interval
  have hcont : ContinuousOn f D := by
    continuity

  -- apply the strict‐derivative test
  exact (strictMonoOn_of_deriv_pos hD hcont hpos).monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 108 * x + 324) (Icc (6: ℝ) (13: ℝ)) := by
  -- Set up notation
  let f := fun x : ℝ => 9 * x ^ 2 - 108 * x + 324
  let D := Icc (6 : ℝ) (13 : ℝ)

  -- D is convex
  have hD : Convex ℝ D :=
    convex_Icc (6 : ℝ) (13 : ℝ)

  -- f is continuous on D (polynomials are continuous)
  have hcont : ContinuousOn f D := by
    continuity

  -- Compute the derivative and show it is positive on the interior of D
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x = 18 * x - 108
    have : deriv f x = 18 * x - 108 := by
      -- simp will discharge all the deriv_xxx lemmas for polynomials
      simp [f, deriv]
    -- rewrite and conclude positivity using 6 < x < 13
    rwa [this] at hx
    linarith

  -- Now apply the strict-monotonicity criterion
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 12) (Icc (1: ℝ) (5: ℝ)) := by
example : MonotoneOn (λ x : ℝ => 2 * x ^ 2 - 4 * x + 12) (Icc 1 5) := …

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 10 * x + 10) (Icc (1: ℝ) (2: ℝ)) := by
  let f := λ x => 5 * x ^ 2 - 10 * x + 10
  let D := Icc (1 : ℝ) (2 : ℝ)
  have hD : Convex ℝ D := convex_Icc _ _
  -- compute the derivative
  have hderiv : ∀ x ∈ interior D, deriv f x = 10 * x - 10 := by
    intro x hx
    dsimp [f]
    simp [deriv_mul, deriv_pow'', deriv_id'']
    ring
  -- on (1,2), 10*x - 10 > 0
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    rw [hderiv x hx]
    linarith [hx.1]
  -- f is a polynomial, hence continuous on D
  have hf : ContinuousOn f D := by
    continuity
  -- now apply the standard strict-derivative criterion
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 12) (Icc (1: ℝ) (6: ℝ)) := by
  let f := fun x => 6*x^2 - 12*x + 12
  let D := Icc (1 : ℝ) 6
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 1 6
  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn
  -- f is differentiable at every point of D (in particular on the interior)
  have hdiff : ∀ x _ : x ∈ D, DifferentiableAt ℝ f x := by
    intro x _
    simp [f]
    apply DifferentiableAt.add
      (DifferentiableAt.add
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
        (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)))
      (differentiableAt_const _)
  -- the derivative is 12*x - 12, which is > 0 for x in the interior (1,6)
  have hder_pos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- interior_Icc tells us x ∈ Ioo 1 6
    have ⟨h1, _⟩ := mem_interior_Icc.1 hx
    -- compute deriv f x = 12*x - 12
    have hder : deriv f x = 12 * x - 12 := by simp [f]
    -- 12*(x - 1) > 0 since x > 1
    simpa [hder] using by linarith [h1]
  -- now apply the standard strictMonoOn_of_deriv_pos and then .monotoneOn
  apply (strictMonoOn_of_deriv_pos hD hcont hdiff hder_pos).monotoneOn
#align my_example my_example  -- you can remove this in your own file

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 768) (Icc (4: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 768
  let D := Icc (4: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 12 * x + 24) (Icc (1: ℝ) (9: ℝ)) := by
  -- abbreviations
  let f := fun x : ℝ => 6*x^2 - 12*x + 24
  let D := Icc (1:ℝ) 9

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute the derivative and show it is strictly positive on the interior
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- deriv (6*x^2 - 12*x + 24) = 12*x - 12
    have : deriv (fun x => 6*x^2 - 12*x + 24) x = 12*x - 12 := by
      simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow'', deriv_id'']; ring
    -- substitute and finish with linarith, using x > 1
    simpa [this] using by linarith [hx.1]

  -- f is continuous on D (the tactic `continuity` can discharge this)
  have hcont : ContinuousOn f D := by continuity

  -- apply the standard strict-monotonicity-from-positive-derivative lemma
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 50 * x + 750) (Icc (5: ℝ) (9: ℝ)) := by

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 140 * x + 4200) (Icc (10: ℝ) (13: ℝ)) := by
  let f := λ x : ℝ => 7 * x ^ 2 - 140 * x + 4200
  let D := Icc (10:ℝ) (13:ℝ)

  -- The domain is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (10:ℝ) (13:ℝ)

  -- The derivative is positive on the interior (10,13)
  have hderiv_pos : ∀ x (hx : x ∈ interior D), 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- compute the derivative
    simp only [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    ring
    -- interior Icc gives 10 < x ∧ x < 13
    rw [interior_Icc] at hx
    -- since x > 10, we get 14*x - 140 > 0
    linarith [hx.1]

  -- f is continuous on [10,13]
  have hcont : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- conclude monotonicity from strict monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 100 * x + 2000) (Icc (5: ℝ) (10: ℝ)) := by
  let f := λ x : ℝ ↦ 10 * x ^ 2 - 100 * x + 2000
  let D := Icc (5: ℝ) (10: ℝ)
  have hD : Convex ℝ D := by
    apply convex_Icc (5: ℝ) (10: ℝ)
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    -- compute the derivative:  deriv f x = 20*x - 100
    simp [deriv_add, deriv_mul, deriv_const, deriv_pow'', deriv_id'']
    rw [interior_Icc] at hx
    -- on (5,10), 20*x - 100 > 20*5 - 100 = 0
    linarith [hx.1]
  have hf : ContinuousOn f D := by
    -- polynomials are continuous
    have h_cont : Continuous f := by
      continuity
    exact h_cont.continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 160 * x + 1920) (Icc (8: ℝ) (15: ℝ)) := by
  -- define f and the domain D
  let f := fun x : ℝ => 10*x^2 - 160*x + 1920
  let D := Icc (8 : ℝ) (15 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (8:ℝ) (15:ℝ)

  -- show f' (the derivative) is strictly positive on the interior of D
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- compute the derivative
    simp [deriv_add, deriv_sub, deriv_mul, deriv_pow, deriv_const, deriv_id]
    -- now the goal is `0 < 20*x - 160`
    have h : 20*x - 160 = 20*(x - 8) := by ring
    rw [h]
    -- use that x ∈ interior D gives 8 < x
    apply mul_pos
    · norm_num                        -- 0 < 20
    · apply sub_pos.2 hx.1            -- 0 < x - 8

  -- f is continuous on D (a polynomial is continuous)
  have hf : ContinuousOn f D := by continuity

  -- conclude monotonicity from strict positivity of the derivative
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 4050) (Icc (9: ℝ) (11: ℝ)) := by
  -- set up
  let f := λ x : ℝ => 5 * x ^ 2 - 90 * x + 4050
  let D := Icc (9 : ℝ) 11

  -- the interval is convex
  have hD : Convex ℝ D := by
    apply convex_Icc _ _

  -- the derivative is positive on the interior (9,11)
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    -- compute deriv
    unfold f
    simp only [deriv_add, deriv_sub, deriv_mul, deriv_pow'', deriv_id'', deriv_const] at *
    -- now deriv f x = 10 * x - 90
    ring
    -- interior D = (9,11)
    rw [interior_Icc] at hx
    -- on (9,11) we have x > 9, so 10 * x - 90 > 10*9 - 90 = 0
    linarith [hx.1]

  -- f is continuous on D (polynomial ⇒ continuous)
  have hf : ContinuousOn f D := by
    simp only [f]
    continuity

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 180 * x + 6480) (Icc (9: ℝ) (18: ℝ)) := by
  let f := λ x : ℝ, 10 * x ^ 2 - 180 * x + 6480
  let D := Icc (9 : ℝ) (18 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := by
    apply convex_Icc (9 : ℝ) (18 : ℝ)

  -- the derivative of f is 20*x - 180, which is positive on the interior (9,18)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute the derivative
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- now use interior_Icc to get 9 < x
    rw [interior_Icc] at hx
    -- conclude positivity
    linarith [hx.1]
    -- the chain of differentiability proofs
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact differentiableAt_const _

  -- f is continuous on D
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.sub
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const).continuousOn

  -- apply the strict-monotonicity criterion
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 32 * x + 512) (Icc (8: ℝ) (14: ℝ)) := by
  let f := λ x : ℝ ↦ 2 * x ^ 2 - 32 * x + 512
  let D := Icc (8: ℝ) (14: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (14: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 70) (Icc (1: ℝ) (4: ℝ)) := by
f : ℝ → ℝ   := λ x => 10*x^2 - 20*x + 70
D := Icc (1:ℝ) 4

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 14 * x + 63) (Icc (1: ℝ) (3: ℝ)) := by
  -- abbreviations
  let f : ℝ → ℝ := λ x => 7 * x^2 - 14 * x + 63
  let D := Icc (1:ℝ) (3:ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- polynomial continuity
    simp [f]
    apply (Continuous.add
             (Continuous.add
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- the derivative is 14*x - 14, which is strictly positive on the interior (1,3)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x
    dsimp [f]
    simp [deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring
    -- now use x ∈ (1,3) to show 14*x - 14 > 0
    rw [interior_Icc] at hx
    linarith [hx.1]
    -- supplying the missing differentiability proofs
    all_goals
      try exact differentiableAt_const _
      <|> try exact differentiableAt_id
      <|> try exact differentiableAt_pow _
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      <|> try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
      <|> try exact DifferentiableAt.add
            (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _))
            (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))

  -- conclude monotonicity from positivity of the derivative
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 84 * x + 882) (Icc (7: ℝ) (11: ℝ)) := by
  let f := fun x => 6 * x ^ 2 - 84 * x + 882
  let D := Icc (7 : ℝ) (11 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (7 := rfl) (11 := rfl)

  -- show f′(x) > 0 on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute the derivative by `simp` + `ring`
    unfold f
    have deriv_eq : deriv (fun x => 6 * x ^ 2 - 84 * x + 882) x = 12 * x - 84 := by
      simp [deriv, deriv_add, deriv_mul, deriv_pow, deriv_id, deriv_const]
      ring
    rw [deriv_eq]
    -- now x ∈ interior (Icc 7 11) gives 7 < x
    rw [interior_Icc] at hx
    have h7x : 7 < x := hx.1
    -- conclude 12*x - 84 > 0
    linarith

  -- f is continuous on D (it is a polynomial)
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const).continuousOn

  -- apply the strict-monotonicity criterion
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 16 * x + 224) (Icc (4: ℝ) (8: ℝ)) := by
f x = 2*x^2 - 16*x + 224

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1050) (Icc (5: ℝ) (7: ℝ)) := by
  let f := λ x : ℝ ↦ 7 * x ^ 2 - 70 * x + 1050
  let D := Icc (5: ℝ) (7: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (5: ℝ) (7: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 90 * x + 1215) (Icc (9: ℝ) (17: ℝ)) := by
  let f := λ x : ℝ ↦ 5 * x ^ 2 - 90 * x + 1215
  let D := Icc (9: ℝ) (17: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (9: ℝ) (17: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 144 * x + 2880
  let D := Icc (8: ℝ) (11: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (8: ℝ) (11: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 48 * x + 768) (Icc (4: ℝ) (8: ℝ)) := by
example : MonotoneOn (fun x => 6*x^2 - 48*x + 768) (Icc (4:ℝ) 8) := …

example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 144 * x + 2880) (Icc (8: ℝ) (14: ℝ)) := by
example : MonotoneOn (fun x ↦ 9 * x^2 - 144 * x + 2880) (Icc (8:ℝ) (14:ℝ)) := …

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 80 * x + 800) (Icc (4: ℝ) (8: ℝ)) := by
  -- Define the function and the interval
  let f := λ x : ℝ => 10 * x ^ 2 - 80 * x + 800
  let D := Icc (4:ℝ) (8:ℝ)

  -- The interval is convex
  have hD : Convex ℝ D := by
    apply convex_Icc

  -- We show the derivative is strictly positive on the interior (4,8)
  have hf' : ∀ x hx, 0 < deriv f x := by
    intros x hx
    -- compute the derivative
    dsimp [f]
    nth_rewrite 1 [deriv_sub]
    nth_rewrite 1 [deriv_add]  -- for the constant +800
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_const]
    ring
    -- now  deriv f x = 20*x - 80
    -- use x ∈ (4,8) to get positivity
    rw [interior_Icc] at hx
    have hpos : 0 < 20 * x - 80 := by linarith [hx.1]
    exact hpos

    -- Establish differentiability for each building block
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact differentiableAt_id

  -- The function is continuous on [4,8]
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
             (Continuous.sub
               (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
               (Continuous.mul continuous_const continuous_id))
             continuous_const).continuousOn

  -- Conclude monotonicity by the standard “strict derivative > 0” criterion
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 24 * x + 324) (Icc (3: ℝ) (7: ℝ)) := by
example : MonotoneOn (λ x => 4*x^2 - 24*x + 324) (Icc (3:ℝ) (7:ℝ)) := …

example: MonotoneOn (λ x ↦ 10 * x ^ 2 - 20 * x + 100) (Icc (1: ℝ) (6: ℝ)) := by
  -- abbreviate the function and domain
  let f := fun x => 10 * x ^ 2 - 20 * x + 100
  let D := Icc (1 : ℝ) (6 : ℝ)

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc (1 : ℝ) (6 : ℝ)

  -- show the derivative is strictly positive on the interior of D
  have hderiv_pos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x
    have : deriv f x = 20 * (x - 1) := by
      unfold f
      simp [deriv_pow'', deriv_mul, deriv_const, deriv_id'']
      ring
    rw [this]
    -- on the interior 1 < x, so x - 1 > 0
    have h1 : 1 < x := (interior_Icc.1 hx).1
    exact mul_pos (by norm_num : 0 < 20) (by linarith)

  -- f is continuous on D
  have hcont : ContinuousOn f D := (by continuity : Continuous f).continuousOn

  -- conclude monotonicity by the strict‐derivative test
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 98 * x + 1372) (Icc (7: ℝ) (12: ℝ)) := by
  -- abbreviate the function and domain
  let f := λ x : ℝ => 7 * x^2 - 98 * x + 1372
  let D := Icc 7 12

  -- the interval is convex
  have hD : Convex ℝ D := convex_Icc 7 12

  -- the derivative is 14*x - 98, which is positive on (7,12)
  have hder : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    unfold f
    -- computing the derivative
    simp [deriv]
    -- interior (Icc 7 12) is {x | 7 < x ∧ x < 12}
    rw [interior_Icc] at hx
    -- now 14*x - 98 > 14*7 - 98 = 0
    linarith

  -- f is a polynomial, hence continuous on D
  have hcont : ContinuousOn f D := by
    continuity

  -- apply the “strictMonoOn_of_deriv_pos” lemma and extract MonotoneOn
  exact (strictMonoOn_of_deriv_pos hD hcont hder).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 42 * x + 252) (Icc (3: ℝ) (12: ℝ)) := by
  let f := fun x => 7 * x ^ 2 - 42 * x + 252
  let D := Icc (3 : ℝ) (12 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 3 12

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- this follows immediately by `continuity`
    continuity

  -- the derivative of f is positive on the interior of D
  have hder_pos : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- unpack `x ∈ interior D`
    rw [interior_Icc] at hx
    -- compute the derivative
    have deriv_f : deriv f x = 14 * x - 42 := by
      simp [f, deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id]
      ring
    -- rewrite and finish by linarith, using `3 < x`
    rw [deriv_f]
    linarith [hx.1]

  -- now apply the general fact that a C⁰ function with strictly positive derivative
  -- on the interior of a convex set is strictly monotone, hence monotone
  exact (strictMonoOn_of_deriv_pos hD hcont hder_pos).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 112) (Icc (4: ℝ) (14: ℝ)) := by
  let f := λ x => 7*x^2 - 56*x + 112
  let D := Icc (4:ℝ) (14:ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 4 14
  -- compute the derivative of f, and show it is >0 on the interior  (4,14)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold f and simplify deriv f x
    dsimp [f]
    simp [deriv_mul, deriv_pow'', deriv_const, deriv_id'']
    -- now deriv f x = 14*x - 56, and `hx.1 : 4 < x`
    linarith
  -- f is continuous on the closed interval (it is a polynomial)
  have hf_cont : ContinuousOn f D := by
    continuity
  -- apply the strict‐monotonicity‐from‐positive‐derivative theorem
  exact (strictMonoOn_of_deriv_pos hD hf_cont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 2 - 4 * x + 8) (Icc (1: ℝ) (11: ℝ)) := by
  let f := λ x : ℝ => 2*x^2 - 4*x + 8
  let D := Icc (1:ℝ) (11:ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc (1:ℝ) (11:ℝ)
  -- compute the derivative and show it is strictly positive on (1,11)
  have h_deriv : ∀ x, deriv f x = 4*x - 4 := by
    intro x
    dsimp [f]
    simp [deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id]
    ring
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- interior (Icc 1 11) is { x | 1 < x ∧ x < 11 }
    rw [h_deriv]
    rw [interior_Icc] at hx
    linarith [hx.1]
  -- f is clearly continuous (it's a polynomial)
  have hf : ContinuousOn f D := by
    dsimp [f]
    continuity
  -- conclude strict‐monotonicity ⇒ monotonicity
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 70 * x + 1750) (Icc (5: ℝ) (8: ℝ)) := by
  let f := fun x => 7 * x^2 - 70 * x + 1750
  let D := Icc (5:ℝ) (8:ℝ)

  -- [5,8] is convex
  have hD : Convex ℝ D := convex_Icc 5 8

  -- f is a polynomial, hence continuous
  have hcont : ContinuousOn f D := by
    continuity

  -- On the open interval (5,8) we have
  --    deriv f x = 14*x - 70
  -- and since x > 5 this is strictly positive.
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intros x hx
    dsimp [f]
    -- simp away the usual derivative‐rules
    simp [deriv_add, deriv_sub, deriv_mul_const, deriv_pow, deriv_id, deriv_const]
    ring
    -- interior_Icc: interior D = (5,8)
    rw [interior_Icc] at hx
    linarith

  -- Apply the strict‐derivative criterion for strict monotonicity,
  -- then downgrade to monotonicity.
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 6 * x ^ 2 - 72 * x + 1296) (Icc (6: ℝ) (10: ℝ)) := by
  -- set up
  let f := λ x : ℝ => 6 * x ^ 2 - 72 * x + 1296
  let D := Icc (6 : ℝ) (10 : ℝ)
  have hD : Convex ℝ D := by
    apply convex_Icc (6 : ℝ) (10 : ℝ)

  -- show f′(x) > 0 on the interior (6,10)
  have hf' : ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    -- compute the derivative by repeated `nth_rewrite`
    unfold f
    nth_rewrite 1 [deriv_add]    -- (6*x^2)′ + (−72*x + 1296)′
    nth_rewrite 1 [deriv_add]    -- (6*x^2)′ + (−72*x)′ + (1296)′
    -- 6*x^2
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    -- −72*x
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    -- 1296
    nth_rewrite 1 [deriv_const]
    ring
    -- now use x > 6 to conclude 12*x - 72 > 0
    rw [interior_Icc] at hx
    linarith

    -- supply differentiability facts for each subterm
    all_goals
      try exact differentiableAt_const _
      try exact differentiableAt_pow _
      try exact differentiableAt_id
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
      try exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
      try exact DifferentiableAt.add _ _

  -- f is continuous on the closed interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.mul continuous_const (Continuous.pow continuous_id _))
        (Continuous.mul continuous_const continuous_id))
      continuous_const).continuousOn

  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 8 * x ^ 2 - 64 * x + 128) (Icc (4: ℝ) (12: ℝ)) := by
  let f := λ x : ℝ ↦ 8 * x ^ 2 - 64 * x + 128
  let D := Icc (4: ℝ) (12: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (4: ℝ) (12: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
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
    rw [interior_Icc] at hx
    linarith [hx.1]
    exact differentiableAt_const _
    exact differentiableAt_id
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
    exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)) (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id))
    exact differentiableAt_const _
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 32 * x + 192) (Icc (4: ℝ) (13: ℝ)) := by
  let f := fun x => 4 * x^2 - 32 * x + 192
  let D := Icc (4 : ℝ) 13
  -- D is convex
  have hD : Convex ℝ D := convex_Icc _ _
  -- f is continuous on D (in fact polynomial)
  have hf : ContinuousOn f D := by continuity
  -- on the interior of D, deriv f x = 8*x - 32 > 0
  have hderiv : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- interior D = Ioo 4 13
    rw [interior_Icc] at hx
    -- compute the derivative
    simp [f]
    -- now 8*x - 32 > 0 because x > 4
    linarith [hx.1]
  -- conclude strict monotonicity ⇒ monotonicity
  exact (strictMonoOn_of_deriv_pos hD hf hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 18 * x + 189) (Icc (3: ℝ) (10: ℝ)) := by
  -- notation
  let f := fun x : ℝ => 3 * x ^ 2 - 18 * x + 189
  let D := Icc (3:ℝ) 10

  -- D is convex
  have hD : Convex ℝ D := convex_Icc 3 10

  -- f is continuous on D
  have hcont : ContinuousOn f D := by
    -- polynomial → continuous → continuousOn
    continuity

  -- the derivative of f is 6*x - 18, which is > 0 on the interior (3,10)
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- unfold the definition of deriv on polynomials
    simp [deriv, deriv_const, deriv_mul, deriv_pow'']
    -- now deriv f x = 6*x - 18
    norm_num
    -- since x ∈ interior D, we have 3 < x < 10, so 6*x - 18 > 0
    rcases interior_Icc.1 hx with ⟨h3, h10⟩
    linarith

  -- apply the mean‐value theorem lemma for strict monotonicity
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 8 * x + 12) (Icc (1: ℝ) (9: ℝ)) := by
  let f := λ x:ℝ, 4*x^2 - 8*x + 12
  let D := Icc (1:ℝ) (9:ℝ)
  -- [1,9] is convex
  have hD : Convex ℝ D := convex_Icc (1:ℝ) (9:ℝ)
  -- compute the derivative and show it is positive on (1,9)
  have hderiv : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- simp all the derivs away, then ring
    simp [deriv] at *
    ring at *
    -- we now have `deriv f x = 8*(x-1)`, and `x>1` from `hx.1`
    simpa [interior_Icc] using mul_pos (by norm_num) (sub_pos.2 hx.1)
  -- f is obviously continuous on [1,9]
  have hcont : ContinuousOn f D := by
    dsimp [f]
    continuity
  -- Finally apply the strict‐monotonicity‐by‐positive‐derivative theorem.
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 126 * x + 5670) (Icc (9: ℝ) (16: ℝ)) := by
  let f := λ x : ℝ => 7 * x ^ 2 - 126 * x + 5670
  let D := Icc (9 : ℝ) (16 : ℝ)
  have hD : Convex ℝ D := convex_Icc 9 16
  -- f is a polynomial, hence continuous on the closed interval D
  have hf : ContinuousOn f D := by
    simp [f]
    apply
      (Continuous.add
        (Continuous.add
          (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
          (Continuous.mul continuous_const continuous_id))
        continuous_const)
      .continuousOn
  -- compute the derivative and show it is strictly positive on the interior (9,16)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    simp [f]  -- uses deriv_add, deriv_mul, deriv_pow, deriv_const, deriv_id
    -- now `deriv f x = 14*x - 126`, and on x>9 we have 14*x - 126 > 0
    linarith [hx.1]
  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 5 * x ^ 2 - 60 * x + 1080) (Icc (6: ℝ) (8: ℝ)) := by
  -- set up
  let f := fun x : ℝ => 5 * x^2 - 60 * x + 1080
  let D := Icc (6 : ℝ) (8 : ℝ)

  -- D is convex
  have hD : Convex ℝ D := convex_Icc (6 : ℝ) (8 : ℝ)

  -- show the derivative is strictly positive on the interior
  have hf' : ∀ x hx, 0 < deriv f x := by
    intro x hx
    -- derivative! will compute λ x, 10*x - 60
    derivative!
    -- on (6,8) we have x > 6, so 10*x - 60 > 0
    linarith [hx.1]

  -- f is continuous on D (in fact everywhere)
  have hf : ContinuousOn f D := by
    -- the continuity tactic solves polynomials instantly
    continuity

  -- conclude
  exact (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 4 * x ^ 2 - 40 * x + 300) (Icc (5: ℝ) (7: ℝ)) := by
  -- set up notation
  let f := λ x : ℝ => 4 * x ^ 2 - 40 * x + 300
  let D := Icc (5 : ℝ) (7 : ℝ)

  -- the domain is convex
  have hD : Convex ℝ D := by
    apply convex_Icc

  -- show the derivative is strictly positive on the interior
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- compute deriv f x = 8 * x - 40
    unfold f
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_add]
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_pow'']
    nth_rewrite 1 [deriv_id'']
    nth_rewrite 1 [deriv_mul]
    nth_rewrite 1 [deriv_const]
    nth_rewrite 1 [deriv_id'']
    ring
    -- on (5,7) we have x > 5, so 8*x - 40 > 8*5 - 40 = 0
    rw [interior_Icc] at hx
    linarith [hx.1]

  -- f is continuous on the whole interval
  have hf : ContinuousOn f D := by
    simp [f]
    apply (Continuous.add
      (Continuous.add
        (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) 2))
        (Continuous.mul (continuous_const) continuous_id))
      (continuous_const)).continuousOn

  -- conclude monotonicity from derivative positivity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 48 * x + 576) (Icc (8: ℝ) (11: ℝ)) := by
  -- abbreviate
  let f := fun x => 3*x^2 - 48*x + 576
  let D := Icc (8:ℝ) 11

  -- [8,11] is convex
  have hD : Convex ℝ D := convex_Icc _ _

  -- compute the derivative
  have deriv_f : ∀ x, deriv f x = 6*x - 48 := by
    intro x
    simp [f, deriv_add, deriv_mul, deriv_const, deriv_pow, deriv_id]

  -- on the interior (8,11) we have x>8 ⇒ 6*x-48>0
  have hderiv_pos : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    -- rewrite the derivative and use `interior_Icc`
    rw [deriv_f x]
    rwa [interior_Icc] at hx
      with ⟨hx₁, _⟩
    -- now `linarith` closes 6*x - 48 > 0 since hx₁ : 8 < x

  -- f is continuous on [8,11] (it is a polynomial)
  have hcont : ContinuousOn f D := by
    simp [f]
    apply
      ( Continuous.add
          (Continuous.add
            (Continuous.mul continuous_const (Continuous.pow continuous_id 2))
            (Continuous.mul continuous_const continuous_id))
          continuous_const
      ).continuousOn

  -- conclude by the standard “strict mono from positive derivative” lemma
  change MonotoneOn f D
  exact (strictMonoOn_of_deriv_pos hD hcont hderiv_pos).monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 28 * x + 168) (Icc (2: ℝ) (10: ℝ)) := by
  let f := fun x : ℝ => 7 * x^2 - 28 * x + 168
  let D := Icc (2 : ℝ) (10 : ℝ)
  -- D is convex
  have hD : Convex ℝ D := convex_Icc 2 10
  -- show f' (x) = 14*x - 28 and that is > 0 on the interior (2,10)
  have hf' : ∀ x ∈ interior D, 0 < deriv f x := by
    intro x hx
    dsimp [f]
    -- use the basic deriv lemmas
    simp [deriv_add, deriv_sub, deriv_mul, deriv_const, deriv_pow, deriv_id]
    ring
    -- now  deriv f x = 14*x - 28
    rw [interior_Icc] at hx
    -- on (2,10) we have 14*x - 28 > 14*2 - 28 = 0
    linarith
  -- f is a polynomial, hence continuous on D
  have hf : ContinuousOn f D := by
    continuity
  -- conclude monotonicity
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 7 * x ^ 2 - 56 * x + 336) (Icc (4: ℝ) (8: ℝ)) := by
example : MonotoneOn (λ x => 7 * x^2 - 56 * x + 336) (Icc (4:ℝ) 8) := …

