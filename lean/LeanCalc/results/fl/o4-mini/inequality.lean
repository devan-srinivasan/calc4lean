import Mathlib
open Real

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 18) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 2 * q x > 12 * x := by
  -- set up f and the domain D = [0,1]
  let f := fun t => p t + 2 * q t - 12 * t
  let D := Icc (0 : ℝ) 1

  -- check f(0) > 0:
  have f0_pos : f 0 > 0 := by
    simp [f, h0.left]
    -- f 0 = p 0 + 2 q 0 = q 0 * (1 + 2) = 3 * q 0 > 0
    rw [← one_add_mul]
    exact mul_pos (by norm_num) h0.right

  -- prove f is monotone on [0,1] by checking f' ≥ 0 on the interior
  have mono : MonotoneOn f D := by
    -- f is everywhere differentiable
    have hfd : Differentiable ℝ f := by
      simp only [f]
      exact (hpDeriv.add (hqDeriv.const_mul _)).sub (differentiable_id.const_mul _)
    have hfd_on : DifferentiableOn ℝ f (interior D) :=
      hfd.differentiableOn.mono interior_subset
    have hcont : ContinuousOn f D := hfd.continuous.continuousOn

    -- on (0,1) we show f' ≥ 0
    have deriv_nonneg : ∀ y ∈ interior D, deriv f y ≥ 0 := by
      intro y hy
      -- p' y > 0 so we may divide by it
      have hp_pos : deriv p y > 0 := hP y
      have q'_eq : deriv q y = 18 / deriv p y := by
        have t : deriv p y * deriv q y = 18 ↔ deriv q y = 18 / deriv p y := by
          field_simp [hp_pos]
          ring
        exact (t.mp (hf' y))

      -- now compute f' y = p' y + 2*(18/p' y) - 12
      simp [f] at *
      simp_rw [deriv_sub, deriv_add, deriv_const_mul, q'_eq, deriv_const_mul, deriv_id']

      -- multiply by the positive factor p' y
      have step : 0 ≤ deriv p y * (deriv p y + 2*(18/deriv p y) - 12) := by
        apply mul_nonneg_iff_of_pos_left (le_of_lt hp_pos)
        -- square‐complete: p'^2 + 36 - 12 p' = (p' - 6)^2 ≥ 0
        have e1 : deriv p y * (deriv p y + 2*(18/deriv p y) - 12)
               = deriv p y ^ 2 + 36 - 12 * deriv p y := by
          field_simp [hp_pos]; ring
        have e2 : deriv p y ^ 2 + 36 - 12 * deriv p y = (deriv p y - 6) ^ 2 := by ring
        rw [e1, ← e2]
        exact sq_nonneg _

      -- conclude f' y ≥ 0
      simpa using (mul_nonneg_iff_of_pos_left (le_of_lt hp_pos)).mp step

    -- apply the derivative‐test monotonicity lemma
    exact monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hcont hfd_on deriv_nonneg

  -- now on [0,1], f x ≥ f 0 > 0
  have fx_pos : f x > 0 := by
    have hx0 : x ≥ 0 := (mem_Icc.mp hD).1
    have fx_ge₀ : f x ≥ f 0 := mono (by norm_num) hD hx0
    linarith [f0_pos, fx_ge₀]

  -- unpack f x > 0 into the desired inequality
  simp [f] at fx_pos
  linarith

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 8) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 2 * q x > 8 * x := by

  -- define the auxiliary function
  let f := λ t => p t + 2 * q t - 8 * t
  let D := Icc (0 : ℝ) 1

  -- show f(0) > 0
  have gt_zero : f 0 > 0 := by
    -- f 0 = p 0 + 2 * q 0 = q 0 + 2 * q 0 = 3 * q 0
    simp [f, h0.left]
    apply mul_pos
    · norm_num        -- 3 > 0
    · exact h0.right  -- q 0 > 0

  -- show f is monotone on [0,1]
  have monotonic : MonotoneOn f D := by
    -- f is globally differentiable
    have hfDiff : Differentiable ℝ f :=
      by simpa [f] using ((hpDeriv).add (hqDeriv.const_mul 2)).sub (differentiable_id.const_mul 8)
    -- hence differentiable on interior
    have hfDiffOn : DifferentiableOn ℝ f (interior D) :=
      hfDiff.differentiableOn.mono interior_subset
    -- and continuous on D
    have hfCont : ContinuousOn f D :=
      hfDiff.continuous.continuousOn

    -- show the derivative is ≥ 0 on the interior of D
    have der_nonneg : ∀ t ∈ interior D, deriv f t ≥ 0 := by
      intros t ht
      -- p' t > 0, so we may solve for deriv q t
      have hp_pos : deriv p t > 0 := hP t
      have hq_eq : deriv q t = 8 / deriv p t := by
        field_simp [hp_pos]; ring at hf' ⊢
        exact (hf' t).symm
      -- compute deriv f t
      -- deriv f t = deriv p t + 2 * deriv q t - 8
      have : deriv f t
        = deriv p t + 2 * (8 / deriv p t) - 8 := by
          simp [f, deriv_add, deriv_const_mul, deriv_sub, hq_eq, deriv_id'']
      rw [this]
      -- reduce to a square
      have sq_iff :
        0 ≤ deriv p t * (deriv p t + 2 * (8 / deriv p t) - 8)
        ↔ 0 ≤ deriv p t + 2 * (8 / deriv p t) - 8 :=
        mul_nonneg_iff_of_pos_left (hp_pos.le)
      have expand :
        deriv p t * (deriv p t + 2 * (8 / deriv p t) - 8)
        = deriv p t ^ 2 + 2*8 - 8 * deriv p t := by
        field_simp [hp_pos]; ring
      have square :
        deriv p t ^ 2 + 2*8 - 8 * deriv p t = (deriv p t - 4) ^ 2 := by ring
      -- conclude nonnegativity
      rwa [expand, square] at sq_iff
      exact sq_nonneg _

    -- apply the monotonicity criterion
    exact monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hfCont hfDiffOn der_nonneg

  -- now f x ≥ f 0 and f 0 > 0, so f x > 0
  have fx_pos : f x > 0 := by
    have x_ge_0 : 0 ≤ x := (mem_Icc.mp hD).1
    have fx_ge_f0 : f x ≥ f 0 :=
      monotonic (left_mem_Icc.mpr (by norm_num)) hD x_ge_0
    exact lt_of_lt_of_le gt_zero fx_ge_f0

  -- finish
  simpa [f] using fx_pos

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 98) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 2 * q x > 28 * x := by
  let f := (λ x ↦ p x + 2 * q x - 28 * x)
  let D := Icc (0: ℝ) (1: ℝ)
  have gt_zero: f 0 > 0 := by
    simp [f, h0.left]
    rw [← one_add_mul]
    apply mul_pos
    · norm_num
    · exact h0.right
  have monotonic: MonotoneOn f D := by
    have hfDifferentiableInReal : Differentiable ℝ f := by
        exact ((hpDeriv).add (hqDeriv.const_mul _)).sub (differentiable_id.const_mul _)
    have hfDifferentiable: DifferentiableOn ℝ f (interior D) := by
      exact hfDifferentiableInReal.differentiableOn.mono interior_subset
    have hfContinuous: ContinuousOn f D:= by
      exact hfDifferentiableInReal.continuous.continuousOn
    have interior_increasing: ∀ x2 ∈ interior D, deriv f x2 ≥ 0 := by
      intros x2 hx2
      let hpX2 := hP x2
      have reciprocal_deriv: deriv q x2 = 98 / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = 98 ↔ deriv q x2 = 98 / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + 2 * (98 / deriv p x2) - 28) ↔
        0 ≤ deriv p x2 + 2 * (98 / deriv p x2) - 28 := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + 2 * (98 / deriv p x2) - 28)
              = deriv p x2 ^ 2 + 2 * 98 - 28 * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + 2 * 98 - 28 * deriv p x2 = (deriv p x2 - 14) ^ 2 := by ring
      have simplify: deriv p x2 + 2 * (98 / deriv p x2) - 28 * (fun x2 ↦ 1) x = deriv p x2 + 2 * (98 / deriv p x2) - 28 := by ring
      rw [quad_eq, quad_sq] at sq_iff
      rw [simplify]
      exact sq_iff.mp (by apply sq_nonneg)
      exact differentiableAt_id
      exact hqDeriv x2
      exact hpDeriv x2
      exact DifferentiableAt.const_mul (hqDeriv x2) _
      exact DifferentiableAt.add (hpDeriv x2) (DifferentiableAt.const_mul (hqDeriv x2) _)
      exact DifferentiableAt.const_mul differentiableAt_id _
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0: ℝ) 1) (hfContinuous) (hfDifferentiable) (interior_increasing)
  have f_pos: f x > 0 := by
    have x_pos: x ≥ 0 := by
      apply (mem_Icc.mp hD).1
    have fx_gt_f_zero: f x ≥ f 0 := by
      apply monotonic (left_mem_Icc.mpr (by norm_num)) hD
      exact x_pos
    apply lt_of_lt_of_le gt_zero fx_gt_f_zero
  have equiv: p x + 2 * q x > 28 * x ↔ p x + 2 * q x - 28 * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 75) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 3 * q x > 30 * x := by
hf' : ∀ y, deriv p y * deriv q y = 75,
k   = 3,
t   = 30

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 75) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 3 * q x > 30 * x := by
  let f := (λ x ↦ p x + 3 * q x - 30 * x)
  let D := Icc (0: ℝ) (1: ℝ)
  have gt_zero: f 0 > 0 := by
    simp [f, h0.left]
    rw [← one_add_mul]
    apply mul_pos
    · norm_num
    · exact h0.right
  have monotonic: MonotoneOn f D := by
    have hfDifferentiableInReal : Differentiable ℝ f := by
        exact ((hpDeriv).add (hqDeriv.const_mul _)).sub (differentiable_id.const_mul _)
    have hfDifferentiable: DifferentiableOn ℝ f (interior D) := by
      exact hfDifferentiableInReal.differentiableOn.mono interior_subset
    have hfContinuous: ContinuousOn f D:= by
      exact hfDifferentiableInReal.continuous.continuousOn
    have interior_increasing: ∀ x2 ∈ interior D, deriv f x2 ≥ 0 := by
      intros x2 hx2
      let hpX2 := hP x2
      have reciprocal_deriv: deriv q x2 = 75 / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = 75 ↔ deriv q x2 = 75 / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + 3 * (75 / deriv p x2) - 30) ↔
        0 ≤ deriv p x2 + 3 * (75 / deriv p x2) - 30 := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + 3 * (75 / deriv p x2) - 30)
              = deriv p x2 ^ 2 + 3 * 75 - 30 * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + 3 * 75 - 30 * deriv p x2 = (deriv p x2 - 15) ^ 2 := by ring
      have simplify: deriv p x2 + 3 * (75 / deriv p x2) - 30 * (fun x2 ↦ 1) x = deriv p x2 + 3 * (75 / deriv p x2) - 30 := by ring
      rw [quad_eq, quad_sq] at sq_iff
      rw [simplify]
      exact sq_iff.mp (by apply sq_nonneg)
      exact differentiableAt_id
      exact hqDeriv x2
      exact hpDeriv x2
      exact DifferentiableAt.const_mul (hqDeriv x2) _
      exact DifferentiableAt.add (hpDeriv x2) (DifferentiableAt.const_mul (hqDeriv x2) _)
      exact DifferentiableAt.const_mul differentiableAt_id _
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0: ℝ) 1) (hfContinuous) (hfDifferentiable) (interior_increasing)
  have f_pos: f x > 0 := by
    have x_pos: x ≥ 0 := by
      apply (mem_Icc.mp hD).1
    have fx_gt_f_zero: f x ≥ f 0 := by
      apply monotonic (left_mem_Icc.mpr (by norm_num)) hD
      exact x_pos
    apply lt_of_lt_of_le gt_zero fx_gt_f_zero
  have equiv: p x + 3 * q x > 30 * x ↔ p x + 3 * q x - 30 * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos

example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 75) (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p) (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 3 * q x > 30 * x := by
  -- 1) set up f and the interval D
  let f : ℝ → ℝ := fun t => p t + 3 * q t - 30 * t
  let D := Icc (0 : ℝ) 1

  -- 2) show f(0)>0
  have f0_pos : f 0 > 0 := by
    dsimp [f]
    -- f 0 = p 0 + 3 q 0 = q 0 + 3 q 0 = 4 q 0
    have : p 0 + 3 * q 0 = 4 * q 0 := by simp [h0.1]
    simpa [this] using mul_pos (by norm_num : 4 > 0) h0.2

  -- 3) f is differentiable on ℝ, hence continuous on D and differentiable on interior D
  have dif_f : Differentiable ℝ f := by
    dsimp [f]
    exact (hp.add (hq.const_mul 3)).sub (differentiable_id.const_mul 30)
  have cont_f_on : ContinuousOn f D := dif_f.continuous.continuousOn
  have dif_on : DifferentiableOn ℝ f (interior D) :=
    (dif_f.differentiableOn).mono interior_subset

  -- 4) show f' ≥ 0 on interior D
  have deriv_nonneg : ∀ t ∈ interior D, deriv f t ≥ 0 := by
    rintro t ⟨ht0, ht1⟩
    dsimp [f]
    -- substitute q' = 75 / p'
    have hq' : deriv q t = 75 / deriv p t := by
      simpa [hP t] using (hf' t)
    -- unfold deriv:
    simp [deriv_add, deriv_sub, deriv_const_mul, deriv_id, hq']
    -- now
    --   deriv f t = deriv p t + 3*(75/deriv p t) - 30
    -- one checks by field_simp+ring:
    have : deriv p t + 3*(75/deriv p t) - 30 = (deriv p t - 15)^2 / deriv p t := by
      field_simp [hP t]; ring
    rw [this]; clear this
    -- last bit: (p' - 15)^2 ≥ 0 and p'>0 ⇒ quotient ≥ 0
    apply div_nonneg
    · exact (hP t).le
    · exact sq_nonneg _

  -- 5) by monotoneOn_of_deriv_nonneg, f is monotone on D
  have f_mon : MonotoneOn f D :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) cont_f_on dif_on deriv_nonneg

  -- 6) apply monotonicity: f x ≥ f 0
  have f_ge_f0 : f x ≥ f 0 :=
    f_mon (mem_Icc.mpr ⟨by norm_num, by norm_num⟩) hD

  -- 7) conclusion
  linarith

