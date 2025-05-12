import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic
open Real
open Set

-- CONDITION-TYPE QUESTIONS
-- 17: The function $ h: \\mathbb{R} \\to \\mathbb{R} $ is differentiable and satisfies for every $ x $ the condition $ h(ax) = b h(x) $, where $ a $ and $ b $ are certain fixed real numbers and $ 0 \\neq |a| \\neq 1 $. Additionally, the function $ h $ is continuous at the point $ x = 0 $.\nProve that $ a = b $ and there exists a real number $ c $ such that $ h(x) = cx $."

-- 92: It is known about the functions $a(x)$ and $b(x)$ that $a(0)=b(0)>0$ and $a^{\\prime}(x) \\sqrt{b^{\\prime}(x)}=2$ for any $x \\in[0 ; 1]$. Prove that if $x \\in[0 ; 1]$, then $a(x)+8 b(x)>6 x$."

-- 107: It is known about the functions $p(x)$ and $q(x)$ that $p(0)=q(0)>0$ and $p^{\\prime}(x) \\sqrt{q^{\\prime}(x)}=\\sqrt{2}$ for any $x \\in[0 ; 1]$. Prove that if $x \\in[0 ; 1]$, then $p(x)+2 q(x)>3 x$."

-- 122: It is known about the functions $s(x)$ and $t(x)$ that $s(0)=t(0)>0$ and $s^{\\prime}(x) \\sqrt{t^{\\prime}(x)}=5$ for any $x \\in[0 ; 1]$. Prove that if $x \\in[0 ; 1]$, then $2 s(x)+5 t(x)>15 x$.

-- 137: For functions $f(x)$ and $g(x)$, it is known that $f(0)=g(0)>0$ and $f^{\\prime}(x) \\sqrt{g^{\\prime}(x)}=3$ for any $x \\in[0 ; 1]$. Prove that if $x \\in[0 ; 1]$, then $2 f(x)+3 g(x)>9 x$.

-- invented:
example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 1)
  (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p)
  (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 9 * q x > 6 * x := by
  let f := (λ x ↦ p x + 9 * q x - 6 * x)
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
      have reciprocal_deriv: deriv q x2 = 1 / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = 1 ↔ deriv q x2 = 1 / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + 9 * (1 / deriv p x2) - 6) ↔
        0 ≤ deriv p x2 + 9 * (1 / deriv p x2) - 6 := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + 9 * (1 / deriv p x2) - 6)
              = deriv p x2 ^ 2 + 9 - 6 * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + 9 - 6 * deriv p x2 = (deriv p x2 - 3) ^ 2 := by ring
      have simplify: deriv p x2 + 9 * (1 / deriv p x2) - 6 * (fun x2 ↦ 1) x = deriv p x2 + 9 * (1 / deriv p x2) - 6 := by ring
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
  have equiv: p x + 9 * q x > 6 * x ↔ p x + 9 * q x - 6 * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos

example: MonotoneOn (λ x ↦ x ^ 2) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ x ^ 2
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    intros x hx
    rw [interior_Icc] at hx
    exact hx.1
  have hf: ContinuousOn f D := by
    apply (continuous_pow 2).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    intros x hx
    rw [interior_Icc] at hx
    exact hx.1
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.mul (continuous_const) (continuous_pow 2)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 + 3) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 + 3
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    intros x hx
    rw [interior_Icc] at hx
    exact hx.1
  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.mul (continuous_const) (continuous_pow 2)) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 + 5 * x + 3) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 + 5 * x + 3
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    -- @bindu help me please
    -- Help Done
    intros x hx
    rw [interior_Icc] at hx
    rw [deriv_add]
    rw [deriv_const_mul]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_id'']
    ring_nf
    rcases hx with ⟨hx0, hx1⟩
    -- note that x * 6 < 6 since x < 1
    have h1 : 0 < x * 6 := mul_pos hx0 (by norm_num)
    have h2 : 0 < 5 + x * 6 := by linarith
    exact h2
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.const_mul (differentiableAt_pow _) _
    exact DifferentiableAt.const_mul differentiableAt_id _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (continuous_pow 2)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 3 + 5 * x ^ 2 + 8 * x + 3) (Icc (0: ℝ) (1: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 3 + 5 * x ^ 2 + 8 * x + 3
  let D := Icc (0: ℝ) (1: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (1: ℝ)
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
    have h0: 0 < 8 := by norm_num
    have h1: 0 < 10 * x := by linarith [hx.1]
    have h2: 0 < 9 * x^2 := by
      have power_pos: 0 < x^2 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h0, h1, h2]
    -- linarith [hx.1]
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
    apply (Continuous.add (Continuous.add (Continuous.add (Continuous.mul (continuous_const) (continuous_pow _)) (Continuous.mul (continuous_const) (continuous_pow _))) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 12) (Icc (2: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 12 * x + 12
  let D := Icc (2: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (3: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    intros x hx
    rw [deriv_sub]
    rw [deriv_const_mul]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_id'']
    ring
    rw [interior_Icc] at hx
    -- have h0: 0 < 8 := by norm_num
    -- have h1: 0 < 10 * x := by linarith [hx.1]
    -- have h2: 0 < 9 * x^2 := by
    --   have power_pos: 0 < x^2 := by
    --     apply pow_pos (hx.1)
    --   linarith [power_pos]
    linarith [hx.1]
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.const_mul (differentiableAt_pow _) _
    exact DifferentiableAt.const_mul differentiableAt_id _

example: MonotoneOn (λ x ↦ 3 * x ^ 2 - 12 * x + 12) (Icc (2: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 3 * x ^ 2 - 12 * x + 12
  let D := Icc (2: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (2: ℝ) (3: ℝ)
  have hf': ∀ x ∈ interior D, 0 < deriv f x := by
    simp [f]
    intros x hx
    rw [deriv_sub]
    rw [deriv_const_mul]
    rw [deriv_pow]
    rw [deriv_const_mul]
    rw [deriv_id'']
    ring
    rw [interior_Icc] at hx
    -- have h0: 0 < 8 := by norm_num
    -- have h1: 0 < 10 * x := by linarith [hx.1]
    -- have h2: 0 < 9 * x^2 := by
    --   have power_pos: 0 < x^2 := by
    --     apply pow_pos (hx.1)
    --   linarith [power_pos]
    linarith [hx.1]
    exact differentiableAt_id
    exact differentiableAt_pow _
    exact DifferentiableAt.const_mul (differentiableAt_pow _) _
    exact DifferentiableAt.const_mul differentiableAt_id _

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.sub (Continuous.mul (continuous_const) (continuous_pow _)) (Continuous.mul (continuous_const) (continuous_id))) (continuous_const)).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn

example: MonotoneOn (λ x ↦ 2 * x ^ 3 + 3 * x ^ 2 + 2 * x + 3) (Icc (0: ℝ) (5: ℝ)) := by
    let f := λ x : ℝ ↦ 2 * x ^ 3 + 3 * x ^ 2 + 2 * x + 3
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
        nth_rewrite 1 [deriv_id'']
        nth_rewrite 1 [deriv_const]

        ring
        rw [interior_Icc] at hx
        have h0: 0 < 3 := by norm_num
        have h1: 0 < 2 * x := by linarith [hx.1]

        have h2: 0 < 3 * x ^ 2 := by
            have power_pos: 0 < x ^ 2 := by
                apply pow_pos (hx.1)
            linarith [power_pos]

        have h3: 0 < 2 * x ^ 3 := by
            have power_pos: 0 < x ^ 3 := by
                apply pow_pos (hx.1)
            linarith [power_pos]
        linarith [h0, h1, h2, h3]
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

example (f : ℝ → ℝ) (x : ℝ) (s : Set ℝ)
  (h_ext : IsLocalExtrOn f x s)
  (h_diff : DifferentiableAt ℝ f x) :
  deriv f x = 0 := by
  apply IsLocalExtrOn.deriv_eq_zero h_ext h_diff


-- Tangent line equation problem
-- (fun p ↦ p.1 ^ 2 + p.2 ^ 2 - 25) = 0 is basically the equation of the curve
-- (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) is the equation of the tangent the the point (3,4) 
-- We are trying to prove that the equations are exactly the same
-- The proof should work for all polynomial type equations (so we can do circle, ellipse, parabolas)
example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) → (3 * x + 4 * y - 25 = 0) := by
  intro h
  rw [fderiv_sub, fderiv_add] at h
  simp at h

  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2) (x-3, y-4) (3, 4) = 6 * x - 18 := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2) = (fun x => x ^ 2) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    simp [fderiv_fst] --This is the part I would Ideally like to change. I.e. not use simp. But can't find how to do it without simp
    -- @Devan if you find a solution let me know
    ring
    exact differentiableAt_pow _
    exact differentiableAt_fst

  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.2 ^ 2) (x-3, y-4) (3, 4) = 8 * y - 32  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun y => y ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    simp [fderiv_snd]
    ring
    exact differentiableAt_pow _
    exact differentiableAt_snd

  rw [h1] at h
  rw [h2] at h
  ring_nf at h
  linarith
  exact differentiableAt_fst.pow _
  exact differentiableAt_snd.pow _
  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)
  exact differentiableAt_const _

-- DOMAIN / RANGE -TYPE QUESTIONS
-- 182: "Task 3. II variant.\n\nFor what values of the parameter $a$ does the function $y=\\frac{8}{x^{2}+4 x+44}$ increase on the interval $[a-3 ; 3 a]?$"

-- EXTRA
-- Prove that the function $f(x)=\\sin x+\\sin \\sqrt{2} x$ is non-periodic.


-- 1447: 6.46. Let the functions $\\alpha(x)$ and $\\beta(x)$ satisfy the following conditions:\n\n1) $\\alpha(x)$ and $\\beta(x)$ are $n$-times differentiable;\n\n2) $2 \\alpha^{(m)}\\left(x_{0}\\right)=\\beta^{(m)}\\left(x_{0}\\right)$, where $m=0,1, \\ldots, n-1$;\n3) $\\alpha^{(n)}(x)>\\beta^{(n)}(x)$ for $x>x_{0}$.\n\nThen the inequality $\\alpha(x)>\\beta(x)$ holds for $x>x_{0}$.",
-- "S o l u t i o n. Consider the function $f^{(n-1)}(x)=\\alpha^{(n-1)}(x)-$ $-\\beta^{(n-1)}(x)$ and apply Lagrange's theorem to it on the interval $\\left[x_{0} ; x\\right]: f^{(n-1)}(x)-f^{(n-1)}\\left(x_{0}\\right)=f^{(n)}(c)\\left(x-x_{0}\\right)$, by conditions 2) and 3) we obtain $f^{(n-1)}(x)>0$ for $x>x_{0}$. Similarly, we can prove that $f(x)>0$, or $\\alpha(x)>\\beta(x)$, for $x>x_{0}$.",

-- 1442: 6.48. Using the constancy of the derivative of the function $\\arcsin x + \\arccos x$ on the interval $x \\in [-1; 1]$, prove the validity of the equality $\\arcsin x + \\arccos x = \\pi / 2$.",
-- "Solution. We have for\n\n$$\nf(x)=\\arcsin x+\\arccos x f^{\\prime}(x)=\\frac{1}{\\sqrt{1-x^{2}}}-\\frac{1}{\\sqrt{1-x^{2}}}=0\n$$\n\nfor $x \\in(-1 ; 1)$, hence for $x \\in(-1 ; 1)$ the function $f(x)=$ $=\\arcsin x+\\arccos x=$ const and due to the continuity of this function on the interval $x \\in[-1 ; 1]$ we conclude that $f(x)=$ $=\\arcsin x+\\arccos x=$ const everywhere for $x \\in[-1 ; 1]$.\n\nAt the point $x=1$ we get $f(1)=\\arcsin 1+\\arccos 1=$ $=$ const $=\\pi / 2$.",

-- 77: "problem": "Task 3. II variant.\n\nFor what values of the parameter $a$ does the function $y=\\frac{8}{x^{2}+4 x+44}$ increase on the interval $[a-3 ; 3 a]?$",
--  "solution": "Solution. The function is increasing on the interval $(-\\infty ;-2]$. The function will be decreasing on the segment $[a-3 ; 3 a]$ under the conditions\n\n$\\left\\{\\begin{array}{l}3 a \\leq-2, \\\\ a-3<3 a\\end{array} \\Leftrightarrow \\quad-\\frac{3}{2}<a \\leq-\\frac{2}{3}\\right.$.\n\nAnswer: $a \\in\\left(-\\frac{3}{2} ;-\\frac{2}{3}\\right]$.
