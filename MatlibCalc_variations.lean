import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Real



theorem h0_0 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  -- Apply the derivative to each term separately using linearity
  rw [deriv_add, deriv_sub]
  -- Simplify the derivatives of constant multiples
  rw [deriv_const_mul, deriv_const_mul, deriv_const]
  -- Use basic derivative rules for powers and the identity function
  rw [deriv_pow, deriv_id'']
  -- Simplify constants and expressions
  simp
  -- Combine like terms
  ring

  have h01: DifferentiableAt ℝ (fun y => y) x0 := (hasFDerivAt_id x0).differentiableAt
  apply h01
  have h02: DifferentiableAt ℝ (fun x => x ^ 3) x0 := (hasDerivAt_pow _ x0).differentiableAt
  apply h02

  have h03: DifferentiableAt ℝ (fun x => 6 * x ^ 3) x0 := by
    apply DifferentiableAt.const_mul _ _
    apply (hasDerivAt_pow 3 x0).differentiableAt
  apply h03
  have h04: DifferentiableAt ℝ (HMul.hMul 9) x0 := by
    apply DifferentiableAt.const_mul _ _
    apply (hasFDerivAt_id x0).differentiableAt
  apply h04

  have h05: DifferentiableAt ℝ (fun x => 6 * x ^ 3) x0 := by
    apply DifferentiableAt.const_mul _ 6
    apply (hasDerivAt_pow 3 x0).differentiableAt
  have h06: DifferentiableAt ℝ (HMul.hMul 9) x0 := by
    apply DifferentiableAt.const_mul _ 9
    apply (hasFDerivAt_id x0).differentiableAt

  apply (DifferentiableAt.sub h05 h06)
  apply (hasDerivAt_const x0 4).differentiableAt

theorem h0_1 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  have h_identity_diff: DifferentiableAt ℝ (fun y => y) x0 :=
    (hasFDerivAt_id x0).differentiableAt
  have h_pow_diff (z:ℕ): DifferentiableAt ℝ (fun x => x ^ z) x0 :=
    (hasDerivAt_pow z x0).differentiableAt

  have h_const_mul_pow_diff(c:ℝ)(z:ℕ): DifferentiableAt ℝ (fun x => c * x ^ z) x0 := by
    apply DifferentiableAt.const_mul _ _
    apply h_pow_diff

  have h_const_mul_identity_diff(c:ℝ): DifferentiableAt ℝ (HMul.hMul c) x0 := by
    apply DifferentiableAt.const_mul _ _
    assumption

  -- Apply the derivative to each term separately using linearity
  rw [deriv_add, deriv_sub]
  -- Simplify the derivatives of constant multiples
  rw [deriv_const_mul, deriv_const_mul, deriv_const]
  -- Use basic derivative rules for powers and the identity function
  rw [deriv_pow, deriv_id'']
  -- Simplify constants and expressions
  simp
  -- Combine like terms
  ring

  apply h_identity_diff
  apply h_pow_diff
  apply h_const_mul_pow_diff
  apply h_const_mul_identity_diff
  apply DifferentiableAt.sub (h_const_mul_pow_diff 6 3) (h_const_mul_identity_diff 9)
  apply (hasDerivAt_const x0 4).differentiableAt


theorem h0_2 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by
  have h01: DifferentiableAt ℝ (fun y => y) x0 :=
    (hasFDerivAt_id x0).differentiableAt
  have h02: DifferentiableAt ℝ (fun x => x ^ 3) x0 :=
    (hasDerivAt_pow _ x0).differentiableAt
  --let h03 := DifferentiableAt.const_mul _ _

  have h03: DifferentiableAt ℝ (fun x => 6 * x ^ 3) x0 := by
    apply DifferentiableAt.const_mul _ _
    assumption
    -- apply (hasDerivAt_pow 3 x0).differentiableAt
  -- apply h03
  have h04: DifferentiableAt ℝ (HMul.hMul 9) x0 := by
    apply DifferentiableAt.const_mul _ _
    -- apply h01--(hasFDerivAt_id x0).differentiableAt
    assumption
  -- Apply the derivative to each term separately using linearity
  rw [deriv_add, deriv_sub] <;> try assumption
  -- Simplify the derivatives of constant multiples
  rw [deriv_const_mul, deriv_const_mul, deriv_const] <;> try assumption
  -- Use basic derivative rules for powers and the identity function
  rw [deriv_pow, deriv_id''] --<;> try assumption
  -- Simplify constants and expressions
  simp
  -- Combine like terms
  ring

  apply DifferentiableAt.sub <;> assumption
  apply (hasDerivAt_const x0 4).differentiableAt


theorem h0_3 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by
  have h01: DifferentiableAt ℝ (fun y => y) x0 :=
    (hasFDerivAt_id x0).differentiableAt
  have h02: DifferentiableAt ℝ (fun x => x ^ 3) x0 :=
    (hasDerivAt_pow _ x0).differentiableAt
  --let h03 := DifferentiableAt.const_mul _ _

  have h03: DifferentiableAt ℝ (fun x => 6 * x ^ 3) x0 := by
    apply DifferentiableAt.const_mul _ _
    assumption
    -- apply (hasDerivAt_pow 3 x0).differentiableAt
  -- apply h03
  have h04: DifferentiableAt ℝ (HMul.hMul 9) x0 := by
    apply DifferentiableAt.const_mul _ _
    -- apply h01--(hasFDerivAt_id x0).differentiableAt
    assumption
  -- Apply the derivative to each term separately using linearity
  rw [deriv_add, deriv_sub]
  -- Simplify the derivatives of constant multiples
  rw [deriv_const_mul, deriv_const_mul, deriv_const]
  -- Use basic derivative rules for powers and the identity function
  rw [deriv_pow, deriv_id''] --<;> try assumption
  -- Simplify constants and expressions
  simp
  -- Combine like terms
  ring

  apply h01
  apply h02
  apply h03
  apply h04
  apply DifferentiableAt.sub h03 h04
  apply (hasDerivAt_const x0 4).differentiableAt


theorem h0_4 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  rw [deriv_add]
  rw [deriv_sub]
  rw [deriv_const_mul]
  rw [deriv_const_mul]
  rw [deriv_id'']
  rw [deriv_pow]
  rw [deriv_const]
  ring
  exact differentiableAt_id
  exact differentiableAt_pow 3
  exact DifferentiableAt.const_mul (differentiableAt_pow 3) 6
  exact DifferentiableAt.const_mul differentiableAt_id 9
  exact DifferentiableAt.sub (
    DifferentiableAt.const_mul (differentiableAt_pow 3) 6
    ) (
      DifferentiableAt.const_mul differentiableAt_id 9
    )
  exact differentiableAt_const 4


theorem h0_5 (x0: ℝ): deriv (λ x ↦ 6 * x^3 - 9 * x + 4) x0 = 18 * x0^2 - 9 := by

  simp [deriv_add]
  rw [deriv_sub]
  simp [deriv_const_mul]
  rw [deriv_const_mul]
  simp [deriv_id'']
  ring
  exact differentiableAt_id
  exact DifferentiableAt.const_mul (differentiableAt_pow 3) 6
  exact DifferentiableAt.const_mul differentiableAt_id 9
