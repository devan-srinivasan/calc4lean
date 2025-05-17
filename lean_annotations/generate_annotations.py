"""
Prompt GPT4o to generate annotations. Later we can add fine-tuning here as well.
"""
import dotenv, os, json
from openai import OpenAI

def convert_copied_proof_to_one_line_str(proof): return '\\n'.join(proof.split('\n'))

def populate_manual_diff():
    import json
    proofs = [
"""example (x: ℝ)  (h_log_ne_zero_16: x ≠ 0): deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) := by

nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
ring
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_16)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_16))
exact Real.differentiableAt_sin
exact DifferentiableAt.add (DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))) (DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_16)))
""",

"""example (x: ℝ)  (h_div_ne_zero_20: Real.log ((5:ℝ)) ≠ 0) (h_log_ne_zero_21: x ≠ 0) (h_log_ne_zero_23: (5:ℝ) ≠ 0): deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2))) := by

nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [Real.deriv_exp]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_div]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 3 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_const]
field_simp [h_div_ne_zero_20, h_log_ne_zero_21, h_log_ne_zero_23]
ring
exact Real.differentiableAt_log (h_log_ne_zero_23)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_21)
exact DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_23)
exact h_div_ne_zero_20
exact differentiableAt_id
exact differentiableAt_pow _
exact DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_21)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_23)) (h_div_ne_zero_20)
exact differentiableAt_id
exact differentiableAt_pow _
exact differentiableAt_const _
exact Real.differentiableAt_exp
exact DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _)
exact DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))
exact DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_21)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_23)) (h_div_ne_zero_20))
exact Real.differentiableAt_exp
exact DifferentiableAt.add (DifferentiableAt.mul (Real.differentiableAt_exp) (DifferentiableAt.add (differentiableAt_pow _) (differentiableAt_const _))) (DifferentiableAt.mul (differentiableAt_pow _) (DifferentiableAt.div (Real.differentiableAt_log (h_log_ne_zero_21)) (DifferentiableAt.log (differentiableAt_const _) (h_log_ne_zero_23)) (h_div_ne_zero_20)))
""",

"""example (x: ℝ)  (h_log_ne_zero_5: x ≠ 0) (h_log_ne_zero_19: ((5:ℝ) * x + (2:ℝ)) ≠ 0): deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ))) := by

nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
nth_rewrite 1 [deriv_sub]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 2 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_add]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [deriv_const]
nth_rewrite 1 [deriv_id'']
nth_rewrite 1 [deriv_const]
field_simp [h_log_ne_zero_5, h_log_ne_zero_19]
ring
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_log (h_log_ne_zero_19)
exact DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_19)
exact differentiableAt_const _
exact differentiableAt_id
exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)
exact differentiableAt_const _
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_5)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact DifferentiableAt.sub (DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_5))) (DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _)
exact DifferentiableAt.pow (DifferentiableAt.log (DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)) (h_log_ne_zero_19)) _
""",

"""example (x: ℝ)  (h_tan_ne_zero_1: Real.cos (Real.cos ((Real.log (x))) * (Real.sin (((2:ℝ) * x - (1:ℝ)))) ^ 2) ≠ 0) (h_log_ne_zero_6: x ≠ 0): deriv (λ x ↦ Real.tan (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / Real.cos (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2 := by

nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_tan]
nth_rewrite 1 [deriv_mul]
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_cos]
nth_rewrite 1 [Real.deriv_log]
nth_rewrite 1 [deriv_pow'']
nth_rewrite 1 [← Function.comp_def]
nth_rewrite 1 [deriv_comp]
nth_rewrite 1 [Real.deriv_sin]
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
exact Real.differentiableAt_sin
exact DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _)
exact DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))
exact Real.differentiableAt_cos
exact Real.differentiableAt_log (h_log_ne_zero_6)
exact DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_6))
exact DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _
exact Real.differentiableAt_tan.mpr (h_tan_ne_zero_1)
exact DifferentiableAt.mul (DifferentiableAt.cos (Real.differentiableAt_log (h_log_ne_zero_6))) (DifferentiableAt.pow (DifferentiableAt.sin (DifferentiableAt.sub (DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_id)) (differentiableAt_const _))) _)
"""

    ]

    annotations = [
"""We want to prove that the derivative with respect to x of sin((e^x) * (x^2 + 3) + cos(log(x))) = cos(e^x * (x^2 + 3) + cos(log(x))) * ((e^x * (x^2 + 3)) + (e^x * 2 * x) + (-1) * sin (log(x)) / x) given that x is not equal to 0.
1. First we must differentiate the function, which will include using (more than once) differentiation rules.
2. Second, we must simplify the algebra to show the two sides of the equation are equal. Often this is trivial / obvious.
3. Finally, we recall that each differentiation rule we applied in step (1) requires that we prove differentiability of the constituent functions. 
Now we are done!
""",

"""We want to prove that the derivative with respect to x of e^((e^x) * (x^2 + 3) + (x ^ 3) * log_5(x)) = e^(e^x * (x^2 + 3) + (x ^ 3) * log_5(x)) * ((e^x * (x^2 + 3)) + (e^x * 2 * x) + ((3 * x ^ 2) * log_5(x)) + ((x ^ 3) * ((log(5) / x) / log(5)) ^ 2))) given that x is not equal to 0.
1. First we must differentiate the function, which will include using (more than once) differentiation rules.
2. Second, we must simplify the algebra to show the two sides of the equation are equal. Often this is trivial / obvious.
3. Finally, we recall that each differentiation rule we applied in step (1) requires that we prove differentiability of the constituent functions. 
Now we are done!
""",

"""We want to prove that the derivative with respect to x of cos(log(x)) - (sin(2*x - 1)) ^ 2 + (log(5*x + 2)) ^3 = (-1) * sin(log(x)) / x - (2 * sin(2*x - 1) * (cos(2*x - 1) * 2)) + 3 * log(5*x + 2) ^ 2 * (5 / (5*x + 2)) given that x does not equal and 5*x + 2 does not equal 0 
1. First we must differentiate the function, which will include using (more than once) differentiation rules.
2. Second, we must simplify the algebra to show the two sides of the equation are equal. Often this is trivial / obvious.
3. Finally, we recall that each differentiation rule we applied in step (1) requires that we prove differentiability of the constituent functions. 
Now we are done!
""",

"""
We want to prove that the derivative with respect to x of tan(cos(log(x)) * (sin(2*x - 1))^2) = ((((-1) * sin(log(x)) / x) * (sin (2*x - 1) ^ 2)) + (cos(log(x)) * 2 * sin(2*x - 1) * cos(2*x - 1) * 2)) / cos(cos(log(x)) * sin(2*x - 1)^2)^2 given that cos(cos(log(x)) * sin(2*x-1)) ^ 2 is not 0 and x is not 0
1. First we must differentiate the function, which will include using (more than once) differentiation rules.
2. Second, we must simplify the algebra to show the two sides of the equation are equal. Often this is trivial / obvious.
3. Finally, we recall that each differentiation rule we applied in step (1) requires that we prove differentiability of the constituent functions. 
Now we are done!
"""
    ]

    pairs = []
    for proof, ann in zip(proofs, annotations):
        pairs.append({
            "proof": proof,
            "annotation": ann
        })

    with open('lean_annotations/differentiation_examples.json', 'w') as f: json.dump(pairs, f, indent=4)

def easymylife(s):
    s = s.replace('Real.', '').replace(':ℝ', '').replace('exp ', 'e^')
    print(s)

# easymylife('deriv (λ x ↦ Real.sin ((Real.exp x) * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x))) x = Real.cos (Real.exp x * (x ^ 2 + (3:ℝ)) + Real.cos (Real.log x)) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x))')
# print()
# easymylife('deriv (λ x ↦ Real.exp ((Real.exp x) * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ)))) x = Real.exp (Real.exp x * (x ^ 2 + (3:ℝ)) + (x ^ 3) * (Real.log x / Real.log (5:ℝ))) * ((Real.exp x * (x ^ 2 + (3:ℝ))) + (Real.exp x * ((2:ℝ) * x)) + (((3:ℝ) * x ^ 2) * (Real.log x / Real.log (5:ℝ))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log (5:ℝ)) / Real.log (5:ℝ) ^ 2)))')
# print()
# easymylife('deriv (λ x ↦ Real.cos (Real.log x) - (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2 + (Real.log ((5:ℝ) * x + (2:ℝ))) ^ 3) x = (-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x) - ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))) + (3:ℝ) * Real.log ((5:ℝ) * x + (2:ℝ)) ^ 2 * ((5:ℝ) / ((5:ℝ) * x + (2:ℝ)))')
# print()
# easymylife('deriv (λ x ↦ Real.tan (Real.cos (Real.log x) * (Real.sin ((2:ℝ) * x - (1:ℝ))) ^ 2)) x = ((((-1:ℝ) * Real.sin (Real.log x) * ((1:ℝ) / x)) * (Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2)) + (Real.cos (Real.log x) * ((2:ℝ) * Real.sin ((2:ℝ) * x - (1:ℝ)) * (Real.cos ((2:ℝ) * x - (1:ℝ)) * (2:ℝ))))) / Real.cos (Real.cos (Real.log x) * Real.sin ((2:ℝ) * x - (1:ℝ)) ^ 2) ^ 2')

def populate_manual_mon():
    import json
    proofs = [
"""example: MonotoneOn (λ x ↦ 17 * x ^ 7 + 3 * x ^ 2) (Icc (0: ℝ) (3: ℝ)) := by
  let f := λ x : ℝ ↦ 17 * x ^ 7 + 3 * x ^ 2
  let D := Icc (0: ℝ) (3: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (0: ℝ) (3: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
    nth_rewrite 1 [deriv_add]
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

    have h0: 0 < 6 * x ^ 1 := by
      have power_pos: 0 < x ^ 1 := by
        apply pow_pos (hx.1)
      linarith [power_pos]

    have h1: 0 < 119 * x ^ 6 := by
      have power_pos: 0 < x ^ 6 := by
        apply pow_pos (hx.1)
      linarith [power_pos]
    linarith [h1]
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact differentiableAt_id
    exact differentiableAt_const _
    exact differentiableAt_pow _
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)
    exact DifferentiableAt.mul (differentiableAt_const _) (differentiableAt_pow _)

  have hf: ContinuousOn f D := by
    simp [f]
    apply (Continuous.add (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _)) (Continuous.mul (continuous_const) (Continuous.pow (continuous_id) _))).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn
""",

"""example: MonotoneOn (λ x ↦ 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14) (Icc (0: ℝ) (7: ℝ)) := by
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
  """,

"""example: MonotoneOn (λ x ↦ 9 * x ^ 2 - 126 * x + 3528) (Icc (7: ℝ) (9: ℝ)) := by
  let f := λ x : ℝ ↦ 9 * x ^ 2 - 126 * x + 3528
  let D := Icc (7: ℝ) (9: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc (7: ℝ) (9: ℝ)
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
  """
    ]

    annotations = [
"""We need to prove that the polynomial f(x) = 17 * x ^ 7 + 3 * x ^ 2 is monotonic on the set D = [0, 3]. We will do so by first proving that D is convex. Then we will prove that the derivative 
of f is positive on the interior of D. Then we will show that f is continuous on D. Finally, we can conclude it is monotonic on D. 
1. We can prove D is convey by using the theorem that any closed interval is convex.
2. To prove the derivative of f is positive on the interior of D, we can do the following:
    a. First we can assume that x is in the interior of D, that is, 0 < x < 3
    a. Second we can differentiate the function, which will include using (more than once) differentiation rules. This will show that it sufficies to prove 119 * x ^ 6 + 6 * x > 0. We may need to
        do some algebraic simplification here, but usually it is obvious
    b. Third, we must show the inequality is true. One way to do this is by showing each term is positive, and thus the sum is positive.
    d. Finally, we recall that each differentiation rule we applied in step (b) requires that we prove differentiability of the constituent functions, so we prove that here.
    Now we have proven f' is positive on the interior of D
3. We can show continuity by proving that each term in the polynomial is continuous, and thus the sum is continuous. This part is straightforward.
4. Using these we can then conclude that f is monotonic on D.
Now we are done.
""",

"""We need to prove that the polynomial f(x) = 7 * x ^ 6 + 7 * x ^ 4 + 5 * x ^ 2 + 14 is monotonic on the set D = [0, 7]. We will do so by first proving that D is convex. Then we will prove that the derivative 
of f is positive on the interior of D. Then we will show that f is continuous on D. Finally, we can conclude it is monotonic on D. 
1. We can prove D is convey by using the theorem that any closed interval is convex.
2. To prove the derivative of f is positive on the interior of D, we can do the following:
    a. First we can assume that x is in the interior of D, that is, 0 < x < 7
    a. Second we can differentiate the function, which will include using (more than once) differentiation rules. This will show that it sufficies to prove 42 * x ^ 5 + 28 * x ^ 6 + 10 * x > 0. We may need to
        do some algebraic simplification here, but usually it is obvious
    b. Third, we must show the inequality is true. One way to do this is by showing each term is positive, and thus the sum is positive.
    d. Finally, we recall that each differentiation rule we applied in step (b) requires that we prove differentiability of the constituent functions, so we prove that here.
    Now we have proven f' is positive on the interior of D
3. We can show continuity by proving that each term in the polynomial is continuous, and thus the sum is continuous. This part is straightforward.
4. Using these we can then conclude that f is monotonic on D.
Now we are done.
""",

"""We need to prove that the polynomial f(x) = 9 * x ^ 2 - 126 * x + 3528 is monotonic on the set D = [7, 9]. We will do so by first proving that D is convex. Then we will prove that the derivative 
of f is positive on the interior of D. Then we will show that f is continuous on D. Finally, we can conclude it is monotonic on D. 
1. We can prove D is convey by using the theorem that any closed interval is convex.
2. To prove the derivative of f is positive on the interior of D, we can do the following:
    a. First we can assume that x is in the interior of D, that is, 7 < x < 9
    a. Second we can differentiate the function, which will include using (more than once) differentiation rules. This will show that it sufficies to prove -126 * x + 18 > 0. We may need to
        do some algebraic simplification here, but usually it is obvious
    b. Third, we must show the inequality is true. In this case, it is obvious given that x > 7 so this is easy to show.
    d. Finally, we recall that each differentiation rule we applied in step (b) requires that we prove differentiability of the constituent functions, so we prove that here.
    Now we have proven f' is positive on the interior of D
3. We can show continuity by proving that each term in the polynomial is continuous, and thus the sum is continuous. This part is straightforward.
4. Using these we can then conclude that f is monotonic on D.
Now we are done.
"""

    ]

    pairs = []
    for proof, ann in zip(proofs, annotations):
        pairs.append({
            "proof": proof,
            "annotation": ann
        })

    with open('lean_annotations/motonicity_examples.json', 'w') as f: json.dump(pairs, f, indent=4)

def populate_manual_ineq():
    import json
    proofs = [
"""
example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = 17)
  (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p)
  (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + 17 * q x > 34 * x := by
  let f := (λ x ↦ p x + 17 * q x - 34 * x)
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
      have reciprocal_deriv: deriv q x2 = 17 / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = 17 ↔ deriv q x2 = 17 / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + 17 * (17 / deriv p x2) - 34) ↔
        0 ≤ deriv p x2 + 17 * (17 / deriv p x2) - 34 := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + 17 * (17 / deriv p x2) - 34)
              = deriv p x2 ^ 2 + 17 * 17 - 34 * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + 17 * 17 - 34 * deriv p x2 = (deriv p x2 - 17) ^ 2 := by ring
      have simplify: deriv p x2 + 17 * (17 / deriv p x2) - 34 * (fun x2 ↦ 1) x = deriv p x2 + 17 * (17 / deriv p x2) - 34 := by ring
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
  have equiv: p x + 17 * q x > 34 * x ↔ p x + 17 * q x - 34 * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos
"""
    ]

    annotations = [
"""We aim to show that for two functions p(x), q(x), given that p(0) = q(0) > 0, and that p'(x) * q'(x) = 17 for all x in 
D = [0, 1] it holds that p(x) + 17 * q(x) > 34 * x, with the given assumptions that that p(x), and q(x) are differentiable over all real numbers, and that
p'(x) > 0 for all x. One idea to prove this is to show that the function f(x) = p(x) + 17 * q(x) - 34 * x is positive on D, as that is equivalent
to what we want to show. We can prove that by showing f(0) > 0, and that f is monotonic on (0, 1). We can then conclude that f is positive, and then manipulate
it to show our original inequality is true.

1. Let f(x) = p(x) + 17 * q(x) - 34 * x
2. We can prove that f(0) = 0 by straightforward substitution.
3. Next we can show that f is monotonic on D using the following.
    a. We show that f is differentiable over the reals, which follows using our assumptions about the differentiability of p and q, as well as differentiabiliy
    rules. 
    b. We can then conclude f is differentiable on D since D is a subset of all real numbers
    c. Since f is differentiable, we can conclude that it is continuous on D as well.
    d. We can show that the derivative of f is nonnegative on the interior of D by the following method
        i. We assume that x is in the interior of D, that is 0 < x < 1
        ii. We substitute the q'(x) as 17/p'(x) using the fact that p'(x) > 0
        iii. We apply standard differentiation rules to simplify the derivative to p'(x) + 17 * (17 / p'(x)) - 34
        iv. We show that p'(x) + 17 * (17 / p'(x)) - 34 > 0 if and only if p'(x) * (p'(x) + 17 * (17 / p'(x)) - 34) > 0 using the fact that p'(x) > 0
        v. We show that this expression can be factored into (p'(x) - 17)^2 > 0
        vi. We then show that this is nonnegative using the fact that the square of anything is nonnegative
        vii. Finally, as we used differentiation rules to simplify the derivatives, we show each constitutuent in the rules we applied are differentiability, to satisfy
            valid use of those rules.
    e. Finally, with these proven, we can conclude that f is monotonic on D
4. Now we can prove that f is positive on D.
    a. First we show that x is positive which is easy as we have the assumption that 0 < x < 1.
    b. Then we show that f(x) > f(0) for x in D, which follows from our proof of monotonicity of f on D.
    c. Then we conclude that f is positive on D.
5. Finally we rearrange the terms of f being positive on D to show that we have proven our desired inequality. That is, p(x) + 17 * q(x) - 34 * x > 0 is equivalent to p(x) + 17 * q(x) > 34 * x
Now we are done.

"""
    ]

    pairs = []
    for proof, ann in zip(proofs, annotations):
        pairs.append({
            "proof": proof,
            "annotation": ann
        })

    with open('lean_annotations/inequality_examples.json', 'w') as f: json.dump(pairs, f, indent=4)

def llm_annotate():
    dotenv.load_dotenv(dotenv_path='data/.env')
    client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

    PROMPT = f"""

asfa
"""
    
    response = client.chat.completions.create(
        model="gpt-4o-mini",  # or your preferred model
        messages=[
            {"role": "system", "content": PROMPT},
            {"role": "user", "content": ""}
        ]
    )
    
    return response.choices[0].message.content.strip(), d(0.3 * response.usage.prompt_tokens + 1.2 * response.usage.completion_tokens) / (10**6)


with open('lean_annotations/monotonicity_examples.json', 'r') as f:
    problems = json.load(f)
for p in problems:
    print(p['proof'])
    print()
