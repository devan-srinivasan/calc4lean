"""
Prompt GPT4o to generate annotations. Later we can add fine-tuning here as well.
"""

def convert_copied_proof_to_one_line_str(proof): return '\\n'.join(proof.split('\n'))

def populate_manual():
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

populate_manual()