import func, deriv, json

header = """
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
open Real


"""

monotone_header = """
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set
"""

funcs = [
    "(Real.exp x) * (x^2 + 3)",
    "Real.cos (Real.log x)",
    "(Real.sin (2 * x - 1))^2",
    "(x ^ 3) * (Real.log x / Real.log 5)",
    "(Real.log (5 * x + 2)) ^ 3",
    "Real.tan (5 * x)",
]

funcs_derivs = [
    "(exp x) * x^2 + (exp x) * 2 * x + 3 * exp x",
    "-sin (log x) / x",
    "4 * sin (2 * x - 1) * cos (2 * x - 1)",
    "3 * x ^ 2 * Real.log x / Real.log 5 + x ^ 2 / Real.log 5",
    "15 * (Real.log (5 * x + 2)) ^ 2 / (5 * x + 2)",
    "5 / cos (5 * x) ^ 2",
]

def expand_generic_op(functions, derivatives):
    problems = []
    for i in range(len(functions) - 1):
        for j in range(i+1, len(functions)):
            node1 = deriv.parse(functions[i]).children[0]
            node2 = deriv.parse(functions[j]).children[0]
            node_list = [
                func.Add(children=[node1, node2]),
                func.Sub(children=[node1, node2]),
                func.Mul(children=[node1, node2]),
                func.Div(children=[node1, node2], hyp_ne_zero='h_div_ne_zero'),
            ]

            for n in node_list:
                n = deriv.parse(n.clean(n.__repr__())).children[0]
                problems.append((
                    f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {n.clean(n.__repr__())}) x = {n.clean(n.derivative())} := by", # theorem
                    deriv.get_deriv_proof(n) # proof
                ))
    
    file_str = header
    for theorem, proof in problems:
        file_str += theorem + '\n' + proof + '\n\n'
    
    with open('lean/LeanCalc/synthetic/generic_op.lean', 'w') as f:
        f.write(file_str)
    
    print(len(problems))

def expand_generic_comp(functions, derivatives):
    problems = []
    for i in range(len(functions) - 1):
        node1 = deriv.parse(functions[i]).children[0]
        node_list = [
            func.Sin(children=[node1]),
            func.Cos(children=[node1]),
            func.Tan(children=[node1], hyp_ne_zero='h_tan_ne_zero'),
            func.Exp(children=[node1]),
            func.Log(children=[node1], hyp_ne_zero='h_div_ne_zero'),
        ]

        for n in node_list:
            n = deriv.parse(n.clean(n.__repr__())).children[0]
            problems.append((
                f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {n.clean(n.__repr__())}) x = {n.clean(n.derivative())} := by", # theorem
                deriv.get_deriv_proof(n) # proof
            ))
    
    file_str = header
    for theorem, proof in problems:
        file_str += theorem + '\n' + proof + '\n\n'
    
    with open('lean/LeanCalc/synthetic/generic_comp.lean', 'w') as f:
        f.write(file_str)
    
    print(len(problems))

def generate_monotonicity_simple(min_deg, max_deg, n_per_deg):
    class Poly:
        def __init__(self, degree: int):
            from random import randint
            self.terms = [
                (randint(2, 5), i) for i in range(degree+1)
            ]

            self.interval = (0, randint(1, 10))

        def __repr__(self) -> str:
            terms = []
            for coeff, exp in reversed(self.terms):
                terms.append(f"{coeff}{' * x' if exp > 0 else ''}{f' ^ {exp}' if exp > 1 else ''}")
            return " + ".join(terms)
        
        def get_pos_proof(self):
            lns = []
            for i, (coeff, exp) in enumerate(self.terms):
                if exp == 0:
                    lns.append(f"    have h{i}: 0 < {coeff} := by norm_num")
                elif exp == 1:
                    lns.append(f"    have h{i}: 0 < {coeff} * x := by linarith [hx.1]")
                elif exp > 1:
                    lns.append(
f"""
    have h{i}: 0 < {coeff} * x ^ {exp} := by
      have power_pos: 0 < x ^ {exp} := by
        apply pow_pos (hx.1)
      linarith [power_pos]"""
                )
            lns.append(f"    linarith [{', '.join([f'h{i}' for i in range(len(self.terms))])}]")
            return '\n'.join(lns)

        def get_monotonicity_problem(self):
            poly_node = deriv.parse(str(self)).children[0]
            proof, _, __, diff = deriv.get_deriv_proof(poly_node, separate=True)
            proof = '\n'.join([f"    {l}" for l in proof.split('\n')])
            diff = '\n'.join([f"    {l}" for l in diff.split('\n')])
            pos_proof = self.get_pos_proof()
            template = f"""
example: MonotoneOn (λ x ↦ {str(self)}) (Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)) := by
  let f := λ x : ℝ ↦ {str(self)}
  let D := Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
{proof}
    ring
    rw [interior_Icc] at hx
{pos_proof}
{diff}

  have hf: ContinuousOn f D := by
    simp [f]
    apply ({poly_node.continuity()}).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn
"""
            return template
    
    file_str = monotone_header
    for i in range(min_deg, max_deg):
        for j in range(n_per_deg):
            p = Poly(degree=i)
            problem_str = p.get_monotonicity_problem()
            problem_str = problem_str.replace('\t', '  ')   # no tabs
            file_str += problem_str
    
    with open('lean/LeanCalc/synthetic/monotone_simple.lean', 'w') as f:
        f.write(file_str)

def generate_monotonicity_shifted(n):
    class Poly:
        def __init__(self):
            from random import randint
            shift = randint(1, 10)
            a_coeff = randint(2, 10)
            c_coeff = randint(1, 10)
            
            self.terms = [
                (a_coeff * shift * shift * c_coeff, 0),
                (a_coeff * shift * 2, 1),
                (a_coeff, 2)
            ]

            self.interval = (shift, shift + randint(1, 10))

        def __repr__(self) -> str:
            terms = []
            for coeff, exp in reversed(self.terms):
                terms.append(f"{coeff}{' * x' if exp > 0 else ''}{f' ^ {exp}' if exp > 1 else ''}")
            return terms[0] + ' - ' + terms[1] + ' + ' + terms[2]

        def get_monotonicity_problem(self):
            poly_node = deriv.parse(str(self)).children[0]
            proof, _, __, diff = deriv.get_deriv_proof(poly_node, separate=True)
            proof = '\n'.join([f"    {l}" for l in proof.split('\n')])
            diff = '\n'.join([f"    {l}" for l in diff.split('\n')])
            template = f"""
example: MonotoneOn (λ x ↦ {str(self)}) (Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)) := by
  let f := λ x : ℝ ↦ {str(self)}
  let D := Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)
  have hD: Convex ℝ D := by
    apply convex_Icc ({self.interval[0]}: ℝ) ({self.interval[1]}: ℝ)
  have hf': ∀ x0 ∈ interior D, 0 < deriv f x0 := by
    intro x hx
    unfold f
{proof}
    ring
    rw [interior_Icc] at hx
    linarith [hx.1]
{diff}

  have hf: ContinuousOn f D := by
    simp [f]
    apply ({poly_node.continuity()}).continuousOn
  change MonotoneOn f D
  apply (strictMonoOn_of_deriv_pos hD hf hf').monotoneOn
"""
            return template
    
    file_str = monotone_header
    for i in range(n):
        p = Poly()
        problem_str = p.get_monotonicity_problem()
        file_str += problem_str
    
    with open('lean/LeanCalc/synthetic/monotone_shifted.lean', 'w') as f:
        f.write(file_str)

# expand_generic_op(funcs[:-1], funcs_derivs[:-1])  -> 40
# expand_generic_comp(funcs, funcs_derivs) -> 25
# generate_monotonicity_simple(min_deg=2, max_deg=6, n_per_deg=5) 4*5 -> 20
# generate_monotonicity_shifted(n=20) -> 20