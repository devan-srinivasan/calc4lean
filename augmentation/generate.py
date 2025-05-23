import func, deriv, json, re, random
import numpy as np 

"""
This is the file for creating synthetic problems. Not much to see here
basically just take the AST and compute derivatives / differentiability proofs or whatever
and then follow a template to construct synthetic samples 
"""

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

tangent_header = """
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

open Real
open Set
"""

extrema_headers = """
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp

open Real
"""

funcs = [
    "(Real.exp x) * (x^2 + 3)",
    "Real.cos (Real.log x)",
    "(Real.sin (2 * x - 1))^2",
    "(x ^ 3) * (Real.log x / Real.log 5)",
    "(Real.log (5 * x + 2)) ^ 3",
    # "Real.tan (5 * x)",
]

funcs_derivs = [
    "(exp x) * (x^2 + 2 * x + 3)",
    "(-1) * sin (log x) / x",
    "4 * sin (2 * x - 1) * cos (2 * x - 1)",
    "3 * x ^ 2 * (Real.log x + 1) / Real.log 5",
    "15 * (Real.log (5 * x + 2)) ^ 2 / (5 * x + 2)",
    # "5 / cos (5 * x) ^ 2",
]

def get_corresponding_constant(fx: "Poly", point):
    max_degree = max([e for _,e in fx.terms])
    poly_numpy_format = [0] * (max_degree + 1)
    for c, e in fx.terms:
        poly_numpy_format[e] = c
    poly_numpy_format = poly_numpy_format[::-1]
    return np.polyval(poly_numpy_format, point)

def parse_functions(seed_file: str):
    with open(seed_file, 'r') as f:
        lines = f.readlines()
    fs, dfs, theorems, proofs = [], [], [], []

    i = 0
    while i < len(lines):
        line = lines[i]
        if 'example' not in line: 
            i += 1
            continue
        f, df = re.search(r"deriv\s*\(λ x ↦ (.*?)\)\s*x\s*=\s*(.*?)\s*:=\s*by", line).groups()
        t = line
        j = i + 1
        while j < len(lines) and len(lines[j].replace('\n', '').strip()) > 0:
            j += 1
        p = ''.join(lines[i+1:j])
        fs.append(f)
        dfs.append(df)
        theorems.append(t)
        proofs.append(p)
        i = j
    
    return fs, dfs, theorems, proofs

def expand_seed(original_functions, functions):
    
    def deduplicate_terms(theorem, proof):
        # ChatGPT
        # Step 1: Extract all (hname: desc) pairs
        pattern = r"\((h\w+): ([^)]+)\)"
        matches = re.findall(pattern, theorem)

        hm = {}

        for hname, desc in matches:
            if desc not in hm:
                # Duplicate desc: map the new hname to the original one
                hm[desc] = [hname]
            else:
                hm[desc].append(hname)

        for desc in hm.keys():
            for dup in hm[desc][1:]:
                theorem = theorem.replace(f"({dup}: {desc})", "")
                proof = proof.replace(dup, hm[desc][0])
        return theorem, proof

    problems = []
    for f in functions:
        node1 = deriv.parse(f).children[0]
        
        compositions = [
            func.Sin(children=[node1]),
            func.Cos(children=[node1]),
            func.Tan(children=[node1], hyp_ne_zero='h_tan_ne_zero'),
            func.Exp(children=[node1]),
            func.Log(children=[node1], hyp_ne_zero='h_div_ne_zero'),
        ]

        # ... tweak inside (?)

        candidate_op_functions = [
            f for f in original_functions if f not in str(node1)
        ]

        for f2 in candidate_op_functions:
            node2 = deriv.parse(f2).children[0]
            compositions.extend([
                func.Add(children=[node1, node2]),
                # func.Sub(children=[node1, node2]),
                func.Mul(children=[node1, node2]),
                # func.Div(children=[node1, node2], hyp_ne_zero='h_div_ne_zero'),
            ])

        for n in compositions:
            n = deriv.parse(n.clean(n.__repr__())).children[0]
            deriv_expr = n.clean(n.derivative())
            deriv_node = deriv.parse(deriv_expr).children[0].reduce()
            f, df = n.clean(n.__repr__()), n.clean(str(deriv_node))
            theorem = f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {f}) x = {df} := by" # theorem
            proof = deriv.get_deriv_proof(n)
            theorem, proof = deduplicate_terms(theorem, proof) # ... clean up hypotheses ...
            problems.append((theorem, proof))

    file_str = header
    for theorem, proof in problems:
        file_str += theorem + '\n' + proof + '\n\n'
    
    with open(f'lean/LeanCalc/synthetic/seed_2.lean', 'w') as f:
        f.write(file_str)
    
    print(len(problems))    
        

def create_seed(functions, derivatives, fn='seed_2', comp_only=False):
    problems = []
    if not comp_only:
      c = 3
      for i in range(len(functions) - 1):
          for j in random.sample(range(i+1, len(functions)), min(c, len(functions) - i - 1)):
              node1 = deriv.parse(functions[i]).children[0]
              node2 = deriv.parse(functions[j]).children[0]
              node1.derivative_repr = derivatives[i]
              node2.derivative_repr = derivatives[j]

              node_list = [
                  func.Add(children=[node1, node2]),
                  func.Sub(children=[node1, node2]),
                  func.Mul(children=[node1, node2]),
                  func.Div(children=[node1, node2], hyp_ne_zero='h_div_ne_zero'),
              ]

              for n in node_list:
                  n = deriv.parse(n.clean(n.__repr__())).children[0]
                  deriv_expr = n.clean(n.derivative())
                  deriv_node = deriv.parse(deriv_expr).children[0].reduce()
                  f, df = n.clean(n.__repr__()), n.clean(str(deriv_node))
                  problems.append((
                      f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {f}) x = {df} := by", # theorem
                      deriv.get_deriv_proof(n), # proof
                  ))
      
    for i in range(len(functions) - 1):
        node1 = deriv.parse(functions[i]).children[0]
        node_list = [
            func.Sin(children=[node1]),
            func.Cos(children=[node1]),
            # func.Tan(children=[node1], hyp_ne_zero='h_tan_ne_zero'),
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
    
    with open(f'lean/LeanCalc/synthetic/{fn}.lean', 'w') as f:
        f.write(file_str)
    
    print(len(problems))

# === not used
def expand_generic_op(functions, derivatives):
    problems = []
    for i in range(len(functions) - 1):
        for j in range(i+1, len(functions)):
            node1 = deriv.parse(functions[i]).children[0]
            node2 = deriv.parse(functions[j]).children[0]
            node1.derivative_repr = derivatives[i]
            node2.derivative_repr = derivatives[j]

            node_list = [
                func.Add(children=[node1, node2]),
                func.Sub(children=[node1, node2]),
                func.Mul(children=[node1, node2]),
                func.Div(children=[node1, node2], hyp_ne_zero='h_div_ne_zero'),
            ]

            for n in node_list:
                n = deriv.parse(n.clean(n.__repr__())).children[0]
                deriv_expr = n.clean(n.derivative())
                deriv_node = deriv.parse(deriv_expr).children[0].reduce()
                f, df = n.clean(n.__repr__()), n.clean(str(deriv_node))
                problems.append({
                    "theorem": f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {f}) x = {df} := by", # theorem
                    "proof": deriv.get_deriv_proof(n), # proof
                })
    
    file_str = header
    for p in problems:
        theorem, proof = p['theorem'], p['proof']
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
# ===

def generate_monotonicity_simple(n):
    class Poly:
        def __init__(self, degree: int):
            from random import randint
            self.terms = [
                (randint(2, 20), i) for i in range(degree+1) if i in random.sample(range(8), random.randint(2, 8))
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
                # if exp == 0:
                #     lns.append(f"    have h{i}: 0 < {coeff} := by norm_num")
                if exp == 1:
                    lns.append(f"    have h{i}: 0 < {coeff} := by linarith [hx.1]")
                elif exp > 1:
                    lns.append(
f"""
    have h{i}: 0 < {coeff * exp} * x ^ {exp - 1} := by
      have power_pos: 0 < x ^ {exp - 1} := by
        apply pow_pos (hx.1)
      linarith [power_pos]"""
                )
            lns.append(f"    linarith [{', '.join([f'h{i}' for i in range(1, len(self.terms))])}]")
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
    for _ in range(n):
        p = Poly(degree=7)
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

def generate_pq_easy(n):
    # no a coefficient for now
    def get_random_instance():
        from random import randint

        def factor(num):
            for i in range(2, int(num**0.5) + 1):
                if num % i == 0:
                    return i, num // i
            raise ValueError(f"{num} is prime, and cannot be prime for this to work")

        k = randint(2, 20)
        c = 2*k
        b, d = factor(k**2)
        template = f"""
example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = {d})
  (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p)
  (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + {b} * q x > {c} * x := by
  let f := (λ x ↦ p x + {b} * q x - {c} * x)
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
      have reciprocal_deriv: deriv q x2 = {d} / deriv p x2 := by
        have hf'_iff: deriv p x2 * deriv q x2 = {d} ↔ deriv q x2 = {d} / deriv p x2 := by
          field_simp [hpX2]
          ring
        exact hf'_iff.mp (hf' x2)
      rw [deriv_sub]
      rw [deriv_add]
      rw [deriv_const_mul]
      rw [reciprocal_deriv]
      rw [deriv_const_mul]
      rw [deriv_id'']
      have sq_iff : 0 ≤ deriv p x2 * (deriv p x2 + {b} * ({d} / deriv p x2) - {c}) ↔
        0 ≤ deriv p x2 + {b} * ({d} / deriv p x2) - {c} := by
        apply mul_nonneg_iff_of_pos_left (hP x2)
      have quad_eq : deriv p x2 * (deriv p x2 + {b} * ({d} / deriv p x2) - {c})
              = deriv p x2 ^ 2 + {b} * {d} - {c} * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + {b} * {d} - {c} * deriv p x2 = (deriv p x2 - {int(c/2)}) ^ 2 := by ring
      have simplify: deriv p x2 + {b} * ({d} / deriv p x2) - {c} * (fun x2 ↦ 1) x = deriv p x2 + {b} * ({d} / deriv p x2) - {c} := by ring
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
  have equiv: p x + {b} * q x > {c} * x ↔ p x + {b} * q x - {c} * x > 0 := by constructor <;> intro h <;> linarith
  rw [equiv]
  exact f_pos
"""
        return template
    
    file_str = monotone_header
    # TODO
            # p = Poly()
            # problem_str = p.get_monotonicity_problem()
            # problem_str = problem_str.replace('\t', '  ')   # no tabs
            # file_str += problem_str
    for _ in range(n):
        file_str += get_random_instance() + '\n\n'
    with open('lean/LeanCalc/synthetic/pq_easy.lean', 'w') as f:
        f.write(file_str)

def generate_random_tangent_instance():
    
    class Poly:
        def __init__(self, terms = []):
            self.terms = terms
            if not self.terms:
                # TODO generate randomly
                pass
        def __repr__(self):
            def format_x(c,e):

                if c == 0:
                    return ""

                op = "+ "
                if c < 0:
                    op = "- "
                c = abs(c)
                if e == 0:
                    return op + str(c)

                if c > 1:
                    coeff=f"{c}" + (' * ' if e > 0 else '')
                else:
                    coeff = ""
                if e == 1:
                    p = "x"
                elif e > 1:
                    p = f"x ^ {e}"
                else:
                    p = ""
                return op + coeff + p
            
            return ' '.join([format_x(c,e) for c, e in self.terms])
        
        def repr_sign_changed(self):
            def format_x(c,e):

                if c == 0:
                    return ""

                op = "- "
                if c < 0:
                    op = "+ "
                c = abs(c)
                if e == 0:
                    return op + str(c)

                if c > 1:
                    coeff=f"{c}" + (' * ' if e > 0 else '')
                else:
                    coeff = ""
                if e == 1:
                    p = "x"
                elif e > 1:
                    p = f"x ^ {e}"
                else:
                    p = ""
                return op + coeff + p
            
            return ' '.join([format_x(c,e) for c, e in self.terms])[2:]
        
        def __str__(self):
            representation = repr(self)
            if representation.startswith("-"):
                pass
            return representation[2:]
        
        def leading_operation(self):
            if repr(self).startswith("-"):
                return "-"
            return "+"
    
    class PolyDeriv(Poly):
        def __init__(self, terms):
            self.terms = terms
            for i, (c, e) in enumerate(self.terms):
                self.terms[i] = (c*e, e-1)
            self.terms = [(c,e) for c,e in self.terms if e >= 0]

    class MultiVarNodeHack(func.Node):
        
        def __init__(self, differentiability):
            super().__init__()
            self.differentiability_proof = differentiability

        def differentiability(self):
            return self.differentiability_proof

    # DONOT MAKE THE FIRST COEFFICIENT NEGATIVE
    d1, d2 = random.randint(3,5), random.randint(3,5)
    # @binduchange (2,20) to (-20,20) and you'll hit the error
    x_expression_as_a_list = [(random.randint(-5,5), i) for i in range(1, d1+1)]
    y_expression_as_a_list = [(random.randint(-5,5), i) for i in range(1, d2+1)]

    random_mask1 = random.sample(range(len(x_expression_as_a_list)-1), random.randint(1, len(x_expression_as_a_list) - 1))
    random_mask2 = random.sample(range(len(y_expression_as_a_list)-1), random.randint(1, len(y_expression_as_a_list) - 1))

    solving_equation_x = "norm_num"
    if len(random_mask1) == 1:
        for i,term in enumerate(x_expression_as_a_list):
            if i in random_mask1 and term[1]==1:
                solving_equation_x = ""
    solving_equation_y = "norm_num"
    if len(random_mask2) == 1:
        for i,term in enumerate(y_expression_as_a_list):
            if i in random_mask2 and term[1]==1:
                solving_equation_y = ""
    hsplit_adjust = """congr 1
    ext p
    ring
    """

    if len(random_mask2) == 1:
        hsplit_adjust = ""

    x_expression_as_a_list = [term for i,term in enumerate(x_expression_as_a_list) if i in random_mask1]
    x_expression_as_a_list = [(1,e) if c==0 else (c,e) for c,e in x_expression_as_a_list]
    y_expression_as_a_list = [term for i,term in enumerate(y_expression_as_a_list) if i in random_mask2]
    y_expression_as_a_list = [(1,e) if c==0 else (c,e) for c,e in y_expression_as_a_list]

    # leading coeff is positive :D
    if x_expression_as_a_list[-1][0] < 0: x_expression_as_a_list[-1] = (x_expression_as_a_list[-1][0]*-1, x_expression_as_a_list[-1][1])
    #if y_expression_as_a_list[-1][0] < 0: y_expression_as_a_list[-1] = (y_expression_as_a_list[-1][0]*-1, y_expression_as_a_list[-1][1])

    x_expression_as_a_list = x_expression_as_a_list[::-1]
    y_expression_as_a_list = y_expression_as_a_list[::-1]

    # Adding (1,0) at the end is a neat little trick. Since it gives me the final expression too.
    # (Almost gives me the final expression, since I still have to make some changes)
    x_f_hack = Poly(x_expression_as_a_list + [(1,0)])
    y_f_hack = Poly(y_expression_as_a_list + [(1,0)])
    # For other use I will use normal x_f and y_f
    x_f = Poly(x_expression_as_a_list)
    y_f = Poly(y_expression_as_a_list)
    y_f_sign_change_poly = Poly([(-c,e) for c,e in y_expression_as_a_list])

    dx_f = PolyDeriv([e for e in x_f_hack.terms])
    dy_f = PolyDeriv([e for e in y_f_hack.terms])
    dy_f_sign_change_poly = PolyDeriv([e for e in y_f_sign_change_poly.terms])

    a, b = random.randint(-6,6), random.randint(-6,6)

    x_subbed_node = deriv.parse(str(x_f_hack).replace('p.1', f"(x - {a})")).children[0]
    y_subbed_node = deriv.parse(str(y_f_hack).replace('p.2', f"(x - {b})")).children[0]
    y_subbed_node_sign_change = deriv.parse(str(y_f_hack.repr_sign_changed()).replace('p.2', f"(x - {b})")).children[0]
    y_subbed_node_original = deriv.parse(str(y_f).replace('p.2', f"(x - {b})")).children[0]
    y_subbed_node_original_sign_changed = deriv.parse(y_f.repr_sign_changed().replace('p.2', f"(x - {b})")).children[0]

    deriv_x_subbed_node = deriv.parse(x_subbed_node.derivative()).children[0].reduce()
    deriv_y_subbed_node = deriv.parse(y_subbed_node.derivative()).children[0].reduce()

    x_proof, _, _, x_diff = deriv.get_deriv_proof(x_subbed_node, separate=True)
    y_proof, _, _, y_diff = deriv.get_deriv_proof(y_subbed_node, separate=True)
    y_proof_sign_change, _, _, y_diff_sign_change = deriv.get_deriv_proof(y_subbed_node_sign_change, separate=True)

    x_proof = x_proof.strip().partition("\n")[-1].rpartition("\n")[0]+"\n"
    x_diff = x_diff.strip().rpartition("\n")[0]+"\n"
    y_proof = y_proof.strip().partition("\n")[-1].rpartition("\n")[0]+"\n"
    y_diff = y_diff.strip().rpartition("\n")[0]+"\n"
    y_proof_sign_change = y_proof_sign_change.strip().partition("\n")[-1].rpartition("\n")[0]+"\n"
    y_diff_sign_change = y_diff_sign_change.strip().rpartition("\n")[0]+"\n"
    
    indent = lambda s: '\n'.join([f"    {l}" for l in s.split('\n')])
    x_proof, x_diff, y_proof, y_diff = list(map(indent, [x_proof, x_diff, y_proof, y_diff]))
    y_proof_sign_change, y_diff_sign_change = list(map(indent, [y_proof_sign_change, y_diff_sign_change]))

    def convert_to_multi_var_diff(diff_string, order):
        replace_dict = {
            "differentiableAt_pow" : f"differentiableAt_{order}.pow",
            "differentiableAt_id" : f"differentiableAt_{order}"
        }
        diff_string = diff_string.strip().rpartition("\n")[-1]
        for key in replace_dict:
            diff_string = diff_string.replace(key, replace_dict[key])
        return diff_string

    multivar_diff_p1 = convert_to_multi_var_diff(x_diff, "fst").strip()
    multivar_diff_p2 = convert_to_multi_var_diff(y_diff, "snd").strip()
    multivar_diff_p2_sign_change = convert_to_multi_var_diff(y_diff_sign_change, "snd").strip()

    m_temp = MultiVarNodeHack(multivar_diff_p1[6:])

    def add_y_nodes_recursively(recurr_node, y_original: func.Node, default):
        if isinstance(y_original, func.Add):
            recurr_node = add_y_nodes_recursively(recurr_node, y_original.children[0], default)
            recurr_node = func.Add([recurr_node, y_original.children[1]])
        elif isinstance(y_original, func.Sub):
            recurr_node = add_y_nodes_recursively(recurr_node, y_original.children[0], default)
            recurr_node = func.Sub([recurr_node, y_original.children[1]])
        else:
            if default == "+":
                recurr_node = func.Add([recurr_node, y_original])
            else:
                recurr_node = func.Sub([recurr_node, y_original])
        return recurr_node
    
    if y_f.leading_operation() == "-":
        pass

    a_temp = add_y_nodes_recursively(m_temp, y_subbed_node_original, "+")
    multivar_diff_f_func = convert_to_multi_var_diff("exact " + a_temp.differentiability(), "snd")

    a_temp = add_y_nodes_recursively(m_temp, y_subbed_node_original, "-")
    multivar_diff_f_func_sign_changed = convert_to_multi_var_diff("exact " + a_temp.differentiability(), "snd")
    #multivar_diff_f_func = "sorry"

    operation = "+"
    operation_name = "add"
    str_y_f = str(y_f)
    str_y_f_sign_change = str(y_f)
    str_dy_f_sign_change = str(dy_f)
    y_proof_to_use = y_proof
    y_diff_to_use = y_diff
    multivar_diff_p2_to_use = multivar_diff_p2
    multivar_diff_f_func_to_use = multivar_diff_f_func
    dx_f_at_a = get_corresponding_constant(dx_f, a)
    dy_f_at_b = get_corresponding_constant(dy_f, b)
    dy_f_at_b_original = dy_f_at_b
    
    if y_f.leading_operation() == "-":
        operation = "-"
        str_y_f_sign_change = y_f.repr_sign_changed()
        str_dy_f_sign_change = dy_f.repr_sign_changed()
        operation_name = "sub"
        y_proof_to_use = y_proof_sign_change
        y_diff_to_use = y_diff_sign_change
        multivar_diff_p2_to_use = multivar_diff_p2_sign_change
        multivar_diff_f_func_to_use = multivar_diff_f_func_sign_changed
        dy_f_at_b = get_corresponding_constant(dy_f_sign_change_poly, b)
        
    sign_of_dy_f_at_b = "+" if dy_f_at_b >= 0 else "-"
    operation_for_eq = operation

    a_to_use = f"{a}" if a >=0 else f"({a})"
    b_to_use = f"{b}" if b >=0 else f"({b})"

    #multivar_diff_f_func_to_use = 'sorry'

    c = "c" # Let's keep c as a constant. As it helps with making sure the equation is a valid equation.
    # I.e. it is hard to make sure that f(a,b) = 0. f(a,b) - c will always be 0 for some c.
    # I am doing this as the point (a,b) needs to be on the curve.
    template = f"""
example (x y {c}: ℝ) : (fderiv ℝ (fun p ↦ {str(x_f).replace('x', 'p.1')} {operation} {str_y_f.replace('x', 'p.2')} - {c}) (({a}:ℝ), ({b}:ℝ)) (x-{a_to_use}, y-{b_to_use}) = 0) → ((x-{a_to_use}) * ({dx_f_at_a}) {operation_for_eq} (y-{b_to_use}) * ({dy_f_at_b}) = 0) := by
  intro h
  rw [fderiv_sub] at h

  have h_split 
  (hp1: DifferentiableAt ℝ (fun p => {str(x_f).replace('x', 'p.1')}) (({a}:ℝ), ({b}:ℝ)))
  (hp2: DifferentiableAt ℝ (fun p => {str_y_f_sign_change.replace('x', 'p.2')}) (({a}:ℝ), ({b}:ℝ))): 
    fderiv ℝ (fun p : ℝ × ℝ => 
      {str(x_f).replace('x', 'p.1')} {operation} {str_y_f.replace('x', 'p.2')}) (({a}:ℝ), ({b}:ℝ))
      = 
      fderiv ℝ (fun p => {str(x_f).replace('x', 'p.1')}) (({a}:ℝ), ({b}:ℝ)) {operation}
      fderiv ℝ (fun p => {str_y_f_sign_change.replace('x', 'p.2')}) (({a}:ℝ), ({b}:ℝ)) := by
    rw [←fderiv_{operation_name}]
    {hsplit_adjust}
    exact hp1
    exact hp2

  rw [h_split] at h
  rw [ContinuousLinearMap.sub_apply] at h
  rw [ContinuousLinearMap.{operation_name}_apply] at h

  have h1 : (fderiv ℝ (fun p => {str(x_f).replace('x', 'p.1')}) (({a}:ℝ), ({b}:ℝ))) (x - {a_to_use}, y - {b_to_use}) = (x-{a_to_use}) * ({dx_f_at_a})  := by
    have hp1comp : (fun p : ℝ × ℝ => {str(x_f).replace('x', 'p.1')}) = (fun x => {str(x_f)}) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    rw [fderiv_fst]
    rw [←deriv_fderiv]
{x_proof}
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_fst']
    field_simp
    {solving_equation_x}
{x_diff}
    exact differentiableAt_fst

  have h2 : (fderiv ℝ (fun p => {str_y_f_sign_change.replace('x', 'p.2')}) (({a}:ℝ), ({b}:ℝ))) (x - {a_to_use}, y - {b_to_use}) = (y-{b_to_use}) * ({dy_f_at_b})  := by
    have hp2comp : (fun p : ℝ × ℝ => {str_y_f_sign_change.replace('x', 'p.2')}) = (fun x => {str_y_f_sign_change}) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    rw [fderiv_snd]
    rw [←deriv_fderiv]
{y_proof_to_use}
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.coe_snd']
    field_simp
    {solving_equation_y}
{y_diff_to_use}
    exact differentiableAt_snd

  have h3 : fderiv ℝ (fun p : ℝ × ℝ => ({c}:ℝ)) (({a}:ℝ), ({b}:ℝ)) (x - {a_to_use}, y - {b_to_use}) = 0 := by
    rw [fderiv_const]
    field_simp

  rw [h1] at h
  rw [h2] at h
  rw [h3] at h
  ring_nf at h
  linarith

  {multivar_diff_p1}
  {multivar_diff_p2_to_use}
  
  {multivar_diff_f_func_to_use}

  exact differentiableAt_const _
"""
    
    return template

def generate_tangent_problems(n):
    file_str = tangent_header
    for i in range(n):
      file_str += generate_random_tangent_instance()
    
    with open('lean/LeanCalc/synthetic/tangents.lean', 'w') as f:
        f.write(file_str)

def generate_extrema_instance():

    # Copying what I had in generate tangent
    class Poly:
        def __init__(self, terms = []):
            self.terms = terms
            if not self.terms:
                # TODO generate randomly
                pass
        def __repr__(self):
            def format_x(c,e):

                if c == 0:
                    return ""

                op = "+ "
                if c < 0:
                    op = "- "
                c = abs(c)
                if e == 0:
                    return op + str(c)

                if c > 1:
                    coeff=f"{c}" + (' * ' if e > 0 else '')
                else:
                    coeff = ""
                if e == 1:
                    p = "x"
                elif e > 1:
                    p = f"x ^ {e}"
                else:
                    p = ""
                return op + coeff + p
            
            return ' '.join([format_x(c,e) for c, e in self.terms])[1:]
    
    class PolyDeriv(Poly):
        def __init__(self, terms):
            self.terms = terms
            for i, (c, e) in enumerate(self.terms):
                self.terms[i] = (c*e, e-1)
            self.terms = [(c,e) for c,e in self.terms if e >= 0]

    # I need three things
    # One: the array denoting the polynomial
    # We will use the format @Devan has been using.
    d = random.randint(3,7)
    polynomial = [(random.randint(-5,5), i) for i in range(1, d+1)]
    p_copy = polynomial[::]
    polynomial = [(1,e) if c==0 else (c,e) for c,e in polynomial]

    random_mask = random.sample(range(len(polynomial)-1), random.randint(2, len(polynomial) - 1))

    polynomial = [term for i,term in enumerate(polynomial) if i in random_mask]

    # leading coeff is positive :D
    if polynomial[-1][0] < 0: polynomial[-1] = (polynomial[-1][0]*-1, polynomial[-1][1])
    polynomial = polynomial[::-1]
    max_degree = max([e for _,e in polynomial])
    
    # Second: We want to generate a Maxima, Minima or SaddlePoint question
    QU_TYPES = ["Maxima", "Minima", "SaddlePoint"]
    if max_degree > 2:
        qu_type = random.choice(QU_TYPES)
    else:
        qu_type = QU_TYPES[1]
    #Third the point at which we are evaluating
    point = random.randint(-6,6)

    fx = Poly(polynomial)
    deriv_fx = PolyDeriv([e for e in fx.terms])
    deriv_deriv_fx = PolyDeriv([e for e in deriv_fx.terms])

    # The cheeky part
    # We convert the polynomial to match the question type
    corresponding_constant = get_corresponding_constant(deriv_deriv_fx, point)
    corresponding_inequality = "="

    if qu_type == QU_TYPES[0]:
        # This is a maxima problem
        # f''(x) < 0
        corresponding_constant = corresponding_constant + random.randint(1, 5)
        if corresponding_constant%2 == 1:
            corresponding_constant += 1
        corresponding_inequality = "<" 
    elif qu_type == QU_TYPES[1]:
        # This is a minima problem
        # f''(x) > 0
        corresponding_constant = corresponding_constant - random.randint(1, 5)
        if corresponding_constant%2 == 1:
            corresponding_constant -= 1
        corresponding_inequality = ">"
    else:
        # This is a saddle point problem
        # f''(x) = 0
        corresponding_constant = corresponding_constant # Basically do nothing

    def subtract_single_expression(fx: Poly, term):
        c_term, e_term = term
        for i, (c,e) in enumerate(fx.terms):
            if e == e_term:
                fx.terms[i] = (c-c_term, e)
                break
        else:
            fx.terms.append((-c_term, e_term))

    # Now subtract this constant from f''(x)
    subtract_single_expression(deriv_deriv_fx, (corresponding_constant, 0))
    # Now we also need to update f'(x) and f(x)
    subtract_single_expression(deriv_fx, (corresponding_constant, 1))
    subtract_single_expression(fx, (corresponding_constant//2, 2))

    # For all extrema points f'(x)=0
    # Therefore we do something similar to f'(x)
    corresponding_constant = get_corresponding_constant(deriv_fx, point)
    # Again update f'(x) and f(x)
    subtract_single_expression(deriv_fx, (corresponding_constant, 0))
    subtract_single_expression(fx, (corresponding_constant, 1))

    fx_subbed_node = deriv.parse(str(fx)).children[0]
    deriv_fx_subbed_node = deriv.parse(str(deriv_fx)).children[0]

    deriv_fx_proof, _, _, deriv_fx_diff = deriv.get_deriv_proof(fx_subbed_node, separate=True)
    deriv_deriv_fx_proof, _, _, deriv_deriv_fx_diff = deriv.get_deriv_proof(deriv_fx_subbed_node, separate=True)

    indent = lambda s: '\n'.join([f"    {l}" for l in s.split('\n')])
    deriv_fx_proof, deriv_fx_diff, deriv_deriv_fx_proof, deriv_deriv_fx_diff = list(map(indent, [
        deriv_fx_proof, deriv_fx_diff, deriv_deriv_fx_proof, deriv_deriv_fx_diff
    ]))

    final_expression = "" if corresponding_inequality == "=" else "norm_num"

    # And we are pretty much done
    # Let's generate the Lean proof
    template = f"""
example (f:ℝ→ℝ) : (f = fun x:ℝ => {str(fx)}) → (deriv f ({point}:ℝ) = 0 ∧ deriv (deriv f) ({point}:ℝ) {corresponding_inequality} 0) := by
  intros hf
  have h_deriv_f : deriv f = fun x => {str(deriv_fx)} := by
    ext x
    rw [hf]
{deriv_fx_proof}
    ring
{deriv_fx_diff}

  have h_deriv_deriv_f : deriv (deriv f) = fun x => {str(deriv_deriv_fx)} := by
    ext x
    rw [h_deriv_f]
{deriv_deriv_fx_proof}
    ring
{deriv_deriv_fx_diff}

  constructor
  nth_rewrite 1 [h_deriv_f]
  ring
  nth_rewrite 1 [h_deriv_deriv_f]
  ring
  {final_expression}
    """

    return template

def generate_extrema_problems(n):
    file_str = extrema_headers
    for i in range(n):
      file_str += generate_extrema_instance()
    
    with open('lean/LeanCalc/synthetic/extrema_problems.lean', 'w') as f:
        f.write(file_str)

def check_valid(lines: list[str]) -> bool:
    import subprocess, json, os, time
    # RUN FROM ROOT
    if os.getcwd().endswith("calc4lean"): os.chdir("./lean")
    os.makedirs("LeanCalc/synthetic/tmp", exist_ok=True)
    file_path = f"LeanCalc/synthetic/tmp/tmp.lean"
    # creates the temp lean file and writes to it
    with open(file_path, "w") as lean_file:
        lean_file.writelines(lines)
    lean_file.close()
    # gets proof state back from lean compiler
    result = subprocess.run(
        ["bash", "-c", f"echo '{{\"path\": \"{file_path}\", \"allTactics\": true}}' | lake exe repl"],
        text=True,
        capture_output=True,
        check=True
    )
    # Delete Temp Lean file
    # os.remove(file_path)
    # load to dict
    result_json = json.loads(result.stdout)
    return result_json
    # see if any messages are error message
    # return any({msg['severity'] == 'error' for msg in result_json['messages']})

def clean_mistakes(file: str):
    import tqdm as tqdm

    with open('lean/' + file, 'r') as f:
        lines = f.readlines()
    
    print("Round 1 Cleaning")
    r = check_valid(lines)
    errors = list(filter(lambda msg: msg['severity'] == 'error', r['messages']))
    original = len(errors)
    for err in errors:
      ln = err['pos']['line'] - 1
      if 'Function.comp_def' in lines[ln - 1]:
          lines[ln - 1] = re.sub(r'\d+', lambda m: str(int(m.group()) + 1), lines[ln - 1])
    
    print("Round 2 Cleaning")
    r = check_valid(lines)
    errors = list(filter(lambda msg: msg['severity'] == 'error', r['messages']))
    if not errors:
        with open(file, 'w') as f:
            f.writelines(lines)
    for err in errors:
      ln = err['pos']['line'] - 1
      if 'field_simp' in lines[ln - 1]:
          lines[ln - 1] = '-- ' + lines[ln - 1]
      elif 'field_simp' in lines[ln - 2]:
          lines[ln - 2] = '-- ' + lines[ln - 2]
    
    print("Round 3 Cleaning")
    r = check_valid(lines)
    errors = list(filter(lambda msg: msg['severity'] == 'error', r['messages']))
    if not errors:
        with open(file, 'w') as f:
            f.writelines(lines)
    for err in errors:
      ln = err['pos']['line'] - 1
      if 'Function.comp_def' in lines[ln - 1]:
          lines[ln - 1] = re.sub(r'\d+', lambda m: str(int(m.group()) + 1), lines[ln - 1])
    
    print("Checking Result")
    r = check_valid(lines)
    errors = list(map(lambda msg: msg['severity'] == 'error', r['messages']))
    print("Done")
    if len(errors) < original:
        with open(file, 'w') as f:
            f.writelines(lines)

def shitty_cleanup_script(file: str = 'lean/LeanCalc/synthetic/seed_2.lean'):
    fs, _, ts, ps = parse_functions(file)
    ref_fs, _, _, ref_ps = parse_functions('lean/LeanCalc/synthetic/seed_1_1.lean')
    hm = {}
    lookback=5
    for p in ref_ps:
        proof = p.split('\n')
        i, j = 0, 0
        while i < len(proof) and j < len(proof):
            if 'Function.comp_def' in proof[j]:
                block = '\n'.join(proof[max(j-lookback, i):j])
                if block not in hm:
                    hm[block] = proof[j]
                i = j
            j += 1
    
    for k in range(len(ps)):
        p = ps[k]
        proof = p.split('\n')
        i, j = 0, 0
        while i < len(proof) and j < len(proof):
            if 'Function.comp_def' in proof[j]:
                block = '\n'.join(proof[max(j-lookback, i):j])
                if block in hm:
                    proof[j] = hm[block]  # replace
                i = j
            j += 1
        ps[k] = '\n'.join(proof)

    file_str = header
    for theorem, proof in zip(ts, ps):
        file_str += theorem + proof + '\n\n'
    
    with open(f'lean/LeanCalc/synthetic/seed_2.lean', 'w') as f:
        f.write(file_str)

# create_seed(funcs, funcs_derivs)
# clean_mistakes("LeanCalc/synthetic/seed_1.lean")

# fs, dfs, ts, ps = parse_functions('lean/LeanCalc/synthetic/seed_1.lean')
# create_seed(fs, dfs, 'seed_1_1')
# clean_mistakes("LeanCalc/synthetic/seed_1_1.lean")
# nfs, ndfs, nts, nps = parse_functions('lean/LeanCalc/synthetic/seed_1_1.lean')
# print(len(fs), len(nfs))
            
# with open("lean/LeanCalc/synthetic/seed_1_1.lean", 'r') as f:
#     lines = f.readlines()
# with open("lean/LeanCalc/synthetic/seed_1_1.lean", 'w') as f:
#     f.writelines(
#         [
#             ln for ln in lines if '--' not in ln
#         ]
#     )

# generate_monotonicity_simple(n = 100) # 4*5 -> 20
# generate_monotonicity_shifted(n = 100) # -> 20
#generate_pq_easy(10)

# TODO implement 
# generate_random_tangent_instance()
generate_tangent_problems(170)
generate_extrema_problems(170)
            
# fs, dfs, ts, ps = parse_functions('lean/LeanCalc/synthetic/seed2_good.lean')
# print(len(fs))         
# expand_seed(funcs, fs)
  
# shitty_cleanup_script()
