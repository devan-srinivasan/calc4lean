import func, deriv, json

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

funcs = [
    "(Real.exp x) * (x^2 + 3)",
    "Real.cos (Real.log x)",
    "(Real.sin (2 * x - 1))^2",
    "(x ^ 3) * (Real.log x / Real.log 5)",
    "(Real.log (5 * x + 2)) ^ 3",
    "Real.tan (5 * x)",
]

funcs_derivs = [
    "(exp x) * (x^2 + 2 * x + 3)",
    "(-1) * sin (log x) / x",
    "4 * sin (2 * x - 1) * cos (2 * x - 1)",
    "3 * x ^ 2 * (Real.log x + 1) / Real.log 5",
    "15 * (Real.log (5 * x + 2)) ^ 2 / (5 * x + 2)",
    "5 / cos (5 * x) ^ 2",
]

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
                problems.append((
                    f"example (x: ℝ) {n.hypotheses_str()}: deriv (λ x ↦ {n.clean(n.__repr__())}) x = {n.clean(str(deriv_node))} := by", # theorem
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

def generate_pq_easy(n):
    
    a, b, c, d = 1, 9, 6, 1
    mu = 3
    template = f"""
example (x: ℝ) (p q : ℝ → ℝ) (h0 : p 0 = q 0 ∧ q 0 > 0) (hf': ∀ y:ℝ, (deriv p y) * (deriv q y) = {d})
  (hqDeriv: Differentiable ℝ q) (hpDeriv: Differentiable ℝ p)
  (hP: ∀ y:ℝ, deriv p y > 0) (hD: x ∈ Icc (0: ℝ) (1: ℝ)): p x + {b} * q x > {c} * x := by
  let f := (λ x ↦ p x + 9 * q x - {c} * x)
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
        have hf'_iff: deriv p x2 * deriv q x2 = 1 ↔ deriv q x2 = {d} / deriv p x2 := by
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
              = deriv p x2 ^ 2 + {b} - {c} * deriv p x2 := by
        field_simp [hpX2]
        ring
      have quad_sq : deriv p x2 ^ 2 + {b} - {c} * deriv p x2 = (deriv p x2 - {mu}) ^ 2 := by ring
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
    
    file_str = monotone_header
    # TODO
            # p = Poly()
            # problem_str = p.get_monotonicity_problem()
            # problem_str = problem_str.replace('\t', '  ')   # no tabs
            # file_str += problem_str
    
    with open('lean/LeanCalc/synthetic/pq_easy.lean', 'w') as f:
        f.write(file_str)

def generate_tangent(n):
    
    x_portion = 'p.1 ^ 2 + p.1'
    y_portion = 'p.2 ^ 2'
    point = (3,4)

    x_subbed_node = deriv.parse(x_portion.replace('p.1', f"(x - {point[0]})")).children[0]
    y_subbed_node = deriv.parse(y_portion.replace('p.2', f"(x - {point[1]})")).children[0]

    deriv_x_subbed_node = deriv.parse(x_subbed_node.derivative()).children[0].reduce()
    deriv_y_subbed_node = deriv.parse(y_subbed_node.derivative()).children[0].reduce()

    dir_deriv_x_subbed_node = func.Mul(children=[func.Const(str(point[0])), func.Expr(children=[deriv_x_subbed_node])]).reduce()
    dir_deriv_y_subbed_node = func.Mul(children=[func.Const(str(point[1])), func.Expr(children=[deriv_y_subbed_node])]).reduce()

    c = 25
    template = f"""
example (x y : ℝ) : (fderiv ℝ (fun p ↦ {x_portion} + {y_portion} - {c}) (x-{point[0]}, y-{point[1]}) ({point[0]}, {point[1]}) = 0) → ({dir_deriv_x_subbed_node.clean(str(dir_deriv_x_subbed_node))} + {dir_deriv_y_subbed_node.clean(str(dir_deriv_y_subbed_node)).replace("x", "y")} = 0) := by
  intro h
  rw [fderiv_sub, fderiv_add] at h
  simp at h

  have h1 : fderiv ℝ (fun p : ℝ × ℝ => {x_portion}) (x-{point[0]}, y-{point[1]}) ({point[0]}, {point[1]}) = {dir_deriv_x_subbed_node.clean(str(dir_deriv_x_subbed_node))} := by
    have hp1comp : (fun p : ℝ × ℝ => {x_portion}) = (fun x => {x_portion.replace("p.1", "x")}) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    simp [fderiv_fst]
    ring
    exact differentiableAt_pow _
    exact differentiableAt_fst

  have h2 : fderiv ℝ (fun p : ℝ × ℝ => {y_portion}) (x-{point[0]}, y-{point[1]}) ({point[0]}, {point[1]}) = {dir_deriv_y_subbed_node.clean(str(dir_deriv_y_subbed_node)).replace("x", "y")}  := by
    have hp2comp : (fun p : ℝ × ℝ => {y_portion}) = (fun y => {y_portion.replace("p.2", "y")}) ∘ (fun p => p.2) := rfl
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
"""
    
    file_str = monotone_header
    # TODO
            # p = Poly()
            # problem_str = p.get_monotonicity_problem()
            # problem_str = problem_str.replace('\t', '  ')   # no tabs
            # file_str += problem_str
    
    file_str += template
    
    with open('lean/LeanCalc/synthetic/multivar.lean', 'w') as f:
        f.write(file_str)
# expand_generic_op(funcs[:-1], funcs_derivs[:-1])  # -> 40
# expand_generic_comp(funcs, funcs_derivs) # -> 25
# generate_monotonicity_simple(min_deg=2, max_deg=6, n_per_deg=5) # 4*5 -> 20
# generate_monotonicity_shifted(n=20) # -> 20
        
generate_tangent(1)