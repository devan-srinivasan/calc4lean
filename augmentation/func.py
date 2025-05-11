def parse_brackets(tokens):
    def helper(index):
        items = []
        start_index = index

        while index < len(tokens):
            token = tokens[index]

            if token == '(':
                # Start of nested Bracket
                nested, index = helper(index + 1)
                items.append(nested)
            elif token == ')':
                # End of current Bracket
                bracket = Expr(children=items)
                return bracket, index + 1
            else:
                items.append(token)
                index += 1

        return items, index  # for top-level unwrapped terms

    result, _ = helper(0)
    return result if isinstance(result, list) else [result]

def parse_pow(tokens):
    i = 0
    while i < len(tokens) - 2:
        if tokens[i + 1] == '^':
            tokens[i: i+3] = [Pow(children=[tokens[i], tokens[i+2]])]
            continue
        i += 1
    return tokens

def parse_func(tokens):
    i = len(tokens) - 2 
    while i >= 0:
        if isinstance(tokens[i], str) and tokens[i].isalpha():
            tokens[i:i+2] = [FUNC_NODES[tokens[i]](children=[tokens[i+1]])]
        i -= 1
    return tokens

def parse_op(tokens):
    i = 0
    while i < len(tokens) - 2:
        if tokens[i + 1] in {'*', '/'}:
            tokens[i: i+3] = [OP_NODES[tokens[i+1]](children=[tokens[i], tokens[i+2]])]
            continue
        i += 1

    i = 0
    while i < len(tokens) - 2:
        if tokens[i + 1] in {'+', '-'}:
            tokens[i: i+3] = [OP_NODES[tokens[i+1]](children=[tokens[i], tokens[i+2]])]
            continue
        i += 1
    return tokens

class Node:
    def __init__(self, children: list = [], derivative_repr: str = ''):
        self.hyp_ne_zero = ''
        self.derivative_repr = derivative_repr
        self.children = children
        self.differentiability_proof = []
    
    def parse(self):
        if not self.children: return
        self.children = parse_brackets(self.children)
        self.children = parse_pow(self.children)
        self.children = parse_func(self.children)
        self.children = parse_op(self.children)
        for c in self.children:
            if isinstance(c, Node):
                c.parse()
        return
    
    def assign_ids(self):
        counter = [0]  # Use a mutable object to maintain count across recursive calls

        def dfs(node):
            node.id = counter[0]
            if node.hyp_ne_zero:
                node.hyp_ne_zero = f"{node.hyp_ne_zero}_{node.id}"
            counter[0] += 1

            for child in node.children:
                dfs(child)

        dfs(self)

    def deriv_proof(self):
        proof, subproofs = self.children[0].deriv_proof(stack=[])
        subproofs.reverse()
        diff_proof = []
        for s in subproofs:
            for ln in s:
                if ln: diff_proof.append('exact ' + ln)
        diff_proof = '\n'.join(diff_proof)

        return proof, diff_proof
    
    def differentiability(self):
        return self.children[0].differentiability()
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return self.children[0].derivative()
    
    def clean(self, s: str) -> str:
        import re

        # Step 2: Remove unnecessary outer brackets like ((...)) → (...)
        def remove_outer_brackets(expr: str) -> str:
            stack = []
            remove_indices = set()
            i = 0
            while i < len(expr):
                if s[i] == '(':
                    stack.append(i)
                    i += 1
                    continue
                if s[i] == ')':
                    # we pop then look ahead
                    j = i+1
                    i_ = stack.pop() - 1
                    while s[i_] == '(' and s[j] == ')':
                        stack.pop() # remove it
                        remove_indices.add(i_)
                        remove_indices.add(j)
                        j += 1
                        i_ -= 1
                    i = j
                    continue
                i += 1
            return ''.join(c for i, c in enumerate(s) if i not in remove_indices)

        s = remove_outer_brackets(s)
        s = s.replace("(x)", "x")
        s = re.sub(r'\((\d+)\)', r'\1', s)
        for pattern in [" * 1", " ^ 1", " + 0", " - 0", " / 1"]:
            s = s.replace(pattern, "")
        s = re.sub(r'\(\(([^()]+)\)\)', r'(\1)', s)
        return s
    
    def field_simp_str(self) -> bool:
        hyps = self.get_hyps()
        if hyps:
            return f"field_simp [{', '.join(list(map(lambda x:x[0], hyps)))}]\n"
        else:
            return ''

    def hypotheses_str(self) -> bool:
        hyps = self.get_hyps()
        hyp_str = ""
        for hyp in hyps:
            hyp_str += f" ({hyp[0]}: {hyp[1]} ≠ 0)"
        return hyp_str

    def get_hyps(self):
        hyps = []
        if self.hyp_ne_zero:
            hyps.append((self.hyp_ne_zero, self.children[-1].__repr__()))
        for c in self.children:
            c_hyps = c.get_hyps()
            if c_hyps: hyps.extend(c_hyps)
        return hyps
   
class Const(Node):
    def __init__(self, value: int):
        super().__init__()
        self.value = value
        self.children = []

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_const]\n", stack
    
    def differentiability(self):
        return "differentiableAt_const _"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return "0"
    
    def continuity(self):
        return "continuous_const"
    
    def __repr__(self, as_pow=False) -> str:
        if not as_pow: return f"({self.value}:ℝ)"
        else: return f"{self.value}"    # as natural

    def is_zero(self): return self.value == '0'
    def is_one(self): return self.value == '1'
    def reduce(self): return self

class Expr(Node):

    def deriv_proof(self, stack):
        proof, stack = self.children[0].deriv_proof(stack)
        return proof, stack

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"({self.children[0].__repr__()})"
    
    def is_zero(self): return self.children[0].is_zero()
    def is_one(self): return self.children[0].is_one()

    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if type(self.children[0]) in {Const, Expr, Exp, Log, Sin, Cos, Tan, ID}:
            return self.children[0]
        return self

class ID(Node):

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_id'']\n", stack
    
    def differentiability(self):
        return "differentiableAt_id"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return "1"
    
    def continuity(self):
        return "continuous_id"
    
    def __repr__(self):
        return "x"
    
    def is_zero(self): return False
    def is_one(self): return False
    def reduce(self): return self

class Mul(Node):

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability()
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_mul]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.mul ({self.children[0].differentiability()}) ({self.children[1].differentiability()})"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"(({self.children[0].derivative()}) * ({self.children[1].__repr__()})) + (({self.children[0].__repr__()}) * ({self.children[1].derivative()}))"
    
    def continuity(self):
        return f"Continuous.mul ({self.children[0].continuity()}) ({self.children[1].continuity()})"

    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} * {self.children[1].__repr__()}"
    
    def is_zero(self): return self.children[0].is_zero() or self.children[1].is_zero()
    def is_one(self): return self.children[0].is_one() and self.children[1].is_one() # or they cancel (?)

    def reduce(self):
        if self.id == 19: 
            print()
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.children[0].is_zero() or self.children[1].is_zero():
            return Const("0")
        if self.children[1].is_one(): return self.children[0]
        if self.children[0].is_one(): return self.children[1]
        return self
        
class Add(Node):

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability()
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_add]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.add ({self.children[0].differentiability()}) ({self.children[1].differentiability()})"

    def continuity(self):
        return f"Continuous.add ({self.children[0].continuity()}) ({self.children[1].continuity()})"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"{self.children[0].derivative()} + {self.children[1].derivative()}"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} + {self.children[1].__repr__()}"
    
    def is_zero(self): return self.children[0].is_zero() and self.children[1].is_zero()
    def is_one(self): return (self.children[0].is_one() and self.children[1].is_zero()) or (self.children[1].is_one() and self.children[0].is_zero())
    
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        if self.children[0].is_zero(): return self.children[1]
        if self.children[1].is_zero(): return self.children[0]
        return self

class Sub(Node):

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability()
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_sub]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.sub ({self.children[0].differentiability()}) ({self.children[1].differentiability()})"

    def continuity(self):
        return f"Continuous.sub ({self.children[0].continuity()}) ({self.children[1].continuity()})"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"{self.children[0].derivative()} - ({self.children[1].derivative()})"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} - {self.children[1].__repr__()}"
    
    def is_zero(self): return self.children[0].is_zero() and self.children[1].is_zero()
    def is_one(self): return self.children[0].is_one() and self.children[1].is_zero()
    
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        if self.children[0].is_zero(): return Mul(children=[Const(-1), self.children[1]])
        if self.children[1].is_zero(): return self.children[0]
        return self

class Div(Node):
    def __init__(self, children: list[Node], derivative_repr: str = '', hyp_ne_zero: str = ''):
        super().__init__(children, derivative_repr)
        self.hyp_ne_zero = hyp_ne_zero if hyp_ne_zero else 'h_div_ne_zero'

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability(),
            f'{self.hyp_ne_zero}'
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_div]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.div ({self.children[0].differentiability()}) ({self.children[1].differentiability()}) ({self.hyp_ne_zero})"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"(({self.children[0].derivative()}) * ({self.children[1].__repr__()}) - ({self.children[0].__repr__()}) * ({self.children[1].derivative()})) / ({self.children[1].__repr__()})^2"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} / {self.children[1].__repr__()}"
    
    def is_zero(self): return self.children[0].is_zero()
    def is_one(self): return self.children[0].is_one() and self.children[1].is_one() # or they equal

    def reduce(self):
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        if self.children[0].is_one(): self.children[0] = Const(1)
        if self.children[1].is_one(): return self.children[0]
        return self

class Pow(Node):

    def deriv_proof(self, stack):
        # if not isinstance(self.children[0], ID):
        self.differentiability_proof = [self.children[0].differentiability()]
        stack.append(self.differentiability_proof)
        proof, stack = self.children[0].deriv_proof(stack)
        return "nth_rewrite 1 [deriv_pow'']\n" + proof, stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.pow ({self.children[0].differentiability()}) _"
        return "differentiableAt_pow _"
    
    def continuity(self):
        return f"Continuous.pow ({self.children[0].continuity()}) _"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"{self.children[1].value} * ({self.children[0].__repr__()}) ^ ({int(self.children[1].value) - 1}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} ^ {self.children[1].__repr__(as_pow=True)}"
    
    def is_zero(self): return self.children[0].is_zero()
    def is_one(self): return self.children[1].is_one()

    def reduce(self):
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        if self.children[1].is_one(): return self.children[0]
        return self

class Sin(Node):

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                'Real.differentiableAt_sin',
                self.children[0].differentiability()
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_sin]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_sin]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.sin ({self.children[0].differentiability()})"
        return "Real.differentiableAt_sin"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"Real.cos ({self.children[0].__repr__()}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.sin ({self.children[0].__repr__()})"
    
    def is_zero(self): return self.children[0].is_zero()
    def is_one(self): return False

    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        return self
    
class Cos(Node):

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                'Real.differentiableAt_cos',
                self.children[0].differentiability()
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_cos]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_cos]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.cos ({self.children[0].differentiability()})"
        return "Real.differentiableAt_cos"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"(-1) * Real.sin ({self.children[0].__repr__()}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.cos ({self.children[0].__repr__()})"
    
    def is_zero(self): return False
    def is_one(self): return self.children[0].is_zero()
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        return self

class Tan(Node):
    def __init__(self, children: list[Node], derivative_repr: str = '', hyp_ne_zero: str = ''):
        super().__init__(children, derivative_repr)
        self.hyp_ne_zero = hyp_ne_zero if hyp_ne_zero else 'h_tan_ne_zero'

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                f'Real.differentiableAt_tan.mpr ({self.hyp_ne_zero})',
                self.children[0].differentiability()
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_tan]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_tan]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.tan ({self.children[0].differentiability()}) ({self.hyp_ne_zero})"
        return f"Real.differentiableAt_tan.mpr ({self.hyp_ne_zero})"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"{self.children[0].derivative()} / (Real.cos ({self.children[0].__repr__()}))^2"
    
    def __repr__(self) -> str:
        return f"Real.tan ({self.children[0].__repr__()})"
    
    def get_hyps(self):
        hyps = []
        if self.hyp_ne_zero:
            hyps.append((self.hyp_ne_zero, f"Real.cos {self.children[-1].__repr__()}"))
        for c in self.children:
            c_hyps = c.get_hyps()
            if c_hyps: hyps.extend(c_hyps)
        return hyps
    
    def is_zero(self): return self.children[0].is_zero()
    def is_one(self): return False
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        return self

class Exp(Node):

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                'Real.differentiableAt_exp',
                self.children[0].differentiability()
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_exp]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_exp]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.exp ({self.children[0].differentiability()})"
        return "Real.differentiableAt_exp"
    
    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"Real.exp ({self.children[0].__repr__()}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.exp ({self.children[0].__repr__()})"
    
    def is_zero(self): return False
    def is_one(self): return self.children[0].is_zero()
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        return self

class Log(Node):
    def __init__(self, children: list[Node], derivative_repr: str = '', hyp_ne_zero: str = ''):
        super().__init__(children, derivative_repr)
        self.hyp_ne_zero = hyp_ne_zero if hyp_ne_zero else 'h_log_ne_zero'
        self.children = children
        self.differentiability_proof = []

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                f'Real.differentiableAt_log ({self.hyp_ne_zero})',
                self.children[0].differentiability(),
                # f'{self.hyp_ne_zero}'
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_log]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_log]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.log ({self.children[0].differentiability()}) ({self.hyp_ne_zero})"
        return f"Real.differentiableAt_log ({self.hyp_ne_zero})"

    def derivative(self):
        if self.derivative_repr: return self.derivative_repr
        return f"({self.children[0].derivative()}) / ({self.children[0].__repr__()})"
    
    def __repr__(self) -> str:
        return f"Real.log ({self.children[0].__repr__()})"
    
    def is_zero(self): return self.children[0].is_one()
    def is_one(self): return False
    def reduce(self):
        self.children[0] = self.children[0].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const(1)
        return self

FUNC_NODES = {
    'Real.sin': Sin,
    'Real.cos': Cos,
    'Real.tan': Tan,
    'Real.exp': Exp,
    'Real.log': Log,
    'sin': Sin,
    'cos': Cos,
    'tan': Tan,
    'exp': Exp,
    'log': Log,
}

OP_NODES = {
    '*': Mul,
    '+': Add,
    '-': Sub,
    '/': Div
}