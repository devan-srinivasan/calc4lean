"""
This is a BIG FILE, collapse all the classes PLEASE
While intimidating, it is quite straightforward. I have written a shitty parser
that takes a math expr, and converts it to AST. below is the definitions for all the node types

Essentially, to generate a proof we do the following.
To prove derivatives (rw [deriv_...]) we just follow the AST recursing top->down
To prove differentiability, we notice that only operations and some functions introduce the DifferentiableAt... goals
In lean, as we use rw [deriv_...] these DifferentiableAt... goals are introduced, for some lemmas (not all). For example
    differentiableAt_mul introduces the hyp that f, g are both Differentiable, where as differentiableAt_id obviously doesn't

So when we do the derivative, going top->down, as we hit those functions that introduce goals, we add the SOLUTION LEMMAS to a stack (that is passed)
as argument, in order that the goals are introduced. So for ex. differentiableAt_div introduces goals
    DifferentiableAt f, DifferentiableAt g, g != 0 <- in that order (R -> L), so we add to the stack, exact h_g_ne_zero, exact differentiableAt_g, exact differentiableAt_f

i also implemented differentiation with chain rule to compute an expression's derivative, but you can pass in the precomputed form
as derivative_repr attribute and it will use that and not compute the actual derivative. in practice the returned derivative, as a string, 
is very brackety. so i clean it, and now also create a new AST based on it, reduce it, and then call clean() on that serialization. it will reduce like
((2)*x^(2-1)) to (2*x)

next, a minor thing, each function at most requires 1 hypothesis (given the constraints of our work), and that is that it's argument doesn't equal 0
this only applies for Tan, Div, and Log. For these, they introduce their own hypothesis, named as hyp_[func]_ne_zero_[id] where func is the node type (div, tan, log)
and [id] is the node's unique id (assigned AFTER parsing later on)

the last piece to this puzzle is some helper stuff. 
    __repr__ prints the object nicely, for VSCode debugger and serializing back to str
    reduce() reduces the AST as best as possible by removing obvious things like [...]^1 = [...], [ ]*0 = 0, etc. (thats what is_zero() and is_one() functions are for)
    field_simp_str() and hypothesis_str() get the field_simp [h1, ...] and hypothesis strings (for theorem statement) using recursion
    clean() is a function (that should be outside the Node class tbh) that just cleans the serialized strings. this was made before i wrote the 
        reduce() function, so it just removed brackets, removed the R (real) symbol, and did some other heuristic things because before my serialized
        strings were very brackety. Since then I have improved things, but still just call clean usually...just in case. now i am almost positive that
        reduce() does everything already

the regular way to use this code (how its basically used everywhere) is as follows: NOTE i got rid of x0, everything is x

func = "x^2 + 3 * sin x"                    <-- lean function
node = deriv.parse(func).children[0]        <-- we say children[0] because parse returns Node() as the root, but we don't actually need that, we want the actual root (in this case Add) which is the outermost operation
node.derivative()                           <-- computes the lean expression for the derivative, often very brackety
deriv.get_deriv_proof(node, separate=False) <-- will get the classic lean proof (not theorem)

deriv_node = deriv.parse(node.derivative()).children[0]     <-- this will create a new AST for the function's derivative, i.e. 2*x + 3 * cos x
deriv_node = deriv_node.reduce()                            <-- reduce it
cleaned_derivative = deriv_node.clean(str(deriv_node))      <-- just in case, we call clean to clean it, then str(deriv_node) is just deriv_node.__repr__()...aka the serialization for the (now reduced) AST

so then you can construct problems like:

example (x: R) {node.get_hypotheses_str} deriv (fun x -> {str(node)}) = {str(node.derivative)} := by
    {deriv.get_deriv_proof(node, separate=False)}

and hypothetically, if you copy-pasted that to a .lean file, it works terrific :D
"""
# these are helper functions to parse string pieces into objects
# i.e. (...) -> Expr whose child is ...
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
        # simplify where we can
        s = re.sub(r'\((\d+):ℝ\)\s*\+\s*\((\d+):ℝ\)', lambda m: f"({int(m[1]) + int(m[2])}:ℝ)", s)
        s = re.sub(r'\((\d+):ℝ\)\s*-\s*\((\d+):ℝ\)', lambda m: f"({int(m[1]) - int(m[2])}:ℝ)", s)
        s = re.sub(r'\((\d+):ℝ\)\s*\*\s*\((\d+):ℝ\)', lambda m: f"({int(m[1]) * int(m[2])}:ℝ)", s)
        # s = re.sub(r'\((\d+):ℝ\)\s*/\s*\((\d+):ℝ\)', lambda m: f"({int(m[1]) / int(m[2])}:ℝ)", s)
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
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.children[0].is_zero() or self.children[1].is_zero():
            return Const("0")
        if isinstance(self.children[0], Const) and isinstance(self.children[1], Const):
            return Const(str(int(self.children[0].value) * int(self.children[1].value)))
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
        if self.is_one(): return Const("1")
        if isinstance(self.children[0], Const) and isinstance(self.children[1], Const):
            return Const(str(int(self.children[0].value) + int(self.children[1].value)))
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
        if self.is_one(): return Const("1")
        if isinstance(self.children[0], Const) and isinstance(self.children[1], Const):
            return Const(str(int(self.children[0].value) - int(self.children[1].value)))
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
        if self.is_one(): return Const("1")
        # if isinstance(self.children[0], Const) and isinstance(self.children[1], Const):
        #     assert(not self.children[1].value == "0")
        #     return int(self.children[0].value) / int(self.children[1].value)
        if self.children[0].is_one(): self.children[0] = Const("1")
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
    def is_one(self): return self.children[1].is_zero()

    def reduce(self):
        self.children[0] = self.children[0].reduce()
        self.children[1] = self.children[1].reduce()
        if self.is_zero(): return Const("0")
        if self.is_one(): return Const("1")
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
        if self.is_one(): return Const("1")
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
        if self.is_one(): return Const("1")
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
            raise ValueError("Cannot compose with tan, haven't figured that out yet!")
            # return f"DifferentiableAt.tan ({self.children[0].differentiability()}) ({self.hyp_ne_zero})"
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
        if self.is_one(): return Const("1")
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
        if self.is_one(): return Const("1")
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
        if self.is_one(): return Const("1")
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