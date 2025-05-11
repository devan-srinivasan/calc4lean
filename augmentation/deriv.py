class Node:
    def __init__(self, children: list,  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
    
    def parse(self):
        if not self.children: return
        self.children = parse_brackets(self.children)
        self.children = parse_exp(self.children)
        self.children = parse_func(self.children)
        self.children = parse_op(self.children)
        for c in self.children:
            if isinstance(c, Node):
                c.parse()

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
    
    def has_nontrivial_div(self) -> bool:
        if isinstance(self, Div) and not isinstance(self.children[1], Const): 
            return True
        return any([child.has_nontrivial_div() for child in self.children])
    
    def derivative(self):
        return self.children[0].derivative()
   
class Const(Node):
    def __init__(self, value: int,  parsed: bool = False):
        self.value = value
        
        self.children = []
        self.parsed = parsed

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_const]\n", stack
    
    def differentiability(self):
        return "differentiableAt_const _"
    
    def derivative(self):
        return "0"
    
    def __repr__(self) -> str:
        return f"{self.value}"

class Expr(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed

    def deriv_proof(self, stack):
        proof, stack = self.children[0].deriv_proof(stack)
        return proof, stack

    def derivative(self):
        return f"({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"({self.children[0].__repr__()})"

class ID(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_id'']\n", stack
    
    def differentiability(self):
        return "differentiableAt_id"
    
    def derivative(self):
        return "1"
    
    def __repr__(self):
        return "x"

class Mul(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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
        return f"(({self.children[0].derivative()}) * ({self.children[1].__repr__()})) + (({self.children[0].__repr__()}) * ({self.children[1].derivative()}))"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} * {self.children[1].__repr__()}"

class Add(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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

    def derivative(self):
        return f"({self.children[0].derivative()}) + ({self.children[1].derivative()})"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} + {self.children[1].__repr__()}"
    
class Sub(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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

    def derivative(self):
        return f"({self.children[0].derivative()}) - ({self.children[1].derivative()})"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} - {self.children[1].__repr__()}"

class Div(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability(),
            f'h_div_ne_zero'
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_div]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.div ({self.children[0].differentiability()}) ({self.children[1].differentiability()}) (h_ne_zero)"
    
    def derivative(self):
        return f"(({self.children[0].derivative()}) * ({self.children[1].__repr__()}) - ({self.children[0].__repr__()}) * ({self.children[1].derivative()})) / ({self.children[1].__repr__()})^2"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} / {self.children[1].__repr__()}"

class Pow(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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
    
    def derivative(self):
        return f"{self.children[1].value} * ({self.children[0].__repr__()}) ^ ({self.children[1].value - 1}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"{self.children[0].__repr__()} ^ {self.children[1].__repr__()}"

class Sin(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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
        return f"Real.cos ({self.__repr__()}) * ({self.children[1].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.sin ({self.children[0].__repr__()})"
    
class Cos(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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
        return f"-Real.sin ({self.__repr__()})) * ({self.children[1].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.cos ({self.children[0].__repr__()})"

class Tan(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                'Real.differentiableAt_tan.mpr (h_tan_ne_zero)',
                self.children[0].differentiability()
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_tan]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_tan]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.tan ({self.children[0].differentiability()}) (h_tan_ne_zero)"
        return "Real.differentiableAt_tan.mpr (h_tan_ne_zero)"
    
    def derivative(self):
        return f"1 / (Real.cos ({self.children[1].derivative()}))^2"
    
    def __repr__(self) -> str:
        return f"Real.tan ({self.children[0].__repr__()})"

class Exp(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

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
        return f"Real.exp ({self.children[0].__repr__()}) * ({self.children[0].derivative()})"
    
    def __repr__(self) -> str:
        return f"Real.exp ({self.children[0].__repr__()})"

class Log(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

    def deriv_proof(self, stack):
        if not isinstance(self.children[0], ID):
            self.differentiability_proof = [
                'Real.differentiableAt_log (h_log_ne_zero)',
                self.children[0].differentiability(),
                'h_log_ne_zero'
            ]
            stack.append(self.differentiability_proof)
            addition, stack = self.children[0].deriv_proof(stack)
            proof = "nth_rewrite 1 [← Function.comp_def]\nnth_rewrite 1 [deriv_comp]\nnth_rewrite 1 [Real.deriv_log]\n" + addition
            return proof, stack
        return "nth_rewrite 1 [Real.deriv_log]\n", stack
    
    def differentiability(self):
        if not isinstance(self.children[0], ID):
            return f"DifferentiableAt.log ({self.children[0].differentiability()}) (h_log_ne_zero)"
        return "Real.differentiableAt_log (h_log_ne_zero)"

    def derivative(self):
        return f"({self.children[0].derivative()}) / ({self.children[0].__repr__()})"
    
    def __repr__(self) -> str:
        return f"Real.log ({self.children[0].__repr__()})"

# TODO add the rest of the functions

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

def parse_exp(tokens):
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

def parse_numbers_and_ID(tokens):
    for i in range(len(tokens)):
        if isinstance(tokens[i], str) and tokens[i].isnumeric():
            tokens[i] = Const(value=tokens[i])
        elif isinstance(tokens[i], str) and tokens[i] == 'x':
            tokens[i] = ID(children=[])
    return tokens

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

def tokenize(function: str):
    chars = list[Node](function)
    for i, c in enumerate(chars):
        if c == '(' and i+1 < len(chars) and chars[i+1] != ' ':
            chars.insert(i+1, ' ')
        if c == ')' and i-1 > 0 and chars[i-1] != ' ':
            chars.insert(i, ' ')
        if c in {'^', '+', '-', '*', '/'}:
            if i+1 < len(chars) and chars[i+1] != ' ':
                chars.insert(i+1, ' ')
            if i-1 >= 0 and chars[i-1] != ' ':
                chars.insert(i, ' ')
    function = ''.join(chars).split()
    return [t for t in function if t.strip()]

function = 'log x * exp x'

def parse(func: str):
    tokens = tokenize(function)
    tokens = parse_numbers_and_ID(tokens)

    root = Node(children=tokens)
    root.parse()
    return root

def get_deriv_proof(func: str):
    root = parse(func)
    proof, diff = root.deriv_proof()
    # print(proof[:-1])
    # print("ring")
    # print(diff)
    
    return proof + \
        ("field_simp\n" if root.has_nontrivial_div() else "") + \
            "ring\n" + diff

node = parse(function)
print(node.derivative())