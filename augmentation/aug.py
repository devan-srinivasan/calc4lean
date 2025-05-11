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
   
class Const(Node):
    def __init__(self, value: int,  parsed: bool = False):
        self.value = value
        
        self.children = []
        self.parsed = parsed

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_const]\n", stack
    
    def differentiability(self):
        return "differentiableAt_const _"

class Expr(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed

    def deriv_proof(self, stack):
        proof, stack = self.children[0].deriv_proof(stack)
        return proof, stack

class ID(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed

    def deriv_proof(self, stack):
        return "nth_rewrite 1 [deriv_id'']\n", stack
    
    def differentiability(self):
        return "differentiableAt_id"

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

class Div(Node):
    def __init__(self, children: list[Node],  parsed: bool = False):
        
        self.children = children
        self.parsed = parsed
        self.differentiability_proof = []

    def deriv_proof(self, stack):
        self.differentiability_proof = [
            self.children[0].differentiability(),
            self.children[1].differentiability(),
            f'ne_of_gt (h_ne_zero)'
        ]
        stack.append(self.differentiability_proof)
        lhs_addition, stack = self.children[0].deriv_proof(stack)
        rhs_addition, stack = self.children[1].deriv_proof(stack)
        proof = "nth_rewrite 1 [deriv_div]\n" + lhs_addition + rhs_addition
        return proof, stack

    def differentiability(self):
        return f"DifferentiableAt.div ({self.children[0].differentiability()}) ({self.children[1].differentiability()}) (h_ne_zero)"
        
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
        # return ""

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
    'sin': Sin,
    'cos': Cos,
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

function = 'cos x / (x^4 + 1)'
tokens = tokenize(function)
tokens = parse_numbers_and_ID(tokens)

root = Node(children=tokens)
root.parse()

proof, diff = root.deriv_proof()
print(proof[:-1])
print("sorry")
print(diff)