from func import *
# import re

def parse_numbers_and_ID(tokens):
    for i in range(len(tokens)):
        if isinstance(tokens[i], str):
            if tokens[i].isnumeric() or \
                len(tokens[i]) > 1 and tokens[i][1:].isnumeric() and tokens[i][0] == '-': tokens[i] = Const(value=tokens[i])
            elif tokens[i] == 'x':
                tokens[i] = ID(children=[])
    return tokens

def tokenize(function: str):
    chars = list[Node](function)
    for i, c in enumerate(chars):
        if c == '(' and i+1 < len(chars) and chars[i+1] != ' ':
            chars.insert(i+1, ' ')
        if c == ')' and i-1 > 0 and chars[i-1] != ' ':
            chars.insert(i, ' ')
        if c in {'^', '+', '*', '/'}:
            if i+1 < len(chars) and chars[i+1] != ' ':
                chars.insert(i+1, ' ')
            if i-1 >= 0 and chars[i-1] != ' ':
                chars.insert(i, ' ')
        if c == '-': # this is subtraction NOT negative
            if i+1 < len(chars) and chars[i+1] == ' ':
                if i-1 >= 0 and chars[i-1] != ' ':
                    chars.insert(i, ' ')
    function = ''.join(chars).split()
    return [t for t in function if t.strip()]

def parse(func: str):
    import re
    func = func.replace("Real.", "").replace(":ℝ", "")
    func = re.sub(r'\((\d+)\)', r'\1', func)
    func = re.sub(r'\(\(([^()]+)\)\)', r'(\1)', func)
    tokens = tokenize(func)
    tokens = parse_numbers_and_ID(tokens)

    root = Node(children=tokens)
    root.parse()
    root.assign_ids()   # numbers hypotheses
    return root

def get_deriv_proof(root: Node, separate=False):
    proof, diff = root.deriv_proof(stack=[])
    diff.reverse()
    diff_proof = []
    for s in diff:
        for ln in s:
            if ln: diff_proof.append('exact ' + ln)
    diff_proof = '\n'.join(diff_proof)
    if separate:
        return proof, root.field_simp_str(), "ring\n", diff_proof
    else:
        return proof + \
            root.field_simp_str() + \
                "ring\n" + diff_proof
    

# f = '(((Real.exp (x) * (x ^ 2 + (3:ℝ))) + (Real.exp (x) * ((2:ℝ) * (1:ℝ)))) * ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) - (Real.exp (x) * (x ^ 2 + (3:ℝ))) * ((((3:ℝ) * x ^ 2) * (Real.log (x) / Real.log ((5:ℝ)))) + ((x ^ 3) * ((((1:ℝ) / x) * Real.log ((5:ℝ))) / Real.log ((5:ℝ)) ^ 2)))) / ((x ^ 3) * (Real.log (x) / Real.log ((5:ℝ)))) ^ 2'
# node = parse(f).children[0]
# print(str(node))
# node = node.reduce()
# print(str(node))

# f1 = '(Real.exp x) * (x ^ 2 + (3:ℝ))'
# f2 = '(x ^ 3) * (Real.log x / Real.log (5:ℝ))'
# node1 = parse(f1).children[0]
# node2 = parse(f2).children[0]
# node = Div(children=[node1, node2])

# print(node.derivative())

# d_node = parse(node.derivative()).children[0].reduce()
# # print()
# print(str(d_node))

# node1.derivative_repr = '- Real.sin x * Real.log (cos x) - Real.sin x'
# node2 = parse("2 * x").children[0]

# node = Add(children=[node2, node1])

# print(f"example (x: ℝ) {node.hypotheses_str()} : deriv (λ x ↦ {node.clean(str(node))}) x = {node.clean(node.derivative())} := by")
# print(str(node))
# reduced = node.reduce()
# print(str(reduced))
# print(f"example (x: ℝ) {node.hypotheses_str()} : deriv (λ x ↦ {node.clean(str(node))}) x = {node.clean(node.derivative())} := by")
# print(get_deriv_proof(node)) 