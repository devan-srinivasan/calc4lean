from func import *
# import re

def parse_numbers_and_ID(tokens):
    for i in range(len(tokens)):
        if isinstance(tokens[i], str) and tokens[i].isnumeric():
            tokens[i] = Const(value=tokens[i])
        elif isinstance(tokens[i], str) and tokens[i] == 'x':
            tokens[i] = ID(children=[])
    return tokens

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

# f = 'Real.tan ((5:ℝ) * x)'
# node = parse(f).children[0]
# print(f"example (x: ℝ) {node.hypotheses_str()} : deriv (λ x ↦ {node.clean(str(node))}) x = {node.clean(node.derivative())} := by")

# print(node.derivative())
# print(node.clean(str(node)))
# print(node.clean(node.derivative()))
# print(node.clean(node.derivative()))

# print(get_deriv_proof(f))