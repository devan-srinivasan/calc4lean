import os, json, re

model = 'o4-mini'
nl = False
compare_theorems = False

compiled_directory = f"lean/LeanCalc/results_copy/{'nl' if nl else 'fl'}/{model}"
model_output_directory = f"results_copy/{'nl' if nl else 'fl'}/{model}"

regex_checks = {
    'differentiation': r"(\(λ x ↦ .*\)).*=.*:=\s*by", # r"(\(λ x ↦ .*\)).*=\s*(.*?)\s*:=\s*by",
    'monotonicity': r"MonotoneOn (\(λ x.*\)) (\(Icc.*\)) := by",
    'extrema': r"(\(.*\) → \(deriv f .*\) := by)",
    'inequality': r"(example.*:=\s+by)",
    'tangents': r"example \(x y c: ℝ\).*(.*):= by"

}

def parse_functions(file: str, ptype: str):
    with open(file, 'r') as f:
        lines = f.readlines()
    fs = []
    pairs = []
    i = 0
    while i < len(lines):
        if 'example' not in lines[i]: 
            i += 1
            continue
        j = i + 1
        while j < len(lines) and 'example' not in lines[j]:
            j += 1
        block = '\n'.join(lines[i:j])
        match = re.search(regex_checks[ptype], block)
        f = match.groups()[0] if match else ''
        fs.append(f)
        pairs.append((i, j - 1))
        i = j
    return fs, pairs

mets = {

}

for filename in os.listdir(model_output_directory):
    # load the problems and parse the json

    if not filename.endswith('json') or not 'tangent' in filename: continue
    if 'differentiation' in filename:
        ptype = 'differentiation'
    elif 'monot' in filename:
        ptype = 'monotonicity'
    elif 'ineq' in filename:
        ptype = 'inequality'
    elif 'tangent' in filename:
        ptype = 'tangents'
    elif 'extrema' in filename:
        ptype = 'extrema'

    with open(f"{model_output_directory}/{filename.split('.')[0]}.json", 'r') as f:
        problems = json.load(f)
    for item in problems:
        if 'result' in item and isinstance(item['result'], str):
            item['result'] = json.loads(item['result'])

    # load the model generated proofs
    fs, ln_pairs = parse_functions(f"{compiled_directory}/{filename.split('.')[0]}.lean", ptype)
    assert(len(fs) == len(problems))

    # filter the proofs to only those that actually matched the theorem (this is heuristic)
    key = lambda a, b: f"{a}_{b}"
    mapping = {}
    for (a, b), f, problem_dict in zip(ln_pairs, fs, problems):
        if compare_theorems:
            f = f.replace('\n', '')
            true_f = re.search(regex_checks[ptype], problem_dict['result']['problem']).groups()[0]
            if f == true_f: # if time we can change this to some kind of intelligent mapping
                mapping[key(a,b)] = []
        else:
            mapping[key(a,b)] = []

    if len(mapping) < int(0.7) * len(problems):
        raise

    # compute metrics
    with open(f"{compiled_directory}/{filename.split('.')[0]}.json", 'r') as f:
        messages = json.load(f)['messages']
    for msg in messages:
        if msg['severity'] == 'error':
            ln = msg['pos']['line']
        for k in mapping.keys():
            a, b = tuple(map(int, k.split('_')))
            if a <= ln <= b:
                mapping[k].append(msg)
    print()