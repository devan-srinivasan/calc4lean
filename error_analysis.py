import os, json, re

model = 'deepseek'
nl = True
compare_theorems = False

compiled_directory = f"lean/LeanCalc/{'results_copy' if compare_theorems else 'results'}/{'nl' if nl else 'fl'}/{model}"
model_output_directory = f"{'results_copy' if compare_theorems else 'results'}/{'nl' if nl else 'fl'}/{model}"

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
    'differentiation': {
        'success': 0,
        'overproved': 0,
        'incomplete': 0,
        'tactic_failed': 0,
        'tactic_dne': 0,
        'corrupted': 0,
        'earliest_err_lns': [],
        'ill_formed': 0
    },
    'monotonicity': {
        'success': 0,
        'overproved': 0,
        'incomplete': 0,
        'tactic_failed': 0,
        'tactic_dne': 0,
        'corrupted': 0,
        'earliest_err_lns': [],
        'ill_formed': 0
    },
    'inequality': {
        'success': 0,
        'overproved': 0,
        'incomplete': 0,
        'tactic_failed': 0,
        'tactic_dne': 0,
        'corrupted': 0,
        'earliest_err_lns': [],
        'ill_formed': 0
    },
    'tangents': {
        'success': 0,
        'overproved': 0,
        'incomplete': 0,
        'tactic_failed': 0,
        'tactic_dne': 0,
        'corrupted': 0,
        'earliest_err_lns': [],
        'ill_formed': 0
    },
    'extrema': {
        'success': 0,
        'overproved': 0,
        'incomplete': 0,
        'tactic_failed': 0,
        'tactic_dne': 0,
        'corrupted': 0,
        'earliest_err_lns': [],
        'ill_formed': 0
    },
}

for filename in os.listdir(model_output_directory):
    # load the problems and parse the json
    if not filename.endswith('json'): 
        continue

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
    if compare_theorems: assert(len(fs) == len(problems))

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

    # compute metrics -- this is an approximation as LLMs are horrible theorem provers
    def find_key(ln: int):
        for k in mapping.keys():
            a, b = tuple(map(int, k.split('_')))
            if a <= ln <= b:
                return k
        return -1
    
    with open(f"{compiled_directory}/{filename.split('.')[0]}.json", 'r') as f:
        messages = json.load(f)['messages']
    
    corrupted = []
    for msg in messages:
        if msg['severity'] == 'error' or msg['severity'] == 'warning' and 'sorry' in msg['data']:
            ln = msg['pos']['line']
            K = find_key(ln)
            if K == -1:
                continue
            mapping[K].append(msg)
            if "unexpected token 'example'" in msg['data']:
                corrupted.append(K)
                
    for k in mapping:
        if k in corrupted: continue
        if mapping[k]:
            if len(mapping[k]) == 1:
                if 'unsolved goals' in mapping[k][0]['data']:
                    # incomplete, but syntax is correct or no proof provided
                    mets[ptype]['incomplete'] += 1
                elif 'no goals' in mapping[k][0]['data']:
                    # overproved
                    mets[ptype]['overproved'] += 1
            else:
                if any({'failed' in m['data'] for m in mapping[k]}) or \
                    any({'ambiguous' in m['data'] for m in mapping[k]}) or \
                        any({'made no progress' in m['data'] for m in mapping[k]}):
                    mets[ptype]['tactic_failed'] += 1

                if any({'unknown' in m['data'] for m in mapping[k]}):
                    mets[ptype]['tactic_dne'] += 1
            earliest_ln = min(list(map(lambda m: m['pos']['line'], mapping[k]))) - int(k.split('_')[0])
            mets[ptype]['earliest_err_lns'].append(earliest_ln)
            
        else:
            mets[ptype]['success'] += 1
    mets[ptype]['corrupted'] = len(corrupted)
    mets[ptype]['ill_formed'] = len(problems) - len(mapping)


with open(f"analysis_results/{model}_{'nl' if nl else 'fl'}_{compare_theorems}.json", 'w') as f:
    json.dump(mets, f, indent=4)