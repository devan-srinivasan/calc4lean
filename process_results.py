import json, re, os, subprocess

def test_results(directory: str, override_results_file: False):
    subdir = re.match(r"results/(.+)$", directory).group(1)
    out_dir = f"LeanCalc/results/{subdir}"  # we cd into .lean/ when we use repl
    for filename in os.listdir(directory):
        if filename.endswith('json'):
            print(f"processing: {subdir}/{filename}")
            with open(f"{directory}/{filename}", 'r') as f:
                problems = json.load(f)
            for item in problems:
                if 'result' in item and isinstance(item['result'], str):
                    item['result'] = json.loads(item['result'])
            outfile = f"{out_dir}/{filename.split('.')[0]}.lean"
            if not os.path.exists('lean/' + outfile):
                compute_problems(problems, outfile=outfile, use_repl=True)
            else:
                compute_problems(problems, outfile=outfile, use_repl=override_results_file)


def compute_problems(problems, outfile, use_repl=False):

    # ==== process proofs ====
    r = {}
    lines = "import Mathlib\nopen Real Set\n\n"
    sorry_count = 0
    for problem in problems:
        if problem['result']['complete']:
            cleaned_proof = process_proof(problem['result']['proof'])
        else:
            if problem['result']['out']:
                cleaned_proof = process_proof(problem['result']['out'])
            else:
                cleaned_proof = '' # will be logged as failure
        if cleaned_proof and cleaned_proof[-1] != '\n': cleaned_proof += '\n'
        # if not cleaned_proof:
        #     print()
        if 'sorry' in cleaned_proof: sorry_count += 1
        start, end = lines.count('\n') + 1, lines.count('\n') + cleaned_proof.count('\n') + 1
        r[f"{start}_{end}"] = []
        # problem['result']['proof'] = cleaned_proof
        lines += problem['result']['problem'] + cleaned_proof + "\n"

    if use_repl:
        if os.getcwd().endswith("calc4lean"): 
            os.chdir("./lean")
        os.makedirs(os.path.dirname(outfile), exist_ok=True)

        with open(outfile, "w") as lean_file:
            lean_file.write(lines)
        lean_file.close()
        
        # gets proof state back from lean compiler
        result = subprocess.run(
            ["bash", "-c", f"echo '{{\"path\": \"{outfile}\", \"allTactics\": true}}' | lake exe repl"],
            text=True,
            capture_output=True,
            check=True
        )
    
        result_json = json.loads(result.stdout)
        if os.getcwd().split('/')[-1] == "lean":
            os.chdir("../")
        with open('lean/' + outfile.replace(".lean", ".json"), 'w') as json_file:
            json.dump(result_json, json_file, indent=4)
    else:
        with open('lean/' + outfile.replace(".lean", ".json"), 'r') as f:
            result_json = json.load(f)
    
    # ==== compute_metrics ====
            
    for m in result_json['messages']:
        if m['severity'] == 'error':
            ln = m['pos']['line']
            for k in r.keys():
                s, e = tuple(map(int, k.split('_')))
                if s <= ln <= e:
                    r[k].append(m)
                    break

    line_dists = [int(r[k][0]['pos']['line']) - int(k.split('_')[0]) for k in r if r[k]]
    print(f"""
No. Problems: {len(problems)}
{sorry_count} used 'sorry'
Solved: {len(list(filter(lambda k: len(r[k]) == 0, r)))} | Unsolved: {len(problems) - len(list(filter(lambda k: len(r[k]) == 0, r)))}
Proof Length (Lns):
    Max: {max(line_dists)} Min: {min(line_dists)} Avg: {sum(line_dists) / len(line_dists)}
        """)

def process_proof(proof_lines):
    proof = ""
    for ln in proof_lines:
        if ln.endswith('\n'):
            proof += ln
        else:
            proof += ln + '\n'
    
    proof = re.sub(r'^.*\bimport\b.*\n?', '', proof, flags=re.MULTILINE)
    if 'example' in proof and 'by' in proof:
        proof = proof[proof.index('by') + 2:]
        if proof.startswith('\n'):
            proof = proof[1:]
    # proof = proof.strip()
    if proof.startswith("```"):
        proof = proof[3:]
    if proof.endswith("```"):
        proof = proof[:-3]
    if '```' in proof:
        # if proof.index('```') < len(proof) - 10:
        #     print()
        proof = proof[:proof.index('```')]

    return proof

models = ['deepseek', 'o4-mini', 'r1']
for model in models:
    test_results(f"results/fl/{model}", override_results_file=False)
models = ['o4-mini', 'r1']
for model in models:
    test_results(f"results/nl/{model}", override_results_file=False)

# model = 'r1'
# test_results(f"results/nl/{model}", override_results_file=False)

