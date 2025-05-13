import tqdm, json

def validate_proof(imports: str, problem: str, proof_lines: str) -> bool:
    import subprocess, json, os, time
    # TODO rewrite
    os.makedirs("tmp", exist_ok=True)
    file_path = f"tmp/{time.time()}.lean"
    # creates the temp lean file and writes to it
    with open(file_path, "w") as lean_file:
        lean_file.write(imports)
        lean_file.write(problem)
        lean_file.write(proof_lines)
    lean_file.close()
    # gets proof state back from lean compiler
    result = subprocess.run(
        ["bash", "-c", f"echo '{{\"path\": \"{file_path}\", \"allTactics\": true}}' | lake exe repl"],
        text=True,
        capture_output=True,
        check=True
    )
    # Delete Temp Lean file
    os.remove(file_path)
    # load to dict
    result_json = json.loads(result.stdout)
    print(result_json)
    # see if any messages are error message
    # return any({msg['severity'] == 'error' for msg in result_json['messages']})

# TODO given a dataset, and some theorem prover, run the experiment

def run_exp_nohint():
    return

class ProblemSolver:
    def __init__(self, name: str = ""):
        self.name = name

    #TODO
    def get_prompt(self, type):
        raise NotImplementedError

    def solve_nohint(self):
        raise NotImplementedError

    def solve_hint(self):
        raise NotImplementedError
    
    def solve_augmented(self):
        raise NotImplementedError