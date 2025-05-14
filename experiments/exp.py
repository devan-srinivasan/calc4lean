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

class Problem:
    def __init__(self, problem: str, proof: List[str], name: str = ""):
        self.name = name
        self.problem = problem
        self.proof = proof

def parse_lean_file(file_path: str) -> Tuple[str, List[Problem]]:
    """
    Parses a Lean file into two parts: imports/preamble and a list of problems.

    Args:
        file_path (str): Path to the Lean file to parse.

    Returns:
        Tuple[str, List[Dict[str, Optional[str]]]]: A tuple where:
            - The first element is a string containing all the imports and preamble.
            - The second element is a list of problems, where each problem is a dictionary with keys:
                - "original": The original problem string.
                - "tweaked": The tweaked problem string (if any, otherwise None).
                - "problem": The example statement.
                - "proof": The proof body.
    """
    with open(file_path, "r") as file:
        lines = file.readlines()

    header = []
    problems = []

    i = 0
    while 'example' not in lines[i].lower():
        header.append(lines[i])
        i += 1

    while i < len(lines):
        while i < len(lines) and 'example' in lines[i].lower():
            problem = Problem(lines[i], [], name=f"ln{i}")

            i += 1
            while i < len(lines) and 'example' not in lines[i].lower():
                if len(lines[i].strip()) > 0: problem.proof.append(lines[i])
                i += 1
            problems.append(problem)

    return header, problems

def create_lean_file(file_path: str, imports: str, problem: Problem, include_proof=True) -> None:
    """
    Creates a Lean file with the given imports and problems.

    Args:
        file_path (str): Path where the Lean file will be created.
        imports (str): String containing the imports and preamble.
        problems (List[Dict[str, Optional[str]]]): List of problems, where each problem is a dictionary with keys:
            - "problem": The example statement.
            - "proof": The proof body.
    """
    with open(file_path, "w") as lean_file:
        lean_file.writelines(imports)
        # lean_file.write(f"-- Original Problem: {problem.original}")
        # if problem.tweaked:
        #     lean_file.write(f"-- Tweaked Problem: {problem.tweaked}")
        lean_file.write(problem.problem)
        if include_proof: lean_file.writelines(problem.proof)

# TODO given a dataset, and some theorem prover, run the experiment

def run_exp_nohint(problem_file: str, solver: ProblemSolver):
    assert problem_file[-5:] == '.lean'
    imports, problems = parse_lean_file(problem_file)
    
    # Ensure the results directory exists
    os.makedirs(f"results/{solver.name}", exist_ok=True)
    
    # Define the output file
    filename = re.search(r'([^/]+)\.[^/.]+$', problem_file)
    filename = filename.group(1)
    #print(filename)
    outfile = f"results/{solver.name}/{filename}.json"
    solved: Set[str] = set()  # Set to keep track of already solved problems

    # Load existing results if the outfile already exists
    if os.path.exists(outfile):
        with open(outfile, 'r') as f:
            try:
                existing_results = json.load(f)
                # Extract solved problem names
                solved = {result["name"] for result in existing_results}
            except json.JSONDecodeError:
                print("Error reading existing problems, may repeat some problems")
                existing_results = []
    else:
        existing_results = []

    # Go through each problem and solve if not already solved
    pbar = tqdm.tqdm(initial=len(solved), total=len(problems), unit='problem')
    for problem in problems:
        print(problem.name)
        if problem.name not in solved:
            result = solver.solve_nohint(imports, problem)  # Solve the problem
            result_entry = {
                "name": problem.name,
                "result": result.json()  # Assuming result is a dict and JSON-serializable
            }
            if result.proof:
                existing_results.append(result_entry)
            
            # Write intermediate results to the JSON file
            with open(outfile, 'w') as f:
                json.dump(existing_results, f, indent=4)
            pbar.update(1)
    pbar.close()

    print(f"Experiment completed. Results saved to {outfile}")

class ProblemSolver:
    def __init__(self, name: str = ""):
        self.name = name

    #TODO
    def get_prompt(self, prompt_type: str):
        dir = "prompts/" + prompt_type + "_prompts.json"
        with open('your_file.json', 'r') as file:
            data = json.load(file)
        return data[self.name]

    def solve_nohint(self, imports: List[str], problem: Problem):
        raise NotImplementedError

    def solve_hint(self):
        raise NotImplementedError
    
    def solve_augmented(self):
        raise NotImplementedError