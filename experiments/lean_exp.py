import re, json, os
from typing import List, Dict, Optional, Tuple, Set
from .repl_wrapper import read_file
import os, tqdm

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

class ProofState:
    def __init__(self, proofState: dict, imports=list[str], problem: Problem = None):
        self.goals = []
        self.errors = []
        self.hyp = []
        self.proof = proofState['proof'] if 'proof' in proofState else []
        self._json = proofState
        self.start_soln_line = -1
        self.imports = imports
        self.problem = problem

        if 'messages' in proofState:
            msg = None
            for m in proofState['messages']:
                if m['severity'] == 'error': 
                    self.errors.append(m['data'])
                    if not msg and 'unsolved goals' in m['data']:
                        msg = m
            
            # now we do some processing...
            if msg:
                unsolved_err = msg['data'][15:]
                split = unsolved_err.split('⊢')
                for goal in split[1:]:
                    self.goals.append('⊢' + goal)
                for hy in split[0].split('\n')[:-1]:
                    self.hyp.append(hy)

                self.start_soln_line = int(msg['endPos']['line']) + 1
    
    def solved(self) -> bool:
        return not self.goals and not self.errors
    
    def json(self) -> dict:
        if self.proof: self._json['proof'] = self.proof
        return self._json

class ProblemSolver:
    def __init__(self, name: str = ""):
        self.name = name

    def get_proof_suggestion(self, proofState: ProofState) -> list[str]:
        raise NotImplementedError
    
    def solve_problem(self, imports: List[str], problem: Problem) -> list[str]:
        # by default we just get the entire proof
        # override this if you want custom proof solving, using update_proof
        return self.update_proof(imports, problem)

    def update_proof(self, imports: List[str], problem: Problem) -> ProofState:
        # step 1 create the file to solve this in lean
        os.makedirs(f"tmp/{self.name}", exist_ok=True)
        fn = f"tmp/{self.name}/{problem.name}.lean"
        create_lean_file(fn, imports, problem, include_proof=False)

        proofState = ProofState(read_file(fn), imports, problem)

        proof = self.get_proof_suggestion(proofState)
        problem.proof = proof

        create_lean_file(fn, imports, problem, include_proof=True)

        proofState = ProofState(read_file(fn), imports, problem)
        proofState.proof = proof
        
        return proofState
    
def run_exp(problem_file: str, solver: ProblemSolver):
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
            result = solver.solve_problem(imports, problem)  # Solve the problem
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