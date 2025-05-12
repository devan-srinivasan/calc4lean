import json
import os
import threading
from tqdm import tqdm
from datasets import load_dataset
from openai import OpenAI
import dotenv
from concurrent.futures import ThreadPoolExecutor, as_completed

# ========== CONFIG ==========
n_threads = 10
OUTPUT_FILE = "data/llm_filtered_results.json"
# ============================

# Load environment variables and dataset
dotenv.load_dotenv(dotenv_path='data/.env')
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

ds = load_dataset("AI-MO/NuminaMath-1.5")
def filter_criteria(problem):
    return problem['problem_is_valid'] != 'Incomplete' and problem['problem_type'] == 'Calculus'

calcds = ds.filter(filter_criteria)['train']

# Load existing results if available
lock = threading.Lock()
if os.path.exists(OUTPUT_FILE):
    with open(OUTPUT_FILE, 'r') as f:
        processed_data = json.load(f)
else:
    processed_data = {}

PROMPT = """
You are a helpful assistant, proficient in understanding calculus problems. You will be supplied with latex calculus problems (and their solutions), and are tasked with classifying them. We are interested in the problem if its solution (suppose it is translated to formal language, like Lean4) can be verified by compiling the proof. We are not interested in problems who's solution look like an example that needs to be verified by writing lean code. Respond with an (optional) brief justification followed by one of these classification categories.
EASY: if it is a straightforward derivative computation. literally just differentiate a function.
MEDIUM: a problem that boils down to a computation, but the computation itself is not immediately presented. Word problems are common examples of these.
HARD: the solution requires a proving some property, i.e., not executing a computation. Keep in mind a problem of the form "prove f'(x) = ..." does not count as hard as this is just a computation.
UNINTERESTING: proof of the existence of something, as these cannot be trivially verified with a verification language compiler. This is because they need to be plugged in and checked that they solve the problem, using some general checker which we do not have.

See these examples below:

Interesting
1) Let $f(x)= ...$. Prove that $f'(x) = ...$ -> EASY
2) Given property A of function $f(x)$, prove property B of $f(x)$ -> HARD
3) Given train A travelling at speed $v_A$ and train B travelling  at speed $v_B$ and these initial conditions: ... Determine when they meet -> MEDIUM

Uninteresting
1) Prove that there exists a function that satisfies the following conditions: ... -> UNINTERESTING
"""

# LLM call
def get_llm_response(row):
    response = client.chat.completions.create(
        model="gpt-4o-mini",  # or your preferred model
        messages=[
            {"role": "system", "content": PROMPT},
            {"role": "user", "content": f"Classify this problem: \n Statement: {row['problem']} \nSolution: {row['solution']}"}
        ]
    )
    return response.choices[0].message.content.strip(), (0.3 * response.usage.prompt_tokens + 1.2 * response.usage.completion_tokens) / (10**6)

# Process a single row
def process_row(i, row):
    uid = str(i)
    if uid in processed_data:
        return None  # Skip already processed

    try:
        response_text, cost = get_llm_response(row)
        with lock:
            processed_data[uid] = {
                "original": row,
                "llm_response": response_text,
                "api_cost": cost
            }
            # Save incrementally
            with open(OUTPUT_FILE, 'w') as f:
                json.dump(processed_data, f, indent=2)
        return uid
    except Exception as e:
        print(f"[ERROR] Failed on row {i}: {e}")
        return None

# Main concurrent execution
def main():
    total_processed = 0

    with ThreadPoolExecutor(max_workers=n_threads) as executor:
        futures = {executor.submit(process_row, i, row): i for i, row in enumerate(calcds)}

        with tqdm(total=len(futures), desc="Processing") as pbar:
            for future in as_completed(futures):
                result = future.result()
                if result is not None:
                    total_processed += 1
                    # Update tqdm postfix with current total cost
                    total_cost = sum(entry.get("api_cost", 0) for entry in processed_data.values())
                    pbar.set_postfix_str(f"Cost: ${total_cost:.4f}")
                    pbar.update(1)


def load_problems(in_file='data/llm_filtered_results.json'):
    import json
    with open(in_file, 'r') as f:
        problems = json.load(f)
    
    partitions = {
        'easy': [],
        'medium': [],
        'hard': [],
        'uninteresting': []
    }

    for k in problems.keys():
        llm_resp = problems[k]['llm_response']
        if 'HARD' in llm_resp:
            partitions['hard'].append(problems[k])
        elif 'MEDIUM' in llm_resp:
            partitions['medium'].append(problems[k])
        elif 'EASY' in llm_resp:
            partitions['easy'].append(problems[k])
        elif 'UNINTERESTING' in llm_resp:
            partitions['uninteresting'].append(problems[k])

    for k in partitions.keys():
        print(f"{k}: {len(partitions[k])}")

    for k in partitions.keys():
        with open(f"{k}.json", 'w') as f:
            json.dump(partitions[k], f, indent=4)

# load_problems()
# main()
# with open("data/partitions/hard.json", 'r') as f:
#     problems = json.load(f)

# filtered_set = []
# for p in problems:
#     if any({k.lower() in p['original']['problem'].lower()
#             for k in {
#                 'integrate', 'investigate', 'differential equation', 'Lagrange',
#                 'Rolle', 'integral', 'continuous', 'continuity', 'limit', 'find', 
#                 'flux', 'field', 'mass', 'verify', 'determine', 'divergence', 'convergence', 
#                 'series', '\\int', '\\lim', 'Plot', 'Dirichlet', 'Cauchy', 
#             }}):
#         continue
#     filtered_set.append(p)

# with open("data/partitions/hard_filtered.json", 'w') as f:
#     print(len(filtered_set))
#     json.dump(filtered_set, f, indent=4)
            
# print(len(calcds))

monotonic_maybe = calcds.filter(lambda p: all(k in p['problem'] for k in {'monoton', 'prove', 'on'}))
print(len(monotonic_maybe))

c = 0
for p in monotonic_maybe:
    print(p['problem'])
    print()
    c+=1
    if c == 50: break