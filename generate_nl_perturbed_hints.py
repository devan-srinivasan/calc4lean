import os
import json
from openai import OpenAI
import tqdm

nl_hints = "lean/LeanCalc/generated_data/annotated_data"
nl_hints_summaerized = "lean/LeanCalc/generated_data/summerized_annotated_data"
nl_hints_no_structure = "lean/LeanCalc/generated_data/no_structure_annotated_data"

os.makedirs(nl_hints_summaerized, exist_ok=True)
os.makedirs(nl_hints_no_structure, exist_ok=True)

x_list = [f"{i}) " for i in range(1,10)]
x_list.extend([f"{i}. " for i in range(1,7)])
for i in [2,3,5,6]:
    x_list.extend([f"{i}.{j}) " for j in range(1,6)])

for i in [1,2,3,4]:
    x_list.extend([f"{i}.{j}. " for j in range(1,5)])

for i in [2,3]:
    x_list.extend([f"{i}.3.{j}. " for j in range(1,5)])

def remove_structure(annotation):

    edited_lines = []
    line:str
    for line in annotation.split("\n"):
        line = line.strip()
        for ele in reversed(x_list):
            if line.startswith(ele):
                line = line.removeprefix(ele)
                break
        edited_lines.append(line)

    return " ".join(edited_lines)


client = OpenAI()
def summarize(annotation):

    prompt = f"""
Summarize the following instructions in 100 to 150 words. Provide your summary after Summary: tag. Just provide the summary, don't write anything extra.
Instructions:
{annotation} 
"""
    
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": prompt}],
        temperature=0.0,
        max_completion_tokens=500,
    )

    out: str = response.choices[0].message.content.strip()
    return out.split("Summary:")[-1].strip()


# for file_name in os.listdir(nl_hints):
#     with open(f"{nl_hints}/{file_name}", "r") as f:
#         hints_dict = json.load(f)

#     for entry in hints_dict:
#         entry["annotation"] = remove_structure(entry["annotation"])

#     with open(f"{nl_hints_no_structure}/{file_name}", "w") as f:
#         json.dump(hints_dict, f, indent=4)


file_number = 4
for i, file_name in enumerate(os.listdir(nl_hints)):
    if i != file_number:
        continue
    with open(f"{nl_hints}/{file_name}", "r") as f:
        hints_dict = json.load(f)

    for entry in tqdm.tqdm(hints_dict):
        entry["annotation"] = summarize(entry["annotation"])

    with open(f"{nl_hints_summaerized}/{file_name}", "w") as f:
        json.dump(hints_dict, f, indent=4)
