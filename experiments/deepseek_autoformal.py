import re
import torch
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams
from exp import ProblemSolver
from typing import List

class DS_Autoformalizer(ProblemSolver):
    def __init__(self, name: str = "", shots: int = 4, examples: List = []):
        super().__init__(name,shots,examples)
        model_name = "deepseek-ai/DeepSeek-Prover-V1.5-RL"
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = LLM(model=model_name, max_num_batched_tokens=8192, seed=1, trust_remote_code=True)
        sampling_params = SamplingParams(
            temperature=1.0,
            max_tokens=2048,
            top_p=0.95,
            n=1,
        )
        self.sampling_params = sampling_params

    def format_prompt(self, informal_statement_with_answers):
        #from deepseek paper
        return f"""Mathematical Problem in Natural Language:
{informal_statement_with_answers}
Translate the problem to Lean 4 (only the core declaration):
"'lean4
"""
    
    def extract(self, text):
        response = re.sub(r"\s*['\"]\s*$", "", text)
        return response

    def solve(self, prompt):
        try:
            model_outputs = self.model.generate(
                [prompt],
                self.sampling_params,
                use_tqdm=False,
            )

            generated_text = model_outputs[0].outputs[0].text
            statement = self.extract(generated_text)
            return statement, True
        except Exception as e:
            return e, False



# response is in the format: {$formal_statement}
# “‘