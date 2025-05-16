from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
from exp import ProblemSolver
from typing import List

# their paper says they use prompts in the format of draft sketch, and prove to formalize
# draft, sketch, and prove uses few-shot prompting for their autoformlaizer
# TODO: get examples for prompts

class Llemma_Autoformalizer(ProblemSolver):
    def __init__(self, name: str = "", shots: int = 4, examples: List = []):
        super().__init__(name,shots,examples)
        model_name = "EleutherAI/llemma_7b"
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForCausalLM.from_pretrained(model_name)
        self.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
        self.model = self.model.to(self.device)

    def solve(self, prompt):
        try:
            inputs = self.tokenizer(prompt, return_tensors='pt').to(self.device)
            output_ids = self.model.generate(
                **inputs,
                max_new_tokens=max_new_tokens,
                do_sample=False,
                pad_token_id=self.tokenizer.eos_token_id,  
            )
            return self.tokenizer.decode(
                output_ids[0],
                skip_special_tokens=True,
                clean_up_tokenization_spaces=True,
            ), True
        except Exception as e:
            return e, False
    def solve_hint(self, prompt, max_new_tokens: int = 64):
        return
 