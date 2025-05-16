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
            inputs = self.tokenizer(prompt, return_tensors="pt")
            inputs = {k: v.to(self.device) for k, v in inputs.items()}
            prompt_len = inputs["input_ids"].shape[-1]
            out = self.model.generate(
                **inputs,
                max_new_tokens=1024,
                do_sample=False,
                pad_token_id=self.tokenizer.eos_token_id,  
            )
            gen_ids = out[0][prompt_len:]                  # keep only the tail
            gen_text = self.tokenizer.decode(
                gen_ids,
                skip_special_tokens=True,
                clean_up_tokenization_spaces=True,
            )
            return gen_text, True
        except Exception as e:
            print(e)
            return f"{e.__class__.__name__}: {e}", False
    def solve_hint(self, prompt, max_new_tokens: int = 64):
        return
 