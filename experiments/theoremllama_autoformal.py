from transformers import AutoTokenizer, AutoModelForCausalLM
import torch
from exp import ProblemSolver
from typing import List

#use prompt example from huggingface? Or get few shot examples to use in the prompts

class TL_Autoformalizer(ProblemSolver):
    def __init__(self, name: str = "", shots: int = 4, examples: List = []):
        super().__init__(name,shots,examples)
        self.model = AutoModelForCausalLM.from_pretrained("RickyDeSkywalker/TheoremLlama")
        self.model = self.model.to(torch.device("cuda"))
        self.tokenizer = AutoTokenizer.from_pretrained("RickyDeSkywalker/TheoremLlama")
        self.terminators = [self.tokenizer.eos_token_id, 
               self.tokenizer.convert_tokens_to_ids("<|eot_id|>"), 
               self.tokenizer.convert_tokens_to_ids("<|reserved_special_token_26|>")]

    def solve(self, prompt):
        try:
            tokenized_prompt = self.tokenizer(prompt, return_tensors="pt")
            results = self.model.generate(tokenized_prompt["input_ids"].to(torch.device("cuda")), 
                            max_new_tokens=1024,
                            eos_token_id=self.terminators,
                            do_sample=True,
                            temperature=0.85,
                            top_p=0.9)
            result_str = self.tokenizer.decode(results[0])
            return result_str[len(prompt):], True
        except Exception as e:
            return e, False

        