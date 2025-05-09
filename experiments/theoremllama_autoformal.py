from transformers import AutoTokenizer, AutoModelForCausalLM
import torch

#use prompt example from huggingface? Or get few shot examples to use in the prompts

class TL_Autoformalizer():
    def __init__(self):
        self.model = AutoModelForCausalLM.from_pretrained("RickyDeSkywalker/TheoremLlama")
        self.model = self.model.to(torch.device("cuda"))
        self.tokenizer = AutoTokenizer.from_pretrained("RickyDeSkywalker/TheoremLlama")
        self.terminators = [self.tokenizer.eos_token_id, 
               self.tokenizer.convert_tokens_to_ids("<|eot_id|>"), 
               self.tokenizer.convert_tokens_to_ids("<|reserved_special_token_26|>")]

    def formalize(self, prompt):
        tokenized_prompt = self.tokenizer(prompt)
        results = self.model.generate(tokenized_prompt["input_ids"].to(torch.device("cuda")), 
                         max_new_tokens=1024,
                         eos_token_id=self.terminators,
                         do_sample=True,
                         temperature=0.85,
                         top_p=0.9)
        result_str = self.tokenizer.decode(results[0])
        print(result_str[len(prompt):])
