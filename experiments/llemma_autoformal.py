from transformers import AutoTokenizer, AutoModelForCausalLM

# their paper says they use prompts in the format of draft sketch, and prove to formalize
# draft, sketch, and prove uses few-shot prompting for their autoformlaizer
# TODO: get examples for prompts

class Llemma_Autoformalizer():
    def __init__(self):
        model_name = "EleutherAI/llemma_7b"
        self.tokenizer = AutoTokenizer.from_pretrained("EleutherAI/llemma_7b")
        self.model = AutoModelForCausalLM.from_pretrained("EleutherAI/llemma_7b")

    def formalize(self, prompt):
        inputs = self.tokenizer(prompt, return_tensors='pt').to('cuda')
        out = self.model(**inputs)
