from transformers import AutoTokenizer, AutoModelForCausalLM

# Load the model and tokenizer
model = AutoModelForCausalLM.from_pretrained("RickyDeSkywalker/TheoremLlama")
model = model
tokenizer = AutoTokenizer.from_pretrained("RickyDeSkywalker/TheoremLlama")

# Define the terminators
terminators = [
    tokenizer.eos_token_id,
    tokenizer.convert_tokens_to_ids("<|eot_id|>"),
    tokenizer.convert_tokens_to_ids("<|reserved_special_token_26|>")
]

# Read the prompt from prompts.json
prompt = """
<|start_header_id|>system<|end_header_id|>You are a Lean4 expert who can write good Lean4 code based on natural language mathematical theorem and proof<|eot_id|><|start_header_id>user<|end_header_id|>

    Natural language version of theorem and proof:
    mathd_algebra_55
    What fraction is the same as \[
    \frac{2-4+6-8+10-12+14}{3-6+9-12+15-18+21}?
    \] Show that it is \frac{2}{3}.
    
    We have \begin{align*}
    &\frac{2-4+6-8+10-12+14}{3-6+9-12+15-18+21} \\
    & \qquad = \frac{2(1-2+3-4+5-6+7)}{3(1-2+3-4+5-6+7)} \\
    & \qquad = \frac{2}{3}.
    \end{align*}
    
    ### Lean4 version of theorem statement:
    ```lean
    theorem mathd_algebra_55 (q p : ℝ) (h₀ : q = 2 - 4 + 6 - 8 + 10 - 12 + 14)
      (h₁ : p = 3 - 6 + 9 - 12 + 15 - 18 + 21) : q / p = 2 / 3 :=
    ```
    
    ### Lean4 version of theorem and proof:
    ```lean
    theorem mathd_algebra_55 (q p : ℝ) (h₀ : q = 2 - 4 + 6 - 8 + 10 - 12 + 14)
      (h₁ : p = 3 - 6 + 9 - 12 + 15 - 18 + 21) : q / p = 2 / 3 := by
      -- Proof:
      -- We have q = 2(1-2+3-4+5-6+7) and p = 3(1-2+3-4+5-6+7)
      -- Therefore, q / p = 2 / 3.
      aesop_subst [h₀, h₁] -- substitute q and p
      norm_num -- compute the result
    ```<|reserved_special_token_26|>
    
    
    ### Lean4 version of theorem statement:
    ```lean
    theorem mathd_numbertheory_233
      (b :  ZMod (11^2))
      (h₀ : b = 24⁻¹) :
      b = 116 :=
    ```
    
    ### Lean4 version of theorem and proof:
    <|eot_id|><|start_header_id|>assistant<|end_header_id|>
"""

# Define the tokenized_prompt function
def tokenized_prompt(prompt):
    return tokenizer(prompt, return_tensors="pt")
print("generating")
# Generate results
results = model.generate(
    tokenized_prompt(prompt)["input_ids"],
    max_new_tokens=1024,
    eos_token_id=terminators,
    do_sample=True,
    temperature=0.85,
    top_p=0.9
)

# Decode and print the result
result_str = tokenizer.decode(results[0])
print(result_str[len(prompt):])
