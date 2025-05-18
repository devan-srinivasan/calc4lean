from __future__ import annotations

import os
import re
from typing import List, Tuple, Optional
import traceback, json

from openai import OpenAI
from dotenv import load_dotenv
from exp import ProblemSolver
load_dotenv()
KEY = os.getenv("R1_TOKEN")

LEAN_FENCE_RE = re.compile(
    r"```(?:lean4?|Lean)\s*([\s\S]*?)```",   # non‑greedy, DOTALL
    flags=re.IGNORECASE,
)

def extract_lean_code(text: str) -> Optional[str]:
    """
    Return the first ```lean4 fenced block from `text`, or None if absent.
    Leading/trailing blank lines are trimmed.
    """
    match = LEAN_FENCE_RE.search(text)
    return match.group(1).strip() if match else None

class DeepSeekR1ProblemSolver(ProblemSolver):

    def __init__(
        self,
        name: str = "",
        shots: int = 4,
        examples: List = [],
        temperature: float = 0.15,
        top_p: float = 0.95
    ): 
        super().__init__(name=name, shots=shots, examples=[])

        self.client = OpenAI(
            #base_url="https://openrouter.ai/api/v1",
            base_url="https://api.deepseek.com",
            api_key=KEY,
        )

        self.temperature = temperature
        self.top_p = top_p


    def solve(self, prompt: str) -> Tuple[str, bool]:
        try:
            resp = self.client.chat.completions.create(
                #model="deepseek/deepseek-r1:free",
                model="deepseek-reasoner",
                messages=[{"role": "user", "content": prompt}],
                max_tokens=8192,
                temperature=self.temperature,
                top_p=self.top_p,
            )
            print(resp)
            out: str = resp.choices[0].message.content.strip()
            print(out)
            proof = extract_lean_code(out)
            print(proof)
            if not proof:
                proof = extract_lean_code(resp.choices[0].message.reasoning.strip())
                if not proof:
                    return out, False

            return proof, True

        except Exception as e:
            traceback.print_exc()
            return f"DeepSeek API error: {e}", False
