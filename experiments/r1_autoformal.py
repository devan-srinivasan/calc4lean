from __future__ import annotations

import os
import re
from typing import List, Tuple, Optional

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
        temperature: float = 0.2,
        top_p: float = 0.95
    ): 
        super().__init__(name=name, shots=shots, examples=[])

        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=KEY,
        )

        self.temperature = temperature
        self.top_p = top_p


    def solve(self, prompt: str) -> Tuple[str, bool]:
        try:
            resp = self.client.chat.completions.create(
                model="deepseek/deepseek-r1:free",
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                top_p=self.top_p,
            )
            out: str = resp.choices[0].message.content.strip()
            proof = extract_lean_code(out)
            if not proof:
                return out, False

            print(resp)
            return proof, True

        except Exception as e:
            return f"DeepSeek API error: {e}", False
