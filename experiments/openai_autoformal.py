from __future__ import annotations

import re
from typing import List, Tuple

from openai import OpenAI
from langchain.prompts import PromptTemplate
from exp import ProblemSolver

class O3ProblemSolver(ProblemSolver):

    def __init__(
        self,
        name: str = "",
        shots: int = 4,
        examples: List = [],
        temperature: float = 0.0,
        top_p: float = 1.0,
        **chat_kwargs,
    ):
        if examples is None:
            examples = []
        super().__init__(name=name, shots=shots, examples=examples)

        self.temperature = temperature
        self.top_p = top_p
        self.chat_kwargs = chat_kwargs

        self.client = OpenAI()

        self._proof_end_re = re.compile(r"\b(qed|∎|■)\b", re.I)

    def solve(self, prompt: str) -> Tuple[str, bool]:
        try:
            response = self.client.chat.completions.create(
                model="o3",
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                top_p=self.top_p,
                **self.chat_kwargs,
            )

            out: str = response.choices[0].message.content.strip()
            proof = extract_lean_code(out)
            if not proof:
                return out, False

            return proof, True

        # Catch *every* client‑side failure and propagate it upstream
        except Exception as e:
            return f"OpenAI API error: {e}", False
