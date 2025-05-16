from __future__ import annotations

import os
import re
from typing import List, Tuple, Optional

from openai import OpenAI
from dotenv import load_dotenv
from exp import ProblemSolver
load_dotenv()
KEY = os.getenv("R1_TOKEN")


class DeepSeekR1ProblemSolver(ProblemSolver):

    def __init__(
        self,
        name: str = "",
        shots: int = 4,
        examples: List = [],
        temperature: float = 0.2,
        max_tokens: int = 1024,
        top_p: float = 0.95
    ): 
        super().__init__(name=name, shots=shots, examples=[])

        self.client = OpenAI(
            base_url="https://openrouter.ai/api/v1",
            api_key=KEY,
        )

        self.temperature = temperature
        self.max_tokens = max_tokens
        self.top_p = top_p

        self._terminator_re = re.compile(r"\b(qed|∎|■)\b", re.I)

    def solve(self, prompt: str) -> Tuple[str, bool]:
        try:
            resp = self.client.chat.completions.create(
                model="deepseek/deepseek-r1:free",
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                max_tokens=self.max_tokens,
                top_p=self.top_p,
            )
            out: str = resp.choices[0].message.content.strip()


            lower = out.lower()
            complete = (
                "sorry" not in lower
                and bool(self._terminator_re.search(out))
            )
            return out, complete

        except Exception as e:
            return f"DeepSeek API error: {e}", False
