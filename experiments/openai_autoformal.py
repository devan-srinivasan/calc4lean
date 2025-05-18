from __future__ import annotations

import re
from typing import List, Tuple, Optional

from openai import OpenAI
from langchain.prompts import PromptTemplate
from exp import ProblemSolver

import logging
logger = logging.getLogger(__name__)

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
    return match.groups()[-1].strip() if match else None

class OpenAIReasoningProblemSolver(ProblemSolver):

    def __init__(
        self,
        name: str = "o4-mini",
        shots: int = 4,
        examples: List = [],
        temperature: float = 1.0,
        max_tokens: int = 5120,
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
                model=self.name,
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                max_completion_tokens=self.max_tokens,
                top_p=self.top_p,
                **self.chat_kwargs,
            )

            out: str = response.choices[0].message.content.strip()
            logger.info(f"Prompt: {prompt}")
            logger.info(f"Response: {out}")
            proof = extract_lean_code(out)
            if not proof:
                return out, False

            return proof, True

        # Catch *every* client‑side failure and propagate it upstream
        except Exception as e:
            return f"OpenAI API error: {e}", False
