from __future__ import annotations

import re
from typing import List, Tuple, Optional

import replicate
from langchain.prompts import PromptTemplate
from exp import ProblemSolver
import os

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

class ClaudeReasoningProblemSolver(ProblemSolver):

    def __init__(
        self,
        name: str = "claude-3.5-haiku",
        shots: int = 4,
        examples: List = [],
        temperature: float = 0.0,
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
        self.max_tokens = max_tokens

        self._proof_end_re = re.compile(r"\b(qed|∎|■)\b", re.I)

    def solve(self, prompt: str) -> Tuple[str, bool]:
        try:

            response = replicate.run(
                ref=f"anthropic/{self.name}",
                input={
                    "prompt": prompt,
                    "max_tokens": self.max_tokens
                },
            )

            out: str = "".join(response).strip()
            logger.info(f"Prompt: {prompt}")
            logger.info(f"Response: {out}")
            proof = extract_lean_code(out)
            if not proof:
                return out, False

            return proof, True

        # Catch *every* client‑side failure and propagate it upstream
        except Exception as e:
            return f"Replicate API error: {e}", False
