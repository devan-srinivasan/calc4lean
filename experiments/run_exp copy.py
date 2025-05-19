from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from openai_autoformal import OpenAIReasoningProblemSolver
from r1_autoformal import DeepSeekR1ProblemSolver
from exp import run_exp_nohint, run_exp_hint
import sys

import logging
logger = logging.getLogger(__name__)
filename = "differentiation"
logging.basicConfig(filename=f'run_exp_r1_rev_{filename}_nl.log', level=logging.INFO)

solver = DeepSeekR1ProblemSolver("r1")
logger.info(f"Logging for solver {solver.__class__}")
run_exp_hint(problem_file=f"lean/LeanCalc/generated_data/{filename}.lean",solver=solver, force_new_results=True)