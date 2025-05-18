from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from openai_autoformal import OpenAIReasoningProblemSolver
from exp import run_exp_nohint

import logging
logger = logging.getLogger(__name__)
logging.basicConfig(filename='run_exp_monotonicity.log', level=logging.INFO)

solver = OpenAIReasoningProblemSolver("o4-mini")
logger.info(f"Logging for solver {solver.__class__}")
run_exp_nohint(problem_file="lean/LeanCalc/generated_data/monotonicity.lean",solver=solver, force_new_results=True)