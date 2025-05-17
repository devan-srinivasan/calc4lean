from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from openai_autoformal import O3ProblemSolver
from exp import run_exp_nohint

import logging
logger = logging.getLogger(__name__)
logging.basicConfig(filename='run_exp.log', level=logging.INFO)

solver = O3ProblemSolver("o3")
logger.info(f"Logging for solver {solver.__class__}")
run_exp_nohint(problem_file="lean/LeanCalc/generated_data/inequality.lean",solver=solver, force_new_results=True)