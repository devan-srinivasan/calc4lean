from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from exp import run_exp_nohint

solver = TL_Autoformalizer(name="theoremllama")
run_exp_nohint(problem_file="lean/LeanCalc/D_easy.lean",solver=solver)