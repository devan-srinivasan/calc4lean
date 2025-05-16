from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from exp import run_exp_nohint

solver = Llemma_Autoformalizer(name="llemma")
run_exp_nohint(problem_file="lean/LeanCalc/generated_data/inequality_10.lean",solver=solver)