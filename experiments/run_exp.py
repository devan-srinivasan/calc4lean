from deepseek_autoformal import DS_Autoformalizer
from llemma_autoformal import Llemma_Autoformalizer
from theoremllama_autoformal import TL_Autoformalizer
from r1_autoformal import DeepSeekR1ProblemSolver
from exp import run_exp_nohint

path = 'lean/LeanCalc/generated_data/'
#files = ['inequality.lean','extrema_problems.lean','differentiation_632.lean','monotone_A_100.lean','monotone_B_100.lean','pq_easy.lean','tangents.lean']
files = ['monotone_A_100.lean','monotone_B_100.lean']
solver = DeepSeekR1ProblemSolver(name="r1")
for file in files:
    print(file)
    run_exp_nohint(problem_file=path+file,solver=solver)
