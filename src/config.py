from prop_lang.util import neg
from prop_lang.variable import Variable

env = Variable("env_turn")
con = neg(env)
init_state = Variable("init_state")

prefer_ranking = True
only_structural = False
only_ranking = False
only_safety = False
eager_fairness = True