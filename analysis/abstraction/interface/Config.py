from prop_lang.util import neg
from prop_lang.variable import Variable

env = Variable("env_turn")
con = neg(env)
