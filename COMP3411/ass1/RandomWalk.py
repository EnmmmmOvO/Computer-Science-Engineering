"""
An agent that makes random moves. Useful as a baseline comparison with other algorithms

Author: Elliot Colp
"""

from agent import *

class RandomWalk(Agent):
    def do_step(self, S, act, logfile=None):
        Agent.do_step(self, S, act)
        
        R, Sp = act(randint(ACTION_COUNT))
        self.G += R
