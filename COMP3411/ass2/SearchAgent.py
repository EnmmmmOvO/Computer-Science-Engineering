"""
This agent invokes the A* method to find the optimal route to the goal.
Each call to do_step advances the agent to the next state in the path.
Rest and start_agent are called from the main loop.

Author: Claude Sammut
"""

from agent import *
import astar, agent

class SearchAgent(Agent):

    def reset(self):
        # Find the goal
        self.goal = None
        for i, t in enumerate(self.gw.tiles):
            if t == gridworld.TILE_GOAL:
                self.goal = i

        if not self.goal:
            raise Exception("No goal set - can't start search")

        Agent.reset(self)


    def start_agent(self):
        Agent.start_agent(self)
        self.start = self.state
        self.step = 0

        self.path = astar.find_path(self.gw.immtileneighbours,
                               self.start,
                               self.goal,
                               lambda tile: 1,
                               lambda tile: not self.gw.tileblocked(*self.gw.indextopos(tile)),
                               lambda a, b: astar.manhattan_dist(self.gw.indextopos(a),
                                                                 self.gw.indextopos(b)))
        print(self.path)

    def do_step(self, S, act, logfile=None):
        if not self.path:
            self.step = agent.TIMEOUT + 1
            return

        self.state = self.path[self.step]
        self.step += 1

        self.G += 1
        return 0 if self.state == gridworld.TILE_GOAL else -1, self.state

