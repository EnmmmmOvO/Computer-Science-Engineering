"""
This agent invokes the DFS method to find a route to the goal.
Each call to do_step advances the agent to the next state in the path.
Rest and start_agent are called from the main loop.

Author: Armin Chitizadeh, Claude Sammut
"""

from agent import *
import dfs, agent

class DFSAgent(Agent):

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

        self.path = dfs.find_path(self.gw.immtileneighbours,
                                  self.start,
                                  self.goal,
                                  [],
                                  lambda tile: not self.gw.tileblocked(*self.gw.indextopos(tile)))
        print(self.path)

    def do_step(self, S, act, logfile=None):
        if not self.path:
            self.step = agent.TIMEOUT + 1
            return

        self.state = self.path[self.step]
        self.step += 1

        self.G += 1
        return 0 if self.state == gridworld.TILE_GOAL else -1, self.state


class IdDfsAgent(Agent):
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

        self.path = []
        """
        <TODO>
        
        self.path = 
        
        """
        print(self.path)


    def do_step(self, S, act, logfile=None):
        if not self.path:
            self.step = agent.TIMEOUT + 1
            return

        self.state = self.path[self.step]
        self.step += 1

        self.G += 1
        return 0 if self.state == gridworld.TILE_GOAL else -1, self.state



