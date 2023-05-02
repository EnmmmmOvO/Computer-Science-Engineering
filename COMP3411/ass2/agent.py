from pylab import *
from tkinter import *
import random
import gridworld

ACTION_COUNT = 4
TIMEOUT = 5000


class Agent:
    def __init__(self, gw):
        """
        Initialize the agent.
        """
        self.gw = gw
        self.state_count = self.gw.get_state_count()
        self.state = 0

        self.heading = -1   # -1 if no heading; otherwise, N, S, E, W
        self.reset()

    def reset(self):
        """
        Resets all agent data.
        """
        self.state_count = self.gw.get_state_count()
        self.testmode = False
        self.run = 0            # Number of episodes
        self.episode = 0        # Count an episode completes after reaching the goal
        self.step = 0           # How many steps within an episode
        self.returnSum = 0
        self.G = 0
        self.init_Q()
        self.start_agent()

    def start_agent(self):
        if self.gw.agentstart == gridworld.AGENTSTART_RAND:
            self.state = random.choice(self.gw.validtiles())
        else:
            self.state = self.gw.agentstart

    def init_Q(self):
        """
        Initialize Q values.
        """
        self.Q = zeros((self.state_count, ACTION_COUNT), dtype=float)
        
    def get_Qs(self, S):
        """
        Returns Q values for the given state.
        """
        return self.Q[S]
        
    def get_S(self):
        """
        Returns the agent state.
        """
        return self.state

    def get_state(self):
        """
        Gets the current state.
        """
        return self.state

    def set_testmode(self, enabled):
        """
        Turn test mode on or off. When in test mode, the agent should:
        - Disable learning
        - Behave deterministically
        """
        self.testmode = enabled
        
    def init_run(self):
        """
        Resets all run data and starts a new run.
        Override this to reset data!
        """
        self.returnSum = 0
        self.run += 1
        self.episode = -1
        self.init_Q()
        self.init_episode()
    
    def init_episode(self):
        """
        Initializes an episode.
        """
        self.returnSum += self.G
        self.G = 0
        self.step = 0
        self.episode += 1

    def do_step(self, S, act, logfile=None):
        """
        Make the agent take a single step. The agent is given its current state
        and a function to call which takes an action and returns a pair of
        (reward, state).
        Possible actions are:
            0 = go right
            1 = go up
            2 = go left
            3 = go down
            
        This function should return the new state.
        Override this!
        """
        self.step += 1
        return S

    def sample(self, action):
        """
        Takes an action and returns (reward, state)
        Possible actions are:
            0 = go right
            1 = go up
            2 = go left
            3 = go down
        """
        x, y = self.gw.indextopos(self.state)
        x += int(action == 0) - (action == 2)
        y += int(action == 3) - (action == 1)
        newindex = self.gw.postoindex(x, y)

        if not (x < 0 or y < 0 or x > self.gw.w - 1 or y > self.gw.h - 1
                or self.gw.tiles[newindex] == gridworld.TILE_WALL):
            self.state = newindex

        return 0 if self.state == gridworld.TILE_GOAL else -1, self.state

    def init_options(self, master):
        """
        Override this to add options to the agent options panel.
        """
        pass
        
    def init_info(self, master):
        """
        Override this to add options to the agent info panel.
        """
        # Step
        label = Label(master)
        label["text"] = "Step:"
        label.grid(row=0, column=0)
        
        self.step_var = StringVar()
        label = Label(master)
        label["textvariable"] = self.step_var
        label["width"] = 8
        label.grid(row=0, column=1)
        
        # Episode
        label = Label(master)
        label["text"] = "Episode:"
        label.grid(row=1, column=0)
        
        self.episode_var = StringVar()
        label = Label(master)
        label["textvariable"] = self.episode_var
        label["width"] = 8
        label.grid(row=1, column=1)
        
        # Average return
        label = Label(master)
        label["text"] = "Avg return:"
        label.grid(row=2, column=0)
        
        self.avg_return_var = StringVar()
        label = Label(master)
        label["textvariable"] = self.avg_return_var
        label["width"] = 8
        label.grid(row=2, column=1)
        
    def update_info(self):
        """
        Override this to update the agent info panel.
        """
        self.step_var.set(str(self.step))
        self.episode_var.set(str(self.episode))
        
        if self.episode > 0:
            avgret = self.returnSum / self.episode
            self.avg_return_var.set("{:.3f}".format(avgret))
        else:
            self.avg_return_var.set("NaN")

    def draw_agent(self, canvas, tileW, tileH):
        x, y = self.gw.indextopos(self.state)
        x *= tileW
        y *= tileH

        canvas.create_oval(x + 3,
                            y + 3,
                            x + tileW - 2,
                            y + tileH - 2,
                            fill="red")
        if self.heading == gridworld.N:
            canvas.create_line(x + tileW * 0.5,
                                y + tileH - 6,
                                x + tileW * 0.5,
                                y + 6,
                                arrow=LAST,
                                arrowshape=(12, 16, 6))
        if self.heading == gridworld.S:
            canvas.create_line(x + tileW * 0.5,
                                y + tileH - 6,
                                x + tileW * 0.5,
                                y + 6,
                                arrow=FIRST,
                                arrowshape=(12, 16, 6))