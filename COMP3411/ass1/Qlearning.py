"""
Q-Learning agent

Author: Elliot Colp
Modified by: Claude Sammut

This is an implementation of a standard Q-learning algorithm.
The original code mapped "similar" tiles to the same state, e.g. all tiles not touching any wall
mapped to one state, all tiles with a wall on the left mapped to another state, etc.
This was changed to the more common representation of one state corresponding to one tile.

update 17/1/2023: added "list" to As = list(where(Qs == maxQ)[0])
    Previously caused an error in Python 3.11 on mac

"""

from agent import *
import random
import gridworld


class Qlearning(Agent):
    def reset(self):
        Agent.reset(self)
        self.epsilon = 0.1
        self.alpha = 0.1
        self.gamma = 1
    
    def do_step(self, S, act, logfile=None):
        Agent.do_step(self, S, act, logfile)
        
        # Observation -> agent state
        S = self.get_S()
        
        # Epsilon-greedy action selection
        if ranf() <= self.epsilon:
            # Choose a random action (0 or 1)
            A = randint(ACTION_COUNT)
        else:
            # Choose the best action for this state
            # If two actions have the same Q value, pick one at random
            Qs = self.Q[S]
            maxQ = max(Qs)
            As = list(where(Qs == maxQ)[0])
            A = random.choice(As)
        
        # Observe reward and new state
        R, Sp = act(A)
        
        # Update return
        self.G += R
        
        # max_a(Q(S', a))
        nextmax = 0 if Sp == gridworld.TILE_GOAL else max(self.Q[Sp])
        
        # Update Q for this state/action pair
        delta = R + self.gamma * nextmax - self.Q[S][A]
        self.Q[S][A] += self.alpha * delta
        
        if logfile:
            logfile.write("{}\n".format(abs(delta)))
        
        return Sp
        
    def update_alpha(self, event=None):
        if self.testmode: return
        
        self.alpha = self.alpha_var.get()
    
    def update_epsilon(self, event=None):
        if self.testmode: return
        
        self.epsilon = self.epsilon_var.get()
    
    def update_gamma(self, event=None):
        if self.testmode: return
        
        self.gamma = self.gamma_var.get()
        
    def set_testmode(self, enabled):
        if not self.testmode and enabled:
            self.tempAlpha = self.alpha
            self.tempEpsilon = self.epsilon
            self.alpha = 0
            self.epsilon = 0
        
        elif self.testmode and not enabled:
            self.alpha = self.tempAlpha
            self.epsilon = self.tempEpsilon
        
        Agent.set_testmode(self, enabled)

    def init_options(self, master):
        # Alpha
        frame = LabelFrame(master)
        frame["text"] = "Alpha"
        frame["padx"] = 5
        frame["pady"] = 5
        frame.grid(row=0, column=0)
        
        self.alpha_var = DoubleVar()
        self.alpha_var.set(self.alpha)
        scale = Scale(frame)
        scale["from"] = 1
        scale["to"] = 0
        scale["resolution"] = 0.05
        scale["orient"] = VERTICAL
        scale["variable"] = self.alpha_var
        scale["command"] = self.update_alpha
        scale.pack()
        
        # Epsilon
        frame = LabelFrame(master)
        frame["text"] = "Epsilon"
        frame["padx"] = 5
        frame["pady"] = 5
        frame.grid(row=1, column=0)
        
        self.epsilon_var = DoubleVar()
        self.epsilon_var.set(self.epsilon)
        scale = Scale(frame)
        scale["from"] = 1
        scale["to"] = 0
        scale["resolution"] = 0.05
        scale["orient"] = VERTICAL
        scale["variable"] = self.epsilon_var
        scale["command"] = self.update_epsilon
        scale.pack()
        
        # Gamma
        frame = LabelFrame(master)
        frame["text"] = "Gamma"
        frame["padx"] = 5
        frame["pady"] = 5
        frame.grid(row=2, column=0)
        
        self.gamma_var = DoubleVar()
        self.gamma_var.set(self.gamma)
        scale = Scale(frame)
        scale["from"] = 1
        scale["to"] = 0
        scale["resolution"] = 0.05
        scale["orient"] = VERTICAL
        scale["variable"] = self.gamma_var
        scale["command"] = self.update_gamma
        scale.pack()
