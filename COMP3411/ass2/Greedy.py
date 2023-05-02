"""
This module implements a simple left wall following code.

The scan method returns the distance to an obstruction along the 8 points of the compass.
To use this as a kind of sonar, the list of readings from the scan are rotated to be relative
to the robot's heading.

The wall follower is implemented as a simple set of conditions. If the robot is not near a wall,
it first turns left and goes for the wall. After that, it keeps hugging the wall. We assume that
the goal is in the path of the robot.

Author: Claude Sammut
"""

from agent import *

FORWARD, FORWARD_RIGHT, RIGHT, BACK_RIGHT, BACK, BACK_LEFT, LEFT, FORWARD_LEFT = range(8)

dirn = [1, 0, 0, 0, 3, 0, 2, 0]

class Greedy(Agent):

    def reset(self):
        Agent.reset(self)
        self.heading = 0
        self.following_wall = False
        self.blocked = self.gw.scan(self.state)
        print(f'{self.state}: {self.blocked}', end= '        ')
        self.sonar = self.blocked[self.heading:] + self.blocked[:self.heading]
        print(f'{self.heading}: {self.sonar}')

    def turn_left(self):
        self.heading = self.gw.left(self.heading)

    def turn_right(self):
        self.heading = self.gw.right(self.heading)

    def do_step(self, S, act, logfile=None):
        Agent.do_step(self, S, act)

        if not self.following_wall:
            self.heading = self.head_to_goal()
        self.heading = self.left_wall_follow()

        R, Sp = act(dirn[self.heading])
        self.G += R

        self.blocked = self.gw.scan(self.state)
        print(f'{S}: {self.blocked}', end='        ')
        # Rotate the blocked list so that the readings are relative to the robot's heading
        self.sonar = self.blocked[self.heading:] + self.blocked[:self.heading]
        print(f'{self.heading}: {self.sonar}')

    def left_wall_follow(self):
        self.following_wall = True

        if self.sonar[LEFT] > 0 and self.sonar[BACK_LEFT] == 0:
            print("Turn left")
            return (self.heading - 2) % 8       # Turn left
        elif self.sonar[FORWARD] == 0:
            print("Turn right")
            return (self.heading + 2) % 8       # Turn right
        else:
            self.following_wall = False
            return self.heading

    def head_to_goal(self):
        x, y = self.gw.indextopos(self.state)
        goal_x, goal_y = self.gw.indextopos(self.gw.goal_state)

        new_x = x
        new_y = y

        if goal_x > x:
            heading_x = gridworld.E
        elif goal_x < x:
            heading_x = gridworld.W
        else:
            heading_x = -1

        if goal_y > y:
            heading_y = gridworld.S
        elif goal_y < y:
            heading_y = gridworld.N
        else:
            heading_y = -1

        if heading_x != -1 and heading_y != -1:
            return random.choice([heading_x, heading_y])
        elif heading_x != -1:
            return heading_x
        else:
            return heading_y
