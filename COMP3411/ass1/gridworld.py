import pickle
from collections import namedtuple

DEFAULT_W = 16
DEFAULT_H = 16

TILE_WALL = -1
TILE_GOAL = -2
TILE_BEAM = -3

AGENTSTART_RAND = -1

SavedWorld = namedtuple("SavedWorld", ["agentstart", "w", "h", "tiles"])

N, NE, E, SE, S, SW, W, NW = range(8)

dirn_offset = [
    (0, -1),
    (1, -1),
    (1, 0),
    (1, 1),
    (0, 1),
    (-1, -1),
    (-1, 0),
    (-1, -1)
]


class GridWorld:
    """
    A tile-based world with some agents.
    """
    def __init__(self, w=DEFAULT_W, h=DEFAULT_W):
        self.resize(w, h)
        self.goal_state = -1
        
    def resize(self, w: int, h: int):
        """
        Resize the grid and add new tiles
        """
        self.w = w
        self.h = h
        self.agentstart = -1
        
        # Add tiles
        self.tiles = [0] * w * h
        for t in range(w * h):
            self.updt_tile(t)

    def get_state_count(self):
        """
        Gets the current state.
        """
        return self.w * self.h

    def postoindex(self, x, y):
        """
        Converts a position to a tile index.
        """
        return x + y * self.w
        
    def validpos(self, x, y):
        """
        Returns whether this is a valid position in the grid world.
        """
        if x < 0 or x > self.w - 1 or y < 0 or y > self.h - 1:
            return False
            
        return True
        
    def indextopos(self, index):
        """
        Converts a tile index to a position.
        """
        return (index % self.w,
                index // self.w)
   
    def tileneighbours(self, ind):
        """
        Return a list of all 8 neighbours
        """
        x, y = self.indextopos(ind)
        tiles = [ind]
        
        if x > 0:
            tiles.append(ind - 1)
            if y > 0: tiles.append(ind - self.w - 1)
            if y < self.h - 1: tiles.append(ind + self.w - 1)
        
        if x < self.w - 1:
            tiles.append(ind + 1)
            if y > 0: tiles.append(ind - self.w + 1)
            if y < self.h - 1: tiles.append(ind + self.w + 1)
                
        if y > 0: tiles.append(ind - self.w)
        
        if y < self.h - 1: tiles.append(ind + self.w)
        
        return tiles
        
    def immtileneighbours(self, ind):
        """
        Return a list of just the 4 immediate neighbours
        """
        x, y = self.indextopos(ind)
        tiles = []
        
        if x > 0:
            tiles.append(ind - 1)
        if x < self.w - 1:
            tiles.append(ind + 1)
        if y > 0:
            tiles.append(ind - self.w)
        if y < self.h - 1:
            tiles.append(ind + self.w)
            
        return tiles
            
    def tileblocked(self, x, y):
        """
        Returns True if a tile is either a wall or invalid, else False.
        """
        ind = self.postoindex(x, y)
        
        if x < 0: return True
        if x > self.w - 1: return True
        if y < 0: return True
        if y > self.h - 1: return True
        if self.tiles[ind] == TILE_WALL: return True
        
        return False
        
    def updt_tile(self, ind):
        """
        Set the tiles number for displaying its state.
        """
        if self.tiles[ind] == TILE_WALL or self.tiles[ind] == TILE_GOAL:
            return

        self.tiles[ind] = ind

    def scan(self, state):
        x, y = self.indextopos(state)
        self.clear_beams()
        return([
            self.beam(x, y, 0, -1),
            self.beam(x, y, 1, -1),
            self.beam(x, y, 1, 0),
            self.beam(x, y, 1, 1),
            self.beam(x, y, 0, 1),
            self.beam(x, y, -1, 1),
            self.beam(x, y, -1, 0),
            self.beam(x, y, -1, -1)
        ])

    def clear_beams(self):
        for i, v in enumerate(self.tiles):
            if v == TILE_BEAM:
                self.tiles[i] = i

    def beam(self, x, y, incX, incY):
        dist = 0
        x += incX
        y += incY

        while not self.tileblocked(x, y):
            i = self.postoindex(x, y)
            if self.tiles[i] == TILE_GOAL:
                dist +=1
                break
            self.tiles[i] = TILE_BEAM
            x += incX
            y += incY
            dist += 1
        return dist

    def left(self, dirn):
        return (dirn - 2) % 8

    def right(self, dirn):
        return (dirn + 2) % 8

    def back(self, dirn):
        return (dirn + 4) % 8

    def front(self, dirn):
        return dirn

    def move(self, agent, dirn):
        offset = dirn_offset[dirn]
        x, y = self.indextopos(agent.state)
        new_x = x + offset[0]
        new_y = y + offset[1]
        new_ind = self.postoindex(self, new_x, new_y)

        if (self.tileblocked(new_ind)):
            return

        agent.state = new_ind
        return 0 if new_ind == TILE_GOAL else new_ind

    def validtiles(self):
        """
        Returns a list of all tiles indices that are not occupied by a
        wall or goal.
        """
        valid = []
        
        for i, t in enumerate(self.tiles):
            if t != TILE_GOAL and t != TILE_WALL:
                valid.append(i)
                
        return valid

    def save(self, filename):
        """
        Saves the gridworld to a given filename.
        """
        world = SavedWorld(self.agentstart,
                           self.w,
                           self.h,
                           self.tiles)
                           
        with open(filename, "wb+") as f:
            pickle.dump(world, f)
        
    def load(self, filename):
        """
        Loads the gridworld from a given filename.
        """
        for t in range(self.w * self.h):
            self.updt_tile(t)
            
        with open(filename, "rb") as f:
            world = pickle.load(f)
            
            self.agentstart = world.agentstart
            self.w = world.w
            self.h = world.h
            self.tiles = world.tiles[:]
            if self.agentstart != AGENTSTART_RAND:
                self.agentstart = 0
#            self.initworld()
