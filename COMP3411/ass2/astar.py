import pqueue

def manhattan_dist(a, b):
    """
    Returns the Manhattan distance between two points.
    
    >>> manhattan_dist((0, 0), (5, 5))
    10
    >>> manhattan_dist((0, 5), (10, 7))
    12
    >>> manhattan_dist((12, 9), (2, 3))
    16
    >>> manhattan_dist((0, 5), (5, 0))
    10
    """
    return abs(a[0] - b[0]) + abs(a[1] - b[1])

def find_path(neighbour_fn,
              start,
              end,
              cost = lambda pos: 1,
              reachable = lambda pos: True,
              heuristic = manhattan_dist):
    """
    Returns the path between two nodes as a list of nodes using the A*
    algorithm.
    If no path could be found, an empty list is returned.
    
    The cost function is how much it costs to reach the given node. This should
    always be greater than or equal to 1, or shortest path is not guaranteed.
    
    The reachable function returns true if the given node is not blocked by a wall.
    
    The heuristic function takes two nodes and computes the distance between the
    two. Underestimates are guaranteed to provide an optimal path, but it may
    take longer to compute the path. Overestimates lead to faster path
    computations, but may not give an optimal path.
    """
    # tiles to check (tuples of (x, y), cost)
    open = pqueue.PQueue()
    open.update(start, 0)
    
    # tiles we've been to
    closed = set()
    
    # associated G and H costs for each tile (tuples of G, H)
    costs = { start: (0, heuristic(start, end)) }
    
    # parents for each tile
    parents = {}
    
    while open and (end not in closed):
        cur, c = open.pop_smallest()
        closed.add(cur)
        
        # check neighbours
        for n in neighbour_fn(cur):
            # skip it if we've already checked it, or if it isn't blocked
            if ((n in closed) or (not reachable(n))):
                continue
                
            if not (n in open):
                # we haven't looked at this tile yet, so calculate its costs
                g = costs[cur][0] + cost(cur)
                h = heuristic(n, end)
                costs[n] = (g, h)
                parents[n] = cur
                open.update(n, g + h)
            else:
                # if we've found a better path, update it
                g, h = costs[n]
                new_g = costs[cur][0] + cost(cur)
                if new_g < g:
                    g = new_g
                    open.update(n, g + h)
                    costs[n] = (g, h)
                    parents[n] = cur
    
    # we didn't find a path
    if end not in closed:
        return []
    
    # build the path backward
    path = []
    while end != start:
        path.append(end)
        end = parents[end]
    path.append(start)
    path.reverse()
    
    return path
