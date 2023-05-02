def find_path(neighbour_fn,
              start,
              goal,
              visited,
              reachable=lambda pos: True,
              depth=100000):

    if start == goal: return [start]
    if depth < 0: return []

    visited.append(start)

    for i in neighbour_fn(start):
        if i not in visited and reachable(i):
            path = find_path(neighbour_fn, i, goal, visited, reachable, depth - 1)
            if len(path) > 0:
                visited.remove(start)
                return [start] + path

    visited.remove(start)
    return []
