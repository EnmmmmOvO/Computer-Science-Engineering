% The graph is reprsented by a set of edge clauses.

edge(o103, ts).
edge(o103, b3).
edge(o103, o109).
edge(ts, mail).
edge(b3, b1).
edge(b3, b4).
edge(b1, c2).
edge(b1, b2).
edge(c2, c1).
edge(c2, c3).
edge(c1, c3).
edge(b2, b4).
edge(b4, o109).
edge(o109, o119).
edge(o109, o111).
edge(o119, o123).
edge(o119, storage).
edge(o123, o125).
edge(o123, r123).

% The goal is also asserted into the database
goal(r123).


% depthfirst(CurrentNode, PathSoFar)
% This version does not check fo cycles

% Check if the goal node has beeen reached
depthfirst1(N, [N]) :-
	 goal(N).

% Put the current node at the front of the path list,
% then explore each neighbouring node, exploiting Prolog's
% backtracking to maintain a stack implictly
depthfirst1(N, [N|Path]) :-
	edge(N, Neighbour),
	depthfirst1(Neighbour, Path).


% solve(Node, Solution)
% Solution is a path (in reverse order) from start node to a goal state.
% We keep the path visited so we can check is we've been there before
solve_dfs(Node, Solution)  :-
	depthfirst2([], Node, Solution).

% depthfirst(Path, Node, Solution)
% Use depth first search to find a solution recursively.

% If the next node to be expanded is a goal node, add it to
% the current path and return this path.
depthfirst2(Path, Node, [Node|Path])  :-
	goal(Node).

% Otherwise, use Prolog backtracking to explore all successors
% of the current node, in the order returned by s.
depthfirst2(Path, Node, Sol)  :-
	edge(Node, Node1),
	\+ member(Node1, Path),		% Prevent a cycle
	depthfirst2([Node|Path], Node1, Sol).


% A simple breadthfirst traversal of the graph. It only checks
% if a node is reachable from the start. It does not build the
% path.

reachable(Goal, [Goal|_]).
reachable(Goal, [First|Rest]) :-
	neighbours(First, Neighbours),
	union(Rest, Neighbours, NewQ),
	writeln(NewQ),
	reachable(Goal, NewQ).
reachable(Goal, [_|Rest]) :-
	reachable(Goal, Rest).

% The neighbours predicate relates a node to the collection of its neighbours.
% The findall built-in predicate performs collects all N such that
% edge(Node, N) is true and puts them in the list Neighbours.

neighbours(Node, Neighbours) :-
	findall(N, edge(Node, N), Neighbours).


% Breadthfirst search, based on the imeplementation by Bratko.
% Store the paths generated but not yet expanded in a queue,
% sorted in order of increasing path depth (number of nodes).
% Each path is a list of nodes in reverse order,
% with the start node at the back end of the list.
%
% If the next path to be expanded reaches a goal node,
% return this path.
%
% Otherwise, take the path at the front of the queue and extend it,
% by adding successors of its head node. Append these newly
% created paths to the back of the queue, and keep searching.
%
% e.g. solve(o103, Solution).

solve_bfs(Start, Solution)  :-
	breadthfirst([[Start]], Solution).
    
breadthfirst([[Node|Path]|_], [Node|Path]) :-
	goal(Node).
breadthfirst([Path|Paths], Solution)  :-
	extend(Path, NewPaths),
	append(Paths, NewPaths, Paths1),
	breadthfirst(Paths1, Solution).

extend([Node|Path], NewPaths)  :-
    findall([Neighbour, Node|Path],
            new_neighbour([Neighbour, Node|Path]),
            NewPaths).

new_neighbour([Neighbour, Node|Path]) :-
	edge(Node, Neighbour),
	\+ member(Neighbour, [Node|Path]).    % exclude repeated states


% Depth-bounded search is the same as the somepl depthfirst search,
% except that it stops if it exceeds the depth limit, which is passed
% as the 3rd argument,
% e.g. bounded_search(o103, Solution, 5).

bounded_search(N, [N], _) :-
	goal(N).
bounded_search(N, [N|Path], D) :-
	D > 0,
	Depth is D - 1,
	edge(N, Neighbour),
	bounded_search(Neighbour, Path, Depth).

% Iterative deepening is an extension of the depth-bounded search.
% Call the depth bounded search with increasing limits until the
% goal is reached or a maximum depth is reached.
% e.g. iter(o103, Solution, 1, 10).

iter(Start, Solution, L, MaxDepth) :-
	L < MaxDepth,
	bounded_search(Start, Solution, L), !.
iter(Start, Solution, L, MaxDepth) :-
	L < MaxDepth,
	Limit is L + 1,
	write("Increasing limit to "), writeln(Limit),
	iter(Start, Solution, Limit, MaxDepth).
