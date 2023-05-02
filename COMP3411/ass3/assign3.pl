% COMP3411 23T1 Assignment3 - Planning and Machine Learning
% Written by: Jinghan Wang z5286124
% Written on: 19/04/2023

% ----------------------------------------------------------------------------------
% Question 1: Planning
% ----------------------------------------------------------------------------------

% Define the move clockwise start and end loction

move_clockwise(cs, off).
move_clockwise(off, lab).
move_clockwise(lab, mr).
move_clockwise(mr, cs).

% Define the move counterclockwise start and end loction

move_counterclockwise(off, cs).
move_counterclockwise(lab, off).
move_counterclockwise(me, lab).
move_counterclockwise(lab, off).

% Acrion - move clockwise

action(mc, state(RLoc, RHC, SWC, MW, RHM), state(NewRloc, RHC, SWC, MW, RHM)) :- 
    move_clockwise(RLoc, NewRloc).

% Acrion - move counterclockwise

action(mcc, state(RLoc, RHC, SWC, MW, RHM), state(NewRloc, RHC, SWC, MW, RHM)) :- 
    move_counterclockwise(RLoc, NewRloc).

% Acrion - pick up coffee

action(puc, state(cs, false, SWC, MW, RHM), state(cs, true, SWC, MW, RHM)).

% Acrion - deliver coffee

action(dc, state(off, true, true, MW, RHM), state(off, false, false, MW, RHM)).

% Acrion - pick up mail

action(pum, state(mr, RHC, SWC, true, false), state(mr, RHC, SWC, false, true)).

% Acrion - deliver mail

action(dm, state(off, RHC, SWC, MW, true), state(off, RHC, SWC, MW, false)).

% plan(StartState, FinalState, Plan)

plan(State, State, []).				% To achieve State from State itself, do nothing

plan(State1, GoalState, [Action1 | RestofPlan]) :-
	action(Action1, State1, State2),		% Make first action resulting in State2
	plan(State2, GoalState, RestofPlan). 		% Find rest of plan

% Iterative deepening planner
% Backtracking to "append" generates lists of increasing length
% Forces "plan" to ceate fixed length plans

id_plan(Start, Goal, Plan) :-
    append(Plan, _, _),
    plan(Start, Goal, Plan).

% ----------------------------------------------------------------------------------
% Question 2: Inductive Logic Programming
% ----------------------------------------------------------------------------------

% Define Operation '<-'

:- op(300, xfx, <-).

% Inter_construction

inter_construction(C1 <- B1, C2 <- B2, C1 <- D1, C2 <- D2, C <- B) :-
    C1 \= C2,
    intersection(B1, B2, B),
    B \= [],
    gensym(z, C),
    subtract(B1, B, B11),
    subtract(B2, B, B12),
    append(B11, [C], D1),
    append(B12, [C], D2).

% ----------------------------------------------------------------------------------
% Question 2.1 Intra-construction
% ----------------------------------------------------------------------------------

intra_construction(C1 <- B1, C1 <- B2, C1 <- B, C2 <- D1, C2 <- D2) :-
    intersection(B1, B2, B3),
    B3 \= [],
    gensym(z, C2),
    subtract(B1, B3, D1),
    subtract(B2, B3, D2),
    append(B3, [C2], B).

% ----------------------------------------------------------------------------------
% Question 2.2 Absorption
% ----------------------------------------------------------------------------------

absorption(C1 <- B1, C2 <- B2, C1 <- B, C2 <- B2) :-
    C1 \= C2,
    subset(B2, B1),
    subtract(B1, B2, ZB),
    append(ZB, [C2], B).

% ----------------------------------------------------------------------------------
% Question 2.3 Truncation
% ----------------------------------------------------------------------------------

truncation(C <- B1, C <- B2, C <- B) :- intersection(B1, B2, B), B \= [].

