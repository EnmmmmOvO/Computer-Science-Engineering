-- COMP3311 20T3 Final Exam
-- Q5: show "cards" awarded against a given team

-- ... helper views and/or functions go here ...

drop function if exists q5(text);
drop type if exists RedYellow;

create type RedYellow as (nreds integer, nyellows integer);

create or replace function
	Q5(_team text) returns RedYellow
as $$
... your PLpgSQL function code goes here ...
$$ language plpgsql
;
