-- generic count accumulator

create or replace function	
	addone(countSoFar integer, object anyelement) returns integer
as $$
begin
	return countSoFar + 1;
end;
$$ language plpgsql;

create or replace aggregate mycount(anyelement) (
	sfunc     = addone(integer, anyelement),
	stype     = integer,
	initcond  = 0
);

