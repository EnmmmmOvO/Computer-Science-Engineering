-- generate a sequence of integers from 1..N

create or replace function
	iota(_max integer) returns setof integer
as $$
declare
	i integer;
begin
	for i in 1 .. _max
	loop
		return next i;
	end loop;
end;
$$ language plpgsql;
