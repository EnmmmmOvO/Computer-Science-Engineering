-- seq(n)

create or replace function
	seq(n integer) returns setof integer
as $$
declare
	i integer;
begin
	for i in 1..n
	loop
		return next i;
	end loop;
end;
$$
language plpgsql;
