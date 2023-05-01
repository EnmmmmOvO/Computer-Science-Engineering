-- "safe" division function

create or replace function
   div(n integer, m integer) returns integer
as $$
declare
	res integer;
begin
	res := n / m;
	return res;
exception
	when division_by_zero then
		raise NOTICE 'divided % by zero', n;
		return null;
end;
$$ language plpgsql;
