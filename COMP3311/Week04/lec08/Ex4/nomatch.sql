create or replace function
	tfnOf1(_name text) returns text
as $$
declare
	_tfn text;
begin
	select tfn into _tfn from Employees
	where givenname = _name;
	if (not found) then
		--return 'No such employee';
		raise exception 'No such employee: %',_name;
		return null;
	else
		return _tfn;
	end if;
end;
$$ language plpgsql;

-- create or replace function
-- 	tfnOf2(name text) returns text
-- as $$
-- $$ language plpgsql;
