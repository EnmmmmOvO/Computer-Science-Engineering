create or replace function
	lookup(key integer) returns text
as $$
declare
	name text;
begin
	select R.name into name
	from R where id = key;
	if (not found) then
		raise exception 'No such key %',key;
	end if;
	if (name is null) then
		raise exception '% has no name",key;
	end if;
	return name;
end;
$$ language plpgsql;

	select count(*) into nres from R where id = key;
	if (nres = 0) then
		raise exception 'No such key %',key;
	end if;

	select R.name into name from R where id = key;
	if (name is null) then
		raise exception 'No such key %',key;
	end if;
	
