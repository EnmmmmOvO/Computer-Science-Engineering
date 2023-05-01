-- a function version of the d1 view

drop type if exists dInfo cascade;
create type dInfo as (drinker text, suburb text);
 
create or replace function
	d2() returns setof dInfo
as $$
declare
	d dInfo;
begin
	for d in
		select name as drinker, addr as suburb
		from   drinkers
	loop
		return next d;
	end loop;
end;
$$
language plpgsql
;
 
create or replace function
	d3(_name text) returns setof dInfo
as $$
declare
	d dInfo;
begin
	for d in
		select name as drinker, addr as suburb
		from   drinkers
		where  name ~ _name
	loop
		return next d;
	end loop;
	if not found then
		raise notice 'No matching drinker';
	end if;
end;
$$
language plpgsql
;
