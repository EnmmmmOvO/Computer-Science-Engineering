-- return a given drinker's favourite beers

create or replace function
   favBeers(_drinker text) returns setof Beers
as $$
declare
	res record;
	_name text;
	_manf text;
begin
	for res in
		select b.*
		from   Beers b join Likes L on L.beer = b.name
		where  L.drinker = _drinker
	loop
		return next res;
	end loop;
	select name,manf into _name,_manf
	from   Beers where name = 'New';
	res.name := _name;
	res.manf := _manf;
	return next res;
	raise notice 'Name is %',_name;
end;
$$ language plpgsql;
