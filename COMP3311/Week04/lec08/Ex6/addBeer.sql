-- function to add a new beer

create or replace function
   addBeer(_name text, _brewery text,
	           _style text, _abv float)
   returns integer
as $$
declare
	rid integer;
	bid integer;
	sid integer;
begin
	select id into bid from breweries
	where name = _brewery;
	if (not found) then
		raise exception 'No such brewer: %', _brewery;
		return null;
	end if;
	select id into sid
	from Styles where name = _style;
	if (not found) then
		raise exception 'No such style: %', _style;
		return null;
	end if;
	select max(id)+1 into rid from Beers;
	insert into Beers (id,name,style,abv,rating)
	values (rid,_name,sid,_abv,0);
	insert into Brewed_by (beer,brewery)
	values (rid,bid);
	return rid;
end;
$$ language plpgsql
;

-- if Beers.id was defined as serial
--
-- insert into Beers (id,name,style,abv,rating)
-- values (default,_name,sid,_abv,0)
-- returning id into rid;
