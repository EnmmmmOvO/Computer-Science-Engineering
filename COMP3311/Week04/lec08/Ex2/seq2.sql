-- seq(n,m)

create or replace function
	seq(lo integer, hi integer) returns setof integer
AS $function$
declare
	i integer;
begin
	for i in lo..hi
	loop
		return next i;
	end loop;
end;
$function$
language plpgsql;
