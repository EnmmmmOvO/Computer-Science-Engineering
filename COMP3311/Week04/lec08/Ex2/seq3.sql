-- seq(n,m,inc)

create or replace function
	seq(lo integer, hi integer, inc integer) returns setof integer
AS $function$
declare
	i integer;
begin
	i := lo;
	while i <= hi
	loop
		return next i;
		i := i + inc;
	end loop;
end;
$function$
language plpgsql;

create or replace function seq(hi integer) returns setof integer
as $$
begin
	return query select * from seq(1,hi,1);
end;
$$ language plpgsql;
