create type PopulationRecord as (tablename text, ntuples integer);

create or replace function
	dbpop() returns setof PopulationRecord
as $$
declare
	rec record;
	qry text;
	res PopulationRecord;
	num integer;
begin
	for rec in select tablename from pg_tables where schemaname='public' order by tablename
	loop
		qry := 'select count(*) from ' || quote_ident(rec.tablename);
		execute qry into num;
		res.tablename := rec.tablename; res.ntuples := num;
		return next res;
	end loop;
	return;
end;
$$ language plpgsql;
