create or replace function
   nTuples(tableName text) returns integer
as $$
declare
	ntup integer;
	query text;
begin
	query := 'select count(*) from '||quote_ident(tableName);
	raise notice 'Query: %',query;
	execute query into ntup;
	-- raise notice '% contains % tuple',tableName,ntup;
	return ntup;
end;
$$
language plpgsql;
