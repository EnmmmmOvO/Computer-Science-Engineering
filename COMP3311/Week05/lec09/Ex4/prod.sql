-- integer product aggregate

create or replace function
	accum(prodSoFar integer, nnext integer) returns integer
as $$
select prodSoFar * nnext
$$ language sql;

create or replace aggregate product(integer) (
	sfunc     = accum(integer,integer),
	stype     = integer,
	initcond  = 1
);

