-- string concatenation aggregate

create or replace function
	join(state text, next text) returns text
as $$
select state||','||next
$$ language sql;

create or replace function
	strip(state text) returns text
as $$
select substring(state,2)
$$ language sql;

create or replace aggregate cat(text) (
	sfunc     = join(text,text),
	stype     = text,
	initcond  = '',
	finalfunc = strip(text)
);


/*
-- using this definition of join() means
-- we don't need final function
create or replace function
	join(state text, next text) returns text
as $$
begin
	if (state = '') then
		state := next;
	else
		state := state||','||next;
	end if;
	return state;
end;
$$ language plpgsql;
*/
