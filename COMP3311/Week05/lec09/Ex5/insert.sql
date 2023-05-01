
-- create table R (id integer, val text);
-- create table S (r integer references R(id), value text);

create or replace function
   check_S_insert_fk() returns trigger
as $$
begin
    perform * from R where id = new.r;
    if (not found) then
		raise NOTICE 'Invalid S.r value';
        return null;
    else
        return new;
    end if;
end;
$$ language plpgsql;

create trigger S_fk_insert_check
before insert on S
for each row execute
procedure check_S_insert_fk();
