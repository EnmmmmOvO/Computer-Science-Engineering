-- create table R (id integer, val text);
-- create table S (r integer references R(id), value text);

create or replace function
   check_S_fk() returns trigger
as $$
begin
    perform * from R where id = new.r;
    if (not found) then
		raise NOTICE 'Invalid S.r value';
        if (TG_OP = 'INSERT') then
            return null;
        end if;
        if (TG_OP = 'UPDATE') then
            return old;
        end if;
    else
        return new;
    end if;
end;
$$ language plpgsql;


create trigger S_fk_check
before insert or update on S
for each row execute
procedure check_S_fk();
