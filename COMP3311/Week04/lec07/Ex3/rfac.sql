-- recursive factorial function in PLpgSQL

create or replace function
   rfac(n integer) returns integer
as $$
begin
   if (n < 2) then
      return 1;
   else
      return n * rfac(n-1);
   end if;
end;
$$ language plpgsql;
