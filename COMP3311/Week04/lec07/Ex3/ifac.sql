-- iterative factorial function in PLpgSQL

create or replace function
   ifac(n integer) returns integer
as $$
declare
   i   integer;
   fac integer := 1;
begin
   for i in 2..n loop
      fac = fac * i;
   end loop;
   return fac;
end;
$$ language plpgsql;
