create or replace function
	change(initial text, final text) returns integer
as $$
declare
   x integer := 3;
   y integer;
begin
   update Employees set givenname = final
   where givenname  = initial;
   -- table now contains altered tuples
   x := x + 1;
   y := x + 0;
   return y;
exception
   when division_by_zero then
      -- changes to table are rolled back
      raise notice 'caught division_by_zero';
      return x; -- value returned is 4
end;
$$ language plpgsql;
