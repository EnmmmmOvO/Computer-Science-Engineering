   for rec in
      select * from R
   loop
      if (rec.a = 5) then
         ...
      end if;

   end loop

-- OR

   for rec in
      select * from R where a = 5
   loop
      ...
   end loop;

