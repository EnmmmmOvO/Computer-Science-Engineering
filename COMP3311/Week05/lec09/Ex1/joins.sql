for rec1 in
   select * from R
loop
   for rec2 in
      select * from S
   loop
      if R.a = S.y then
         return next (R.b, S.z);
      end if;
   end loop;
end loop;

--OR

for rec in
   select R.b, S.z
   from   R join S on R.a = S.y
loop
   return next rec;
end loop;
