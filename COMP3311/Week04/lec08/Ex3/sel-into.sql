declare
	x integer;
	y text;	
	z text;
	rec R;   -- or R%rowtype

begin

	select a,b,c into x,y,z from R ...
OR
	select * into rec from R ...
	x := rec.a;
	y := reb.b;
	z := rec.c;

end;
