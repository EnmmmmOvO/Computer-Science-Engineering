-- Write "something" to give a list of
-- (EmployeeName, DepartmentName, fraction)
-- tuples

-- As a view

create or replace view
   empdept(employee,department,fraction)
as
select e.givenname||' '||e.familyname, d.name, w.percentage
from   Employees e
       join WorksFor w on w.employee = e.tfn
       join Departments d on w.department = d.id
;

-- As various kinds of function

create or replace function
   EmpDept() returns setof EmpDept
as $$
select e.givenname||' '||e.familyname as employee,
       d.name as department, w.percentage as fraction
from   Employees e
       join WorksFor w on w.employee = e.tfn
       join Departments d on w.department = d.id
$$ language sql;

create or replace function
   ed2() returns setof EmpDept
as $$
begin
	return query 
		select e.givenname||' '||e.familyname as employee,
		       d.name as department, w.percentage as fraction
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id;
end;
$$ language plpgsql;

create or replace function
   ed3() returns setof EmpDept
as $$
declare
	ed record;  -- could also be EmpDept
begin
	for ed in 
		select e.givenname||' '||e.familyname as employee,
		       d.name as department, w.percentage as fraction
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id
	loop
		return next ed;
	end loop;
end;
$$ language plpgsql;

create or replace function
   ed4() returns setof EmpDept
as $$
declare
	ed record;  -- could also be EmpDept
begin
	for ed in 
		select e.givenname||' '||e.familyname as employee,
		       d.name as department, w.percentage as fraction
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id
	loop
		raise notice 'Next emp: %',ed.employee;
		return next ed;
	end loop;
end;
$$ language plpgsql;

create or replace function
   ed5() returns setof EmpDept
as $$
declare
	i  integer := 1;
	ed record;  -- could also be EmpDept
begin
	for ed in 
		select e.givenname||' '||e.familyname as employee,
		       d.name as department, w.percentage as fraction
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id
	loop
		raise notice '%: %', i, ed.employee;
		return next ed;
		i := i + 1;
	end loop;
end;
$$ language plpgsql;

create or replace function
   ed6(_dept text) returns setof EmpDept
as $$
declare
	ed  record;  -- could also be EmpDept
	q   text;
begin
	q :=
	'select e.givenname||'' ''||e.familyname as employee,
	       d.name as department, w.percentage as fraction
	from   Employees e
	       join WorksFor w on w.employee = e.tfn
	       join Departments d on w.department = d.id
    where  d.name = '''||_dept||'''';
	raise notice 'Query is %',q;
	for ed in 
		execute q
	loop
		return next ed;
	end loop;
end;
$$ language plpgsql;

create or replace function
   ed7(_dept text) returns setof text
as $$
declare
	ed  record;  -- could also be EmpDept
begin
	for ed in 
		select e.givenname||' '||e.familyname
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id
        where  d.name = _dept
	loop
		return next ed;
	end loop;
end;
$$ language plpgsql;

create type DeptEmps as (dept text, workers text);

create or replace function
   ed7() returns setof DeptEmps
as $$
declare
	d   Departments;
	e   Employees;
	de  DeptEmps;
	names text;
	gname text;
begin
	for d in
		select * from Departments
	loop
		names := '';
		for e in
			select m.*
			from   Worksfor w
                   join Employees m on w.employee = m.tfn
            where  w.department = d.id
			order by givenname
		loop
			gname := e.givenname;
			if names = '' then
				names := gname;
			else
				names := names || ', ' || gname;
			end if;
		end loop;
		de.dept := d.name;
		de.workers := names;
		return next de;
	end loop;
end;
$$ language plpgsql;

