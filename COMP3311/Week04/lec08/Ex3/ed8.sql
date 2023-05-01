create or replace function
	empdept1() returns setof EmpDept
as $$
select e.givenname||' '||e.familyname, d.name, w.percentage
from   Employees e
       join WorksFor w on w.employee = e.tfn
       join Departments d on w.department = d.id
$$ language sql;


create or replace function
	empdept2() returns setof EmpDept
as $$
declare
	ed record;
begin
	for ed in
		select e.givenname||' '||e.familyname,
               d.name, w.percentage
		from   Employees e
		       join WorksFor w on w.employee = e.tfn
		       join Departments d on w.department = d.id
	loop
		return next ed;
	end loop;
end;
$$ language plpgsql;


create or replace function
	empdept3() returns setof EmpDept
as $$
declare
	emp record; -- (tfn,name)
	wrk record; -- (department,percentage)
	dep record; -- Departments(id,name,manager)
	res EmpDept;
begin
	for emp in
		select e.tfn, e.givenname||' '||e.familyname as name
		from   Employees e
	loop
		for wrk in
			select department, percentage
			from   WorksFor where employee = emp.tfn
		loop
			for dep in
				select *
				from   Departments
				where  id = wrk.department
			loop
				res.employee := emp.name;
				res.department := dep.name;
				res.fraction := wrk.percentage;
				return next res;
			end loop;
		end loop;
	end loop;
end;
$$ language plpgsql;

