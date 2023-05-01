--
-- Functions to compute salary totals
--

-- First version of salary total function
-- The best way to do it; use built-in DB aggregation

create or replace function
	totsal0() returns real
as $$
declare
	total real;
begin
	select into total sum(salary)
	from Employees;
	return total;
end;
$$ language plpgsql;


-- Second version of salary total function
-- To illustrate the use of FOR loops on queries

create or replace function
	totsal() returns real
as $$
declare
	emp record;
	total real := 0;
begin
	for emp in select * from Employees
	loop
		total := total + emp.salary;
	end loop;
	return total;
end;
$$ language plpgsql;


-- Third version of salary total function
-- To illustrate the use of explicit cursors with queries

create or replace function
	totsal1() returns real
as $$
declare
	e cursor for select * from Employees;
	emp record;
	total real := 0;
begin
	open e;
	loop
		fetch e into emp;
		exit when not found;
		total := total + emp.salary;
	end loop;
	close e;
	return total;
end;
$$ language plpgsql;
