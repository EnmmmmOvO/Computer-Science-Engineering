--
-- Functions to solve the "down-sizing" exercise
--

-- Returns a list of names of people to be retrenched

create or replace function
   retrenched(availSalaryBudget real) returns text
as $$
declare
   totSal  real;
   victims text := '';
   emp     record;
begin
   select into totSal sum(salary)
   from Employees;
   for emp in select * from Employees order by salary
   loop
      exit when totSal < availSalaryBudget;
      victims := victims || ',' || emp.name;
      totSal := totSal - emp.salary;
   end loop;
   if (victims = '') then
      return 'Nobody needs to be sacked';
   else
      return substr(victims,2,length(victims));
   end if;
end;
$$ language plpgsql;


-- Returns a table containing tuples for Employees to be laid off

create or replace function
   retrenched(availSalaryBudget real) returns setof Employees
as $$
declare
   totSal  real;
   emp     record;
begin
   select into totSal sum(salary)
   from Employees;
   for emp in select * from Employees order by salary
   loop
      exit when totSal < availSalaryBudget;
      return next emp;
      totSal := totSal - emp.salary;
   end loop;
   return;
end;
$$ language plpgsql;


-- Deletes employees who are to be laid off

create or replace function
   retrench(budget real) returns void
as $$
begin
	 delete from Employees
	 where id in (select id from retrenched(budget));
	 return;
end;
$$ language plpgsql;
