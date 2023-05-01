-- COMP3311 Prac 03 Exercise
-- Schema for simple company database

create table Employees (
	tfn         char(11) primary key,
	givenName   varchar(30),
	familyName  varchar(30),
	hoursPweek  float,
	salary      integer
);

create table Departments (
	id          char(3) primary key,
	name        varchar(100),
	manager     char(11)
);

create table DeptMissions (
	department  char(3),
	keyword     varchar(20)
);

create table WorksFor (
	employee    char(11) references Employees(tfn),
	department  char(3) references Departments(id),
	percentage  float
);
