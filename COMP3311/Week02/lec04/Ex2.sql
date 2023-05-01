# mapping employee-department-project ER design

create table Departments (
	name        text,
	location    text not null,
	phone       integer,
#	manager     integer not null,
	primary key (name),
#	foreign key (manager)
#		references Employees(ssn)
);

create table Employees (
	ssn         integer,
	name        text not null,
	birthday    date,
	works_in    text not null,
	primary key (ssn),
	foreign key (works_in)
		references Departments (name)
);

alter table Departments add manager
	integer not null references Employees(ssn);

create table Projects (
	projNo      integer,
	title       text not null,
	budget      float not null,
	primary key (projNo)
);

# could also be called next_of_kin

create table "Next-of-kin" (
    ssn         integer not null references Employees(ssn),
	name        text,
    relationship text,
    phone       integer,
	primary key (ssn,name)
);

create table WorksOn (
	employee    integer,
	project     integer,
	primary key (employee,project)
	foreign key (employee) references Employees(ssn),
	foreign key (project) references Projects(projNo)
);
