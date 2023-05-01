--
-- Simple bank database
--

create table Branches (
	location varchar(20),
	address  varchar(20),
	assets   real,
	primary key (location)
);

create table Customers (
	name     varchar(10),
	address  varchar(20),
	primary key (name)
);

create table Accounts (
	holder   varchar(10),
	branch   varchar(20),
	balance  real,
	primary key (holder,branch),
	foreign key (holder) references Customers(name),
	foreign key (branch) references Branches(location)
);

create table Employees (
	id	    integer primary key,
	name	varchar(20),
	salary	real
);

create table WorksIn (
    employee integer,
	branch   integer,
	job      varchar(20),
	primary key (employee,branch),
	foreign key (employee) references Employees(id),
	foreign key (branch) references Branches(location)

)
