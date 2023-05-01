# mapping ER publishing model
# (using ER-style subclass mapping)

create table People (
	tfn integer primary key,
	name text,
	address text
);

create table Authors (
	tfn integer references People(tfn),
	primary key (tfn)
);

create table Publishers (
	abn integer primary key,
	name text,
	address text
);

create table Editors (
	tfn integer references People(tfn),
	works_for integer not null
	          references Publishers(abn),
	primary key (tfn)
);

create table Books (
	isbn ISBNtype primary key,
	title text not null,
	edition integer not null,
	publisher integer not null
	         references Publishers(abn),
	editor integer not null
	         references Editors(ssn)
);

create table Writes (
	author integer references Authors(tfn),
	book ISBNtype references books(isbn),
	pen_name text,
	primary key (author,book)
);
