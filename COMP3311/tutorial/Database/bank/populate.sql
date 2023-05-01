--
-- Simple bank database
--
-- Should only run this after triggers in assets.sql are installed
-- Otherwise branches will all end up with assets of ZERO
--

-- Populate Branches table

insert into Branches values ('Clovelly', 'Clovelly Rd.',   0);
insert into Branches values ('Coogee',   'Coogee Bay Rd.', 0);
insert into Branches values ('Maroubra', 'Anzac Pde.',     0);
insert into Branches values ('Randwick', 'Alison Rd.',     0);
insert into Branches values ('UNSW',     'near Library',   0);


-- Populate Customers table

insert into Customers values ('Adam',   'Randwick');
insert into Customers values ('Bob',    'Coogee');
insert into Customers values ('Chuck',  'Clovelly');
insert into Customers values ('David',  'Kensington');
insert into Customers values ('George', 'Maroubra');
insert into Customers values ('Graham', 'Maroubra');
insert into Customers values ('Greg',   'Coogee');
insert into Customers values ('Ian',    'Clovelly');
insert into Customers values ('Jack',   'Randwick');
insert into Customers values ('James',  'Clovelly');
insert into Customers values ('Jane',   'Bronte');
insert into Customers values ('Jenny',  'La Perouse');
insert into Customers values ('Jill',   'Malabar');
insert into Customers values ('Jim',    'Maroubra');
insert into Customers values ('Joe',    'Randwick');
insert into Customers values ('John',   'Kensington');
insert into Customers values ('Keith',  'Redfern');
insert into Customers values ('Steve',  'Coogee');
insert into Customers values ('Tony',   'Coogee');
insert into Customers values ('Victor', 'Randwick');
insert into Customers values ('Wayne',  'Kingsford');


-- Populate Accounts table

insert into Accounts values ('Adam',   'Coogee',   1000.00);
insert into Accounts values ('Adam',   'UNSW',     2000.00);
insert into Accounts values ('Bob',    'UNSW',      500.00);
insert into Accounts values ('Chuck',  'Clovelly',  660.00);
insert into Accounts values ('David',  'Randwick', 1500.00);
insert into Accounts values ('George', 'Maroubra', 2000.00);
insert into Accounts values ('Graham', 'Maroubra',  400.00);
insert into Accounts values ('Greg',   'Randwick', 9000.00);
insert into Accounts values ('Ian',    'Clovelly', 5500.00);
insert into Accounts values ('Jack',   'Coogee',    500.00);
insert into Accounts values ('James',  'Clovelly', 2700.00);
insert into Accounts values ('Jane',   'Maroubra',  350.00);
insert into Accounts values ('Jenny',  'Coogee',   4250.00);
insert into Accounts values ('Jill',   'UNSW',     5000.00);
insert into Accounts values ('Jim',    'UNSW',     2500.00);
insert into Accounts values ('Joe',    'UNSW',      900.00);
insert into Accounts values ('John',   'UNSW',     5000.00);
insert into Accounts values ('Keith',  'UNSW',      880.00);
insert into Accounts values ('Steve',  'UNSW',     1500.00);
insert into Accounts values ('Tony',   'Coogee',   2500.00);
insert into Accounts values ('Victor', 'UNSW',      250.00);


-- Populate Employees table

insert into Employees values (1,  'David',  75000.00);
insert into Employees values (2,  'John',   70000.00);
insert into Employees values (3,  'Andrew', 75000.00);
insert into Employees values (4,  'Peter',  55000.00);
insert into Employees values (5,  'Lucy',   25000.00);
insert into Employees values (6,  'Tim',    30000.00);
insert into Employees values (7,  'Ken',    50000.00);
insert into Employees values (8,  'Wendy',  60000.00);
insert into Employees values (9,  'Steve',  45000.00);
insert into Employees values (10, 'Sue',    35000.00);

