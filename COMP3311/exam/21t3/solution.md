<center><font size=10pt>COMP3311 21T3 Exam Sample Solutions</font></center>

## Q1

```sql
-- COMP3311 21T3 Exam Q1
-- Properties most recently sold; date, price and typeof each
-- Ordered by price, then id if prices are equal

create or replace view q1(date, price, type)
as
select sold_date, sold_price, ptype
from   Properties
where  sold_date = (select max(sold_date) from properties)
order  by sold_price, id
;
```

## Q2

```sql
-- COMP3311 21T3 Exam Q2
-- Number of unsold properties of each type in each suburb
-- Ordered by type, then suburb

create or replace view PropAddr(id,uno,sno,street,stype,suburb,pcode)
as
select  p.id, p.unit_no, p.street_no, st.name, st.stype, su.name, su.postcode
from    Properties p
        join Streets st on p.street = st.id
        join Suburbs su on st.suburb = su.id
;

create or replace view q2(suburb, ptype, nprops)
as
select a.suburb, p.ptype, count(p.id)
from   Properties p join propAddr a on a.id = p.id
where  p.sold_price is null
group  by a.suburb, p.ptype
order  by p.ptype,a.suburb
;
```

## Q3

```sql
-- COMP3311 21T3 Exam Q3
-- Unsold house(s) with the lowest listed price
-- Ordered by property ID

create or replace view q3(id,price,street,suburb)
as
select p.id, p.list_price, a.sno||' '||a.street||' '||a.stype, a.suburb
from   Properties p join PropAddr a on p.id = a.id
where  p.ptype='House' and p.sold_price is null and
       p.list_price = (select min(list_price)
                       from properties
                       where ptype = 'House' and sold_price is null)
order by p.id
;
```

## Q4

```plsql
-- COMP3311 21T3 Exam Q4
-- Return address for a property, given its ID
-- Format: [UnitNum/]StreetNum StreetName StreetType, Suburb Postode
-- If property ID is not in the database, return 'No such property'

create or replace function address(propID integer) returns text
as
$$
declare
	addr text := '';
	uno integer;
	sno integer;
	street text;
	stype StreetType;
	suburb text;
	pcode integer;
	number text;
begin
	select p.unit_no, p.street_no, st.name, st.stype, su.name, su.postcode
	into   uno, sno, street, stype, suburb, pcode
	from   Properties p join Streets st on p.street = st.id
	       join Suburbs su on st.suburb = su.id
	where  p.id = propID;
	if not found then
		return 'No such property';
	end if;
	if uno is null then
		number := sno::text;
	else
		number := uno::text||'/'||sno::text;
	end if;
	return number||' '||street||' '||stype||', '||suburb||' '||pcode::text;
end;
$$ language plpgsql;
```

## Q5

```python
#!/usr/bin/python3
# COMP3311 21T3 exam ... property finder

import sys
import psycopg2
import re

# define any local helper functions here

### set up some globals

usage = f"Usage: {sys.argv[0]} type maxPrice #beds #baths #cars\n"\
f"type is one of Apartment, House, Townhouse\n"\
"maxPrice is upper bound; #x = exact match; 0 means don't care"

types = ["Apartment", "House", "Townhouse"]
db = None

### process command-line args

argc = len(sys.argv)
if argc < 6:
  print(usage)
  exit(1)
ptype = sys.argv[1]
if not ptype in types:
  print(usage)
  exit(1)
digits = re.compile("^\d+$")
for arg in sys.argv[2:5]:
  if not digits.match(arg):
    print(usage)
    exit(1)

maxPrice = int(sys.argv[2])
nbeds = int(sys.argv[3])
nbaths = int(sys.argv[4])
ncars = int(sys.argv[5])

# queries

getProps = '''
select p.id, p.list_price, address(p.id)
from   Properties p
where  ptype = %s and list_price <= %s and sold_price is null
order  by p.list_price, p.id
'''
getFeats = '''
select feature, number
from   Features
where  property = %s
'''

# manipulate database

try:
  db = psycopg2.connect("dbname=pp")

  pcur = db.cursor()
  fcur = db.cursor()
  pcur.mogrify(getProps, [ptype,maxPrice])
  pcur.execute(getProps, [ptype,maxPrice])

  for prop in pcur.fetchall():
    pid,price,addr = prop

    actbeds = 0
    actbaths = 0
    actcars = 0
    fcur.execute(getFeats, [pid])
    for feat in fcur.fetchall():
      fname,fno = feat
      if fname == "bedrooms":
        actbeds = fno
      if fname == "bathrooms":
        actbaths = fno
      if fname == "carspaces":
        actcars = fno
    if (nbeds == 0 or nbeds == actbeds) and (nbaths == 0 or nbaths == actbaths) and (ncars == 0 or ncars == actcars):
      print(f"#{pid}: {addr}, {actbeds}br, {actbaths}ba, {actcars}car, ${price}")

  fcur.close()
  pcur.close()

except Exception as err:
  print("DB error: ", err)
finally:
  if db:
    db.close()
```

## Q6

```sql
# COMP3311 21T3 Final Exam Q6
# SQL schema from ER design

create table Users (
    id serial,
    name text not null,
    email text not null,
    primary key (id)
);

create table Recipes (
    id serial,
    title text not null,
    owner integer not null, -- total participation
    primary key (id),
    foreign key (owner) references Users(id)
);

create table RecipeTags (
    recipe integer,
    tag text,
    primary key (recipe, tag),
    foreign key (recipe) references Recipes(id)
);

-- Satisfies 'a recipe can be associated with zero or more tags'

-- There is no constraint on the possible tag strings,
-- the question only lists some of them

create table Ingredients (
    id serial,
    name text not null,
    primary key (id)
);

create table Uses ( -- Recipe uses Ingredient
    recipe integer,
    ingredient integer,
    amount integer not null, -- not null, otherwise doesn't make sense
    unit text not null,
    primary key (recipe, ingredient),
    foreign key (recipe) references Recipes(id),
    foreign key (ingredient) references Ingredients(id),
    constraint positive_amount check (amount > 0)
);
-- the participation constraint "every recipe has at least one ingredient"
-- cannot be expressed in the relational schema
```

## Q7

```
# COMP3311 21T3 Final Exam Q7
# Python/Psycopg2 scripts

(A)
Yes the two scripts produce the same output. 
Both scripts will output each term and the subjects the 
student was enrolled in for each term.

ScriptA
- get all terms student has been enrolled
- for each term
    - print the term code
    - get subjects student has enrolled in, in the specific term 
    - for each subject
        - print subject code and subject name

ScriptB
- get all terms and subjects student has been enrolled in 
- keep a previous variable to identify if the term we are looking at has changed
- for each tuple 
    - if the current term is different to the previous one we were looking at
        - print term code 
    - print subject code and subject name 
    - set the previous variable to hold the current term code we are looking at


(B)
ScriptA calls execute() 11 times.
It calls it once to get the 10 terms,
then for each term it calls execute() once to get the relevant subjects.

Script B calls execute() 1 time.
it calls once to get all 10 terms + all subjects.


(C)
ScriptB is likely to be faster since it is only making ONE call to the database. 
Calling to the database is expensive so reducing the amount of calls will make
the script faster.
```

## Q8

```
# COMP3311 21T3 Final Exam Q8
# Query execution times

(A)
When you call a query for the first time it has to load from the disk 
which is expensive. The second time we run the query, the data has
already been loaded into memory buffers, and the DB engine loads it 
from memory instead. Loading from memory is much faster than the
initial disk to memory transfer.


(B)
We assume that id is the primary key for the table "people". 
PostgreSQL automatically creates indexes for primary keys.

Indexes provide efficient content-based access to tuples which speeds
up filtering based on indexed attributes, and therefore the query is faster. 

To find the max, it does an Index Scan Backward, and so finds the maximum
value first. It only needs to look at the index (which contains the key),
and not the data.

Since there is no indexing on birthday, the second query needs to
perform a sequential scan on the "people"table. This is clearly
less efficient than the index scan by the first query.
```

## Q9

```
# COMP3311 21T3 Final Exam Q9
# Flight booking triggers

(A)
If the operation is INSERT ...
- check if the flight number actually exists in the flights table
  - if not found, raise an exception.
- check whether the flight is full (nseats == nbooked)
  - if full, raise an exception
- if all ok, return the new record for further processing

If the operation is DELETE ...
- check if the flight number actually exists in the flights table
  - if not found, raise an exception.
- if all ok, return the old record for further processing

(B)
If the operation is INSERT, we could also check:
- has the passenger already booked a seat for the same flight
- has the seat number requested in the booking already been taken

If the operation is DELETE, we could also check:
- is there a booking for this seat on this flight
- has the departure already passed


(C)
First, run the BEFORE trigger (pre_booking_check)
- check if QF01 exists in the flights table 
- then check if the flight is full, 
  because 25-D is empty that means this seat is available.

Next, perform standard constraint checking
- standard database constraint checks e.g. data types, user defined constraints

Next, run the AFTER trigger (post_booking_update)
- add one to the number of seats booked for the flight in the flights table

Insert the new booking tuple.


(D)
First, check the BEFORE trigger (pre_booking_check)
- check if QF02 exists in the flights table 
- check if the flight is full and raise an exception saying 'Booking error'

No further action on this INSERT


(E)
First, check the BEFORE trigger (pre_booking_check)
- check if QF03 exists in the flights table 
- ok, so move onto standard constraint checking

Next, perform standard constraint checking
- standard database constraint checks e.g. data types, any user defined constraints

Next it will check AFTER trigger (post_booking_update)
- subtract one from the number of seats booked for the flight

Remove the tuple where flight_no = 'QF03' and seat_no = '15-F'
```

## Q10

```
# COMP3311 21T3 Final Exam Q10
# BCNF normalization

(A)
Using common-sense, plausible FDs are:

A -> BC
D -> EF


(B)

AD is the candidate key for ABCDEF

Attrs ABCDEF, FDs A -> BC, D -> EF, Key AD, A -> BC violates BCNF

Split into ABC, ADEF

Attrs ABC, FDs A -> BC, Key A, No FDs violates BCNF so ABC is BCNF

Attrs ADEF, FDs D -> EF, Key AD, D -> EF violates BCNF

Split into AD, DEF

Both AD and DEF are in BCNF ... only FD in DEF is D->EF, no FDs in Ad


(C)
Tables are ABC, AD and DEF

ABC is a table containing student information
including  what thesis topic a student is doing.

AD is a table relating students to supervisors

DEF is a table containing supervisor information
relating the supervisor (id) to their name and specialty
```