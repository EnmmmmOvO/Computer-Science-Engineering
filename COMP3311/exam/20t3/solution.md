<center><font size=10pt>COMP3311 20T3 Exam Sample Solutions</font></center>

## Q1

```sql
-- COMP3311 20T3 Final Exam
-- Q1: longest album

create or replace view AlbumLengths("group",title,year,length)
as
select g.name,a.title,a.year,sum(s.length)
from   Groups g join Albums a on g.id = a.made_by
       join Songs s on s.on_album = a.id
group  by g.name,a.title,a.year
;

create or replace view Q1("group",album,year)
as
select "group",title,year
from   AlbumLengths
where  length = (select max(length) from AlbumLengths);
;
```

## Q2

```sql
-- COMP3311 20T3 Final Exam
-- Q2: group(s) with no albums

create or replace view Q2("group")
as
select g.name
from   Groups g left outer join Albums a on g.id = a.made_by
group  by g.name
having count(a.id) = 0
;
```

## Q3

```sql
-- COMP3311 20T3 Final Exam
-- Q3: performer(s) who play many instruments

create or replace view PlayedOn(performer,song,instrument)
as
select performer, song,
       case when instrument like '%guitar%' then 'guitar'
            else instrument
       end
from   PlaysOn
where  instrument <> 'vocals'
;

create or replace view totalInstr(ninstr)
as
select count(distinct instrument)
from   PlayedOn
;

create or replace view nInstrPlayed(pid,name,ninstr)
as
select p.id, p.name, count(distinct pl.instrument)
from   Performers p join PlayedOn pl on p.id=pl.performer
group  by p.id, p.name
;

create or replace view Q3(performer,ninstruments)
as
select p.name, p.ninstr
from   nInstrPlayed p
where  p.ninstr > (select ninstr from totalInstr)/2
;
```

## Q4

```plsql
-- COMP3311 20T3 Final Exam
-- Q4: list of long and short songs by each group

-- ... helper views and/or functions (if any) go here ...

drop function if exists q4();
drop type if exists SongCounts;
create type SongCounts as ( "group" text, nshort integer, nlong integer );

create or replace function
	Q4() returns setof SongCounts
as $$
declare
   ns integer;
   nl integer;
   r1 record;
   r2 record;
   res SongCounts;
begin
   for r1 in select id,name from groups order by name
   loop
      res."group" := r1.name;
      ns := 0; nl := 0;
      for r2 in
         select s.id, s.length
         from   Groups g join Albums a on g.id = a.made_by
                join Songs s on a.id = s.on_album
         where  g.id = r1.id
      loop
         if r2.length < 180
         then
            ns := ns + 1;
         elsif r2.length > 360
         then
             nl := nl + 1;
          end if;
      end loop;
      res.nshort := ns; res.nlong := nl;
      return next res;
   end loop;
end;
$$ language plpgsql
;
```

## Q5

```plsql
-- COMP3311 20T3 Final Exam
-- Q5: find genres that groups worked in

-- ... helper views and/or functions go here ...

drop function if exists Q5();
drop type if exists GroupGenres;

create type GroupGenres as ("group" text, genres text);

create or replace function
    Q5() returns setof GroupGenres
as $$
declare
   r1 record;
   r2 record;
   res GroupGenres;
   genres text;
begin
   for r1 in select id,name from Groups
   loop
      res."group" := r1.name;
      genres := '';
      for r2 in
         select distinct g.name, a.genre
         from   Albums a join Groups g on g.id = a.made_by
         where  g.id = r1.id
         order  by g.name, a.genre
      loop
         if genres = '' then
            genres := r2.genre;
         else
            genres := genres||','||r2.genre;
         end if;
      end loop;
      res.genres := genres;
      return next res;
   end loop;
end;
$$ language plpgsql
;
```

## Q6

```python
#!/usr/bin/python3
# COMP3311 20T3 Final Exam
# Q6: discography for one group, given by Groups.id

import sys
import psycopg2

# ... put helper functions here ...

db = None
cur = None
usage = f"Usage: {sys.argv[0]} GroupID"

# process command-line args

if len(sys.argv) < 2:
   print(usage)
   exit(1)
groupID = sys.argv[1]
if not groupID.isnumeric():
   print(usage)
   exit(1)

# SQL

groupQ = "select name from Groups where id = %s"
albumsQ = "select id,title,year,genre from Albums where made_by = %s order by year, title"
tracksQ = "select title,length,trackno from Songs where on_album = %s order by trackno"

try:
   db = psycopg2.connect("dbname=music")
   cur = db.cursor()
   cur.execute(groupQ, [groupID])
   group = cur.fetchone()
   if not group:
      print("Invalid group ID")
      exit(1)
   print(f"Discography for {group[0]}")
   cur.execute(albumsQ, [groupID])
   for album in cur.fetchall():
      print("-"*20)
      aid,title,year,genre = album
      print(f"{title} ({year}) ({genre})")
      print("-"*20)
      cur.execute(tracksQ, [aid])
      tracks = cur.fetchall()
      for track in tracks:
         title,length,trackno = track
         print(f"{trackno:2d}. {title} ({length//60}:{length%60:02d})")
      
except psycopg2.Error as err:
   print("DB error: ", err)
finally:
   if cur:
       cur.close()
   if db:
      db.close()
```

## Q7

```python
#!/usr/bin/python3
# COMP3311 20T3 Final Exam
# Q7: tracklist for album, given by Albums.id
#     show performers/instruments for each track

import sys
import psycopg2

# ... put helper functions here ...

db = None
cur = None
usage = f"Usage: {sys.argv[0]} AlbumID"

# process command-line args

if len(sys.argv) < 2:
   print(usage)
   exit(1)
albumID = sys.argv[1]
if not albumID.isnumeric():
   print(usage)
   exit(1)

# SQL

albumQ = "select title,year,genre from Albums where id = %s"
tracksQ = """
select id,title,length,trackno
from   Songs
where  on_album = %s order by trackno
"""
playersQ = """
select p.name, string_agg(y.instrument,',')
from   Performers p join PlaysOn y on y.performer = p.id
where  y.song = %s
group  by p.name
"""

try:
   db = psycopg2.connect("dbname=music")
   cur = db.cursor()
   cur.execute(albumQ, [albumID])
   album = cur.fetchone()
   if not album:
      print("Invalid album ID")
      exit(1)
   print(f"{album[0]} ({album[1]}) ({album[2]})")
   cur.execute(tracksQ, [albumID])
   print("="*40)
   tracks = cur.fetchall()
   i = 1
   for track in tracks:
      sid,title,length,tno = track
      print(f"{tno:2d}. {title}")
      i = i + 1
      cur.execute(playersQ, [sid])
      players = cur.fetchall()
      if len(players) == 0:
         print(f"{' ':8s}The whole group")
      else:
         for player in players:
            playr,instr = player
            i2 = instr.split(',')
            i2.sort()
            instr = ','.join(i2)
            print(f"{' '*8}{playr}: {instr}")

except psycopg2.Error as err:
   print("DB error: ", err)
finally:
   if cur:
       cur.close()
   if db:
      db.close()
```

## Q8

```sql
# COMP3311 20T3 Final Exam Q8

(a)

create table U (
	id      serial,
	a       integer not null,
	b       text not null,
	primary key (id)
);

create table M (
	u       integer references U(id),
	m       text,
	primary key (u,m)
);

Notes
=====
Need two tables: U and M
Don't care about precise name of "M"
U must have id, a, b with correct types and "not null"
Don't need "not null" on primary key attributes
In M, PK must be both attributes
In M, "not null" on attributes is optional


(b)

create table S (
	id      serial,
	r       integer references T(id),
	primary key (id)
);

create table T (
	id      serial,
	c       text not null,
	primary key (id)
);


Marking Notes
=============
Assuming tables, attributes ok ...
If table for R, award "c"
If link from T to S instead, "b"
If link from T to S as well, "b+"


(c)

create table P (
	id      serial,
	e       text not null,
	primary key (id)
);

create table Q1 (
	p       integer references P(id),
	f       integer not null,
	primary key (p)
);

create table Q2 (
	p       integer references P(id),
	primary key (p)
);

create table Q3 (
	p       integer references P(id),
	g       integer not null,
	primary key (p)
);

Can't enforce disjoint or total participation

Notes
=====
Must have tables P, Q1, Q2, Q3
Child tables must reference parent (not fussed about FK attr name)
```

## Q9

```plsql
# COMP3311 20T3 Final Exam Q9

(a)

create or replace function q9a() returns trigger
as $$
declare
	nmembers integer;
begin
	select count(performer) into nmembers
	from   MemberOf
	where  in_group = new.in_group and departed is null;
	if (nmembers = 0) then
		update Groups
		set    disbanded = new.departed
		where  id = old.in_group;
	end if;
	return new;   -- not needed
end;
$$ language plpgsql;

create or replace trigger q9a
after update of departed on MemberOf
for each row execute procedure q9a();

Notes
======
use an after update on departed
determine how many members
if 0, mark Groups as disbanded


(b)

create or replace function q9b returns trigger
as $$
declare
	newID integer;
begin
	update Groups
	set    disbanded = current_date
	where  id = old.id;
	newID := newGroupID();
    insert into Groups (id,name,formed,disbanded)
	values (newID, new.name, current_date, null);
	for m in
		select * from MembersOf
		where in_group = old.id and departed is null
	loop
		update MemberOf set departed = current_date
		where  in_group = old.id and performer = m.performer;
		insert into MemberOf(in_group,performer,joined, departed)
		values (newID, m.performer, current_date, null);
	end loop
	return new;   -- not needed
end;
$$ language plpgsql;


create or replace trigger q9b
after update of name on Groups
for each row execute procedure q9b();

-- Marking Notes
-- =============
-- not fussed about syntax ... if there's a gross error, "-"
-- use an after update on name
-- must make new ID and Groups tuple
-- for all members of old group
-- 	mark them as departed (departed=current_date)
--	insert as MemberOf new group (joined=current_date)z
```

## Q10

```
# COMP3311 20T3 Final Exam Q10

(a)

Given
fid -> from,to,distance,departs,arrives,price
aid -> name,range
eid -> ename,salary

Inferred
from,to -> distance

Notes
=====
other FDs are possible, but not as clear as this one
must at least have this
not fussed about precise syntax for FDs
OK to represent as minimised FDs, e.g. aid->name, aid->range


(b)

from,to->distance violates BCNF (not in FLights key (fid))

make new table Route(from,to,distance)
change old table Flights(fid,from,to,departs,arrives,price)

new schema:
Flights(fid,from,to,departs,arrives,price)
Routes(from,to,distance)
Aircraft(aid,aname,range)
Certified(employee,aircraft)
Employees(eid,ename,salary)

Notes
=====
must decompose tables relative to FDs from part (a)
the above is the obvious decomposition, given (a)
```

## Q11

```
# COMP3311 20T3 Final Exam Q11

Notes
=====
Ok to not use implicit projection (see alternatives)
Order of relations in Joins does not matter
Ok to Join before Sel in part (c)


(a)

Res = R
or
Res = Sel[true]R


(b)

Tmp = Sel[c < 0]R
Res = Proj[a,b]Tmp
or
Res(a,b) = Sel[c < 0]R


(c)
 
Tmp1 = Sel[c < 0]R
Tmp2 = Tmp1 Join[b=e] S
Res  = Proj[a,d]Tmp2
or 
Tmp(a,b) = Sel[c < 0]R
Res(a,d) = Tmp Join[b=e] S
or
Tmp1(a,b,c,d,e) = R Join[b=e] S
Res(a,d) = Sel[c<0]Tmp1


(d)

Tmp1 = R Join T
Tmp2 = Tmp1 Join S
Res  = Proj[b,c,e,f]Tmp2
or
Tmp(a,b,c,d,f) = R Join T
Res(b,c,e,f) = Tmp Join S
```

## Q12

```
# COMP3311 20T3 Final Exam Q12

(a)

Conflict on X, T2 -> T1
Conflict on X, T1 -> T2, T1-> T3, T2 -> T3

Cycle in precedence graph
=> not conflict serializable

(b)

Consider serial schedule T2;T1;T3

For X
- nobody does initial read
- T3 does the final write
For Y
- T2 does initial read
- T1 does final write

The concurrent schedule has the same properties
=> view serializable
```