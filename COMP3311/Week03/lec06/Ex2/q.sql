-- COMP3311 

-- Q1. What beers are made by Toohey's?

create or replace view Q1 as
select name from Beers where manf = 'Toohey''s';
;

-- Q2. Show beers with headings "Beer", "Brewer".

create or replace view Q2 as
select name as "Beer", manf as "Brewer" from Beers
;

-- alternative
--create or replace view Q2x("Beer","Brewer") as
-- your SQL goes here
--;

-- Q3. How many different beers are there?

create or replace view Q3 as
select count(name) from beers
;

-- Q4. How many different brewers are there?

create or replace view Q4 as
select count(distinct manf) from beers
;

-- Q5. Find pairs of beers by the same manufacturer
--     (but no pairs like (a,b) and (b,a), and no (a,a))

create or replace view Q5 as
select a.name as aname, a.manf, b.name as bname
from   Beers a join Beers b on a.manf = b.manf
where  a.name < b.name
;

-- Q6a. Which beers does John like?

create or replace view Q6a as
select beer from Likes where drinker = 'John'
;

-- Q6b. Find the brewers whose beers John likes.

create or replace view Q6b as
select distinct Beers.manf
from   Likes join Beers on Likes.beer = Beers.name
where  Likes.drinker = 'John'
;

-- Q7a. How many beers does each brewer make?

create or replace view Q7a(brewer,nbeers) as
select manf, count(name)
from   Beers
group by manf;
;

-- Q7b. Which brewer makes the most beers?

create or replace view Q7b as
select brewer
from   q7a
where  nbeers = (select max(nbeers) from q7a)
;

create or replace view badQ7b as
select brewer
from   Q7a
order  by nbeers desc
limit  1
;

-- Q7c. Beers that are the only one by their brewer.

create or replace view Q7c as
select name
from   Beers
where  manf in (select brewer from q7a where nbeers = 1)
;
