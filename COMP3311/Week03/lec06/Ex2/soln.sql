-- COMP3311 

-- Q1. What beers are made by Toohey's?

create or replace view Q1 as
select name
from   Beers
where  manf = 'Toohey''s';
;

-- Q2. Show beers with headings "Beer", "Brewer".

create or replace view Q2 as
select name as "Beer", manf as "Brewer"
from   Beers
;

-- Q3. How many different beers are there?

create or replace view Q3 as
select count(*) as "#beers"
from   Beers
;

-- Q4. How many different brewers are there?

create or replace view Q4 as
select count(distinct manf) as "#brewers"
from   Beers
;

-- Q5. Find pairs of beers by the same manufacturer
--     (but no pairs like (a,b) and (b,a), and no (a,a))

create or replace view Q5 as
select b1.name as beer1, b2.name as beer2
from   Beers b1
       join Beers b2 on (b1.manf=b2.manf)
where  b1.name < b2.name
;

-- Q6b. Find the brewers whose beers John likes.

create or replace view Q6b as
select distinct(r.name) as brewer
from   Drinkers d
         join Likes L on (d.name=L.drinker)
         join Beers b on (L.beer=b.name)
where  d.name = 'John'
;

-- Q7a. How many beers does each brewer make?

create or replace view Q7a as
select manf as brewer, count(*) as nbeers
from   Beers
group  by manf
;

-- Q7b. Which brewer makes the most beers?

create or replace view Q7b as
select brewer
from   Q7a
where  nbeers = (select max(nbeers) from Q7a);
;

-- Q7c. Beers that are the only one by their brewer.

create or replace view Q7c as
select name
from   Beers
where  manf in (select brewer from Q7a where nbeers=1)
