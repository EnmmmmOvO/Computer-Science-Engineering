-- Q8. List of Beers by each brewer

create or replace view Q8(brewer, beers)
as
select manf, string_agg(name,E',')
from   Beers
group by manf
;

-- Q9. Find the beers sold at bars where John drinks.

create or replace view Q9(beer)
as
select S.beer
from   Sells S
       join Frequents F on S.bar = F.bar
where  F.drinker = 'John'
;

-- Q9a. Beers that John likes that are sold at bars where John drinks.

create or replace view Q9a as
-- left as an exercise
select null
;

-- Q10. Bars where either Gernot or John drink.

create or replace view bar_and_drinker as
select b.name as bar, d.name as drinker
from   Bars b
       join Frequents f on (b.name=f.bar)
       join Drinkers d on (d.name=f.drinker)
;

create or replace view Q10 as
select bar from Bar_and_drinker where drinker = 'John'
union
select bar from Bar_and_drinker where drinker = 'Gernot'
;

create or replace view altQ10 as
select bar
from   Bar_and_drinker
where  drinker = 'John' or drinker = 'Gernot'
;

-- Q11. Bars where both Gernot and John drink.

create or replace view Q11 as
select bar from Bar_and_drinker where drinker = 'John'
intersect
select bar from Bar_and_drinker where drinker = 'Gernot'
;

create or replace view badQ10 as
select bar
from   Bar_and_drinker
where  drinker = 'John' and drinker = 'Gernot'
;

-- Q12. Bars where John drinks but Gernot doesn't

create or replace view Q12 as
select bar from Bar_and_drinker where drinker = 'John'
except
select bar from Bar_and_drinker where drinker = 'Gernot'
;

-- Q13. Find bars that serve New at the same price
--      as the Coogee Bay Hotel charges for VB.

create or replace view CBH_VB_price as
select price
from   Sells
where  bar = 'Coogee Bay Hotel'
         and beer = 'Victoria Bitter';
;

create or replace view Q13 as
select bar
from   Sells
where  beer = 'New'
         and price = (select price from CBH_VB_price)
;

-- Q14. Average price for common beers

create or replace view common_beers
as
select beer
from   Sells
group  by beer
having count(*) > 2;

create or replace view Q14
as
select s.beer, avg(s.price)
from   Sells s
       join Common_beers b on s.beer = b.beer
group  by s.beer
;

-- Q15. Bar that sells 'New' cheapest

create or replace view Q15
as
select bar
from   Sells
where  beer = 'New'
       and price = (select min(price) from Sells where beer='New')
;
