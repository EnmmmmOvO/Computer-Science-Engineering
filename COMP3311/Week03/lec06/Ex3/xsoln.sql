;

-- Q10. Beers sold at bars where John drinks.

drop view if exists Q10;
create view Q10 as
select distinct(b.name) as beer
from   Frequents f
         join Drinkers d on (d.id=f.drinker)
         join Sells s on (s.bar=f.bar)
         join Beers b on (b.id=s.beer)
where  d.name = 'John'
;

-- Q10a. Beers that John likes that are sold at bars where John drinks.

drop view if exists Q10a;
create view Q10a as
select distinct(b.name) as beer
from   Frequents f
         join Drinkers d on (d.id=f.drinker)
         join Sells s on (s.bar=f.bar)
         join Beers b on (b.id=s.beer)
         join Likes L on (L.drinker=d.id and L.beer=b.id)
where  d.name = 'John'
;

-- Q11. Bars where either Gernot or John drink.

drop view if exists bar_and_drinker;
create view bar_and_drinker as
select b.name as bar, d.name as drinker
from   Bars b
         join Frequents f on (b.id=f.bar)
         join Drinkers d on (d.id=f.drinker)
;

drop view if exists Q11;
create view Q11 as
select bar from Bar_and_drinker where drinker = 'John'
union
select bar from Bar_and_drinker where drinker = 'Gernot'
;

-- Q12. Bars where both Gernot and John drink.

drop view if exists Q12;
create view Q12 as
select bar from Bar_and_drinker where drinker = 'John'
intersect
select bar from Bar_and_drinker where drinker = 'Gernot'
;

-- Q13. Bars where John drinks but Gernot doesn't

drop view if exists Q13;
create view Q13 as
select bar from Bar_and_drinker where drinker = 'John'
except
select bar from Bar_and_drinker where drinker = 'Gernot'
;

-- Q14. What is the most expensive beer?

drop view if exists Beer_bar_prices;
create view Beer_bar_prices as
select b.name as beer, r.name as bar, s.price
from   Beers b
         join Sells s on (s.beer=b.id)
         join Bars r on (s.bar=r.id)
;

drop view if exists Q14;
create view Q14 as
select beer
from   Beer_bar_prices
where  price = (select max(price) from Beer_bar_prices)
;

-- Q15. Find bars that serve New at the same price
--      as the Coogee Bay Hotel charges for VB.

drop view if exists CBH_VB_price;
create view CBH_VB_price as
select price
from   Beer_bar_prices
where  bar = 'Coogee Bay Hotel'
         and beer = 'Victoria Bitter';
;

drop view if exists Q15;
create view Q15 as
select bar
from   Beer_bar_prices
where  beer = 'New'
         and price = (select price from CBH_VB_price)
;

-- Q16. Find the average price of common beers
--      ("common" = served in more than two hotels).

drop view if exists Q16;
create view Q16 as
select beer, cast(avg(price) as decimal(5,2)) as "AvgPrice"
from   Beer_bar_prices
group  by beer
having count(bar) > 2
;

-- Q17. Which bar sells 'New' cheapest?

drop view if exists Q17;
create view Q17 as
select bar
from   Beer_bar_prices
where  beer = 'New' and
         price = (select min(price)
                  from   Beer_bar_prices
                  where  beer = 'New')
;

-- Q18. Which bar is most popular? (Most drinkers)

drop view if exists Bar_drinkers;
create view Bar_drinkers as
select b.name as bar, count(*) as ndrinkers
from   Bars b
         left outer join Frequents f on (f.bar=b.id) 
         left outer join Drinkers d on (f.drinker=d.id) 
group  by b.name
;

create view Q18 as
select bar
from   Bar_drinkers
where  ndrinkers = (select max(ndrinkers) from Bar_drinkers)
;

-- Q19. Which bar is least popular? (May have no drinkers)

drop view if exists Q19;
create view Q19 as
select bar
from   Bar_drinkers
where  ndrinkers = (select min(ndrinkers) from Bar_drinkers)
;

-- Q20. Which bar is most expensive? (Highest average price)

drop view if exists Bar_average_price;
create view Bar_average_price as
select b.id, b.name as bar, cast(avg(s.price) as decimal(5,2)) as avg_price
from   Bars b
         join Sells s on (b.id=s.bar)
group  by b.id, b.name
;

drop view if exists Q20;
create view Q20 as
select bar
from   Bar_average_price
where  avg_price = (select max(avg_price) from Bar_average_price)
;

-- Q21. Which beers are sold at all bars?

drop view if exists Q21;
create view Q21 as
select b.name as beer
from   Beers b
        join Sells s on (s.beer=b.id)
where  not exists (
        select id as bar from Bars
        except
        select bar from Sells where beer=b.id
       )
;

-- Q22. Price of cheapest beer at each bar?

drop view if exists Bar_min_price;
create view Bar_min_price as
select b.id, b.name as bar, cast(min(s.price) as decimal(5,2)) as min_price
from   Bars b
         join Sells s on (b.id=s.bar)
group  by b.id, b.name
;

drop view if exists Q22;
create view Q22 as
select bar, min_price
from   Bar_min_price
;

-- Q23. Name of cheapest beer at each bar?

drop view if exists Q23;
create view Q23 as
select bmp.bar, b.name as beer
from   Bar_min_price bmp
         join Sells s on (bmp.id=s.bar)
         join Beers b on (b.id=s.beer)
where  s.price = (select min_price
                  from   Bar_min_price
                  where  bar = bmp.bar)
;

-- Q24. How many drinkers are in each suburb?

drop view if exists Q24;
create view Q24 as
select addr, count(*)
from   Drinkers
group  by addr
;

-- Q25. How many bars in suburbs where drinkers live?
--      (Must include suburbs with no bars)

drop view if exists Q25;
create view Q25 as
select d.addr, count(b.id) as "#bars"
from   Drinkers d
         left outer join Bars b on (d.addr=b.addr)
group  by d.addr
;
