-- Q16 Which bar is most popular? 
--     (Maximum number of regular drinkers)

-- Approach:
-- select X from Y where Z = max(Z)

create view Popularity(bar,ndrinkers)
as
select bar, count(drinker)
from   Frequents
group  by bar;

select bar
from   Popularity
where  ndrinkers = (select max(ndrinkers) from Popularity);

-- NOTE: the following gives a different (incorrect) result

select bar
from   Popularity
order  by ndrinkers desc
limit  1;


-- Q17 Which bar is most expensive?
--     (Maximum average price)

create view AvgPrice(bar, avgPrice)
as
select bar, avg(price)
from   Sells
group  by bar;

select bar
from   AvgPrice
where  avgPrice = (select max(avgPrice) from AvgPrice);


-- Q18 Price of cheapest beer at each bar?
-- for each bar { select minimum price }

-- Soln:

create view Cheapest(bar, price)
as
select bar, min(price)
from   Sells
group  by bar;

select * from Cheapest;


-- Q19 Name of cheapest beer at each bar?

-- Basic approach
-- for each s in Sells {
--   if (s.price = min price in s.bar)
--      add s.* to results
-- }

select s.*
from   Sells s
where  s.price = (select min(price) from Sells where bar = s.bar);



-- Q20 Which beers are sold at all bars?

-- Basic approach:
-- for each beer b {
--     BB = set of bars where b is sold
--     AB = set of all bars
--     if (AB == BB) then b is sold at all bars
-- }

-- "foreach beer b" is implemented as:

-- select name
-- from   Beers b
-- where  some-Condition-Involving-b

-- Unfortunately, SQL does not have set equality
-- but it does have set difference and empty set check
-- so rephrase above test as
--
--     if (isEmpty(AB - BB)) then b is sold at all bars

-- Soln:

select name
from   Beers b
where  not exists (                                  -- isEmpty
        (select name from Bars)                      -- AB
        except                                       -- set diff
        (select bar from Sells where beer = b.name)  -- BB
       );

-- alternative approach
-- for each beer b {
--     NA = number of bars
--     NB = number of bars where b sold
--     if (NA == NB) then b is sold at all bars
-- }

-- Since NB is a single number, can be solved using group-by and count

-- Soln:

select beer,count(bar)
from   Sells
group  by beer
having count(bar) = (select count(*) from Bars);

-- Note: the above approach only works in some cases
-- The set-based approach works in all cases


-- Q21 How many drinkers are in each suburb?

create view DrinkerPlaces(suburb,ndrinkers) as
select addr, count(*)
from   Drinkers
group  by addr;


-- Q22 How many bars in suburbs where dinkers live?
--     (must include all such suburbs, even if no bars)

-- A straight join doesn't work, because omits suburbs with no bar

select * from Drinkers d join Bars b on (d.addr = b.addr);

-- Outer join ensures that *all* dinker-suburbs appear

select * from Drinkers d left outer join Bars b on (d.addr = b.addr);

-- Once we've got drinker-suburbs associated with bars,
-- it's a straightforward group and count()
-- But count() is nice in giving zero for NULL cases

-- Soln:

select d.addr, count(b.name)
from   Drinkers d left outer join Bars b on (d.addr = b.addr)
group  by d.addr;

