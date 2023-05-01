create or replace function
   priciest(_drinker text) returns text
as $$
select s.beer
from   Sells s join Likes d on s.beer = d.beer
where  d.drinker = _drinker
       and s.price = (select max(price)
                      from   Sells s join Likes d on s.beer = d.beer
                      where  d.drinker = _drinker)
$$ language sql;

