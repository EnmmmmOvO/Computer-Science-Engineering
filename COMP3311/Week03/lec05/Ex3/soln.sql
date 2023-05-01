-- Variations on a view on the drinkers table
-- Drinkers(name,addr,phone)

-- returns (name,addr,phone) tuples
-- effectively just a shorthand for Drinkers

create or replace view b
as
select * from Drinkers;


-- returns (drinker,lives_in) tuples

create or replace view b2
as
select name as drinker, addr as lives_in
from   Drinkers;


-- returns (drinker,lives_in) tuples

create or replace view b3(drinker,lives_in)
as
select name,addr from Drinkers;


-- b2 and b3 are effectively the same
