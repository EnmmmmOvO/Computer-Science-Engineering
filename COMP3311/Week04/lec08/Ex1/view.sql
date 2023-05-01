
-- a view on the Drinkers table (no phone)

create or replace view d1(drinker,suburb)
as
select name, addr
from   drinkers
;
