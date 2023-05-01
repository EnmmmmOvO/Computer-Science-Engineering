-- simplified version, assuming no FKs

update Beers set price = price * 1.1;

delete from Beers where price > 5.00;

delete from Drinkers where addr = 'Randwick';

delete from Bars where name = 'Royal Hotel';

-- with FKs, need to add "ON DELETE CASCADE" to FKs

