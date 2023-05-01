update Beers set price = price * 1.1;

delete from Beers where price > 5.00;

delete from Drinkers where addr = 'Randwick';

delete from Hotels
where name = 'Royal' and addr = 'Randwick';
