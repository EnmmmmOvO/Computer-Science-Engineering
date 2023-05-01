-- COMP3311 23T1 Assignment 1

-- Q1: amount of alcohol in the best beers

-- Top rating beers are so delicious that you can't stop drinking once you open a container (bottle/can)
-- containing one of them. Of course, you need to be careful how much alcohol you're consuming as you finish
-- the contents of the container.

-- Define an SQL view Q1(beer,"sold in",alcohol) that gives the name of a highly rated beer
-- (rating must be greater than 9), the size/kind of container that it's sold in, and what volume of alcohol
-- is in that container. This can be computed by (volume * ABV / 100). Examples of the precise format of each
-- tuple is shown on the examples page.

create or replace view Q1(beer, "sold in", alcohol)
as
    select name,
           volume || 'ml ' || sold_in,
           cast(volume * abv / 100 as decimal(5,1)) || 'ml'
    from beers
    where (rating > 9);
;

-- Q2: beers that don't fit the ABV style guidelines

-- Beer styles are defined by an international panel in terms of the ABV, the bitterness, the colour, and the
-- aroma/flavours that you can expect in beers of that style. This database defines styles just in terms of
-- minimum allowed ABV and maximum allowed ABV.

-- Define an SQL view Q2(beer,style,abv,reason) that gives a list of beers that are out-of-style (i.e. their
-- ABV is either to low or too high for that style). For each such beer, give its name, the style that it claims
-- to be, its actual ABV, and a reason why it is out-of-style. See the examples file for the format of the reasons.
-- Use numeric(4,1) to define the format of ABV values and ABV differences.

create or replace view Q2(beer, style, abv, reason)
as
    select b.name, s.name, b.abv,
           case
               when b.abv < s.min_abv then 'too weak by ' || cast(s.min_abv - b.abv as decimal(4,1)) || '%'
               else 'too strong by ' || cast(b.abv - s.max_abv as decimal(4,1)) || '%'
           end
    from beers b join styles s on b.style = s.id
    where b.abv < s.min_abv or b.abv > s.max_abv;
;

-- Q3: Number of beers brewed in each country

-- Define a view Q3(country,"#beers") that gives a list of all countries and the number of beers brewed in that
-- country (according to this database). The list should include all countries; if a country makes no beers, give
-- a count of zero. Assume that collaboration beers are brewed in both breweries, and count the countries for both
-- breweries. Even if both breweries are in the same country, count it as two separate beers for that country.

create or replace view Q3(country, "#beers")
as
    select c.name, count(bb.beer)
    from countries c
        left join locations l on c.id = l.within
        left join breweries b on l.id = b.located_in
        left outer join brewed_by bb on b.id = bb.brewery
    group by c.name
    order by c.name
;

-- Q4: Countries where the worst beers are brewed

-- Define a view Q4(beer,brewery,country) that gives information about the worst beers in the world. "Worst" is
-- determined by having a rating less than 3. Show the name of the offending beer, the offending brewery, and the
-- country where the beer was made.

create or replace view Q4(beer,brewery,country)
as
    select beer.name, b.name, c.name
    from beers beer
        left join brewed_by bb on beer.id = bb.beer
        left join breweries b on bb.brewery = b.id
        left join locations l on l.id = b.located_in
        left join countries c on l.within = c.id
    where beer.rating < 3
;

-- Q5: Beers that use ingredients from the Czech Republic

-- Define a view Q5(beer,ingredient,type) that gives the name of beers that use ingredients whose origin in the
-- Czech Republic.

create or replace view Q5(beer, ingredient, "type")
as
    select beer.name, i.name, i.itype
    from beers beer
        left join contains contain on beer.id = contain.beer
        left join ingredients i on contain.ingredient = i.id
        left join countries c on i.origin = c.id
    where c.name = 'Czech Republic'
;

-- Q6: Beers containing the most used hop and the most used grain

-- Define a view Q6(beer) that gives the names of beers that use both the most popular hop and most popular grain
-- in their ingredients.
--
-- For the purposes of this exercise, treat "rolled" and "flaked" versions of grains as different from the base
-- grain (e.g. "flaked wheat" is not the same as "wheat"). Similarly, treat "cryo" versions of hops and different
-- from the base hop (e.g. "simcoe cryo" is not the same as "simcoe")

create or replace view Q6(beer)
as
    select distinct b.name as beer
    from beers b
        join contains c1 on c1.beer = b.id
        join contains c2 on c2.beer = b.id
        join ingredients i1 on i1.id = c1.ingredient
        join ingredients i2 on i2.id = c2.ingredient
    where i1.itype = 'hop' and i2.itype = 'grain'
        and i1.name in (
            select i.name
            from contains c
                join ingredients i on i.id = c.ingredient
            where i.itype = 'hop'
            group by i.name
            order by count(*) desc
            limit 1)
        and i2.name in (
            select i.name
            from contains c
                join ingredients i on i.id = c.ingredient
            where i.itype = 'grain'
            group by i.name
            order by count(*) desc
            limit 1);
;

-- Q7: Breweries that make no beer

-- Define a view Q7(brewery) that gives the names of any breweries that make no beers (accoring to this database).

create or replace view Q7(brewery)
as
    select b.name as brewery
    from breweries b
        left join brewed_by bb on b.id = bb.brewery
    where bb.beer is null
    order by b.name;
;

-- Q8: Function to give "full name" of beer

-- Write a PLpgSQL function that takes a beer id and returns the "full name" of the beer. The "full name" is formed
-- by prepending (part of) the brewery name to the beer name.

-- *** create or replace function Q8(beer_id integer) returns text ... ***

-- You can work out beer IDs by looking the the Beers table. If you give an invalid beer ID, the function should
-- return the string 'No such beer'.

-- It doesn't make sense to include 'Brewing Co' or 'Beer Co' or 'Brewery' from the brewery name in the "full name",
-- so you should filter these out using the regular expression ' (Beer|Brew).*$'. If this filtering produces an
-- empty string, use the complete name of the brewery.

-- An example: "Mountain Culture Beer Co" is a brewery that makes a beer called "Cult IPA". We want this to appear
-- as "Mountain Culture Cult IPA" and not as "Mountain Culture Beer Co Cult IPA". Similarly, "Sierra Nevada
-- Brewing Company" makes a beer called "Pale Ale". We want this to have the full name "Sierra Nevada Pale Ale".

-- If the beer is brewed collaboratively, all breweries should appear before the beer name in their shortened
-- form, and separated by ' + '. You can assume that no collaboration involves more than two breweries. The
-- order that the breweries appear should be alphabetical on brewery name.

-- There are examples of how the function should behave in the Examples page.

create or replace function
	Q8(beer_id integer) returns text
as
$$
declare
    beer_name text;
    brewery_name text;
    total_brewery_name text := '';
begin
    select name into beer_name from beers where id = beer_id;

    if beer_name is null then
        return 'No such beer';
    end if;

    for brewery_name in (select b.name
                         from brewed_by bb
                                  join breweries b on bb.brewery = b.id
                         where bb.beer = beer_id
                         order by b.name) loop
        if brewery_name ~ ' (Beer|Brew).*$' then
            brewery_name := substring(brewery_name from '^(.*) (Beer|Brew).*$');
        end if;
        if total_brewery_name = '' then
            total_brewery_name := brewery_name;
        else
            total_brewery_name := total_brewery_name || ' + ' || brewery_name;
        end if;
    end loop;

    if brewery_name = '' then
        return beer_name;
    else
        return total_brewery_name || ' ' || beer_name;
    end if;
end;
$$ language plpgsql
;

-- Q9: Beer data based on partial match of beer name

-- Write a PostgreSQL function that takes a string as argument and gets information about all beers that
-- contain that string somewhere in their name (use case-insensitive matching).

-- *** create or replace function Q9(partial_name text) returns setof BeerData ... ***

-- The BeerData type has three components:

-- beer: the name of the beer
-- brewer: the name of the brewery/breweries who make the beer
-- info: the ingredients used in making the beer
-- Note that some beers involve two breweries who collaborate in making the beer. These beers should not
--      be shown twice, once for each brewer. Instead, the brewer column should contain the names of all
--      breweries in alphabetical order, and separated by ' + '. There are examples of this in the Examples
--      page.

-- The info should presented as a single text string, formatted as up to three lines: one containing a
-- comma-separated list of hops, one containing a comma-separated list of grains, and one containing a
-- comma-separated list of adjuncts. If no information is available about one of these types of ingredients,
-- do not include a line for that type. Do not include a final '\n' character in the result string.

-- An example of what the info should look like for a beer that uses all ingredient types:

-- ***
-- Hops: Bravo,Centennial,Mosaic
-- Grain: Oats,Pale,Rye,Treticale,Wheat
-- Extras: Lactose,Vanilla
-- ***

-- The comma-separated ingredient lists should be in alphabetical order.
--
-- For collaboration beers, both breweries should appear, in alphabetical order and separated by ' + '.
-- For this question, you cannot assume that collaborations involve only two breweries.

-- Note that psql put a '+' at the end of each line to indicate that the string spans multiple lines.
-- Ignore this; it's an output artifact.

-- There are more examples of how the function should behave in the Examples page. In particular,
-- if there are no beers matching the partial_name, simply return an empty table (0 rows).

drop type if exists BeerData cascade;
create type BeerData as (beer text, brewer text, info text);

create or replace function
	Q9(partial_name text) returns setof BeerData
as
$$
declare
    beer record;
    beer_data BeerData;
    temp_text text;
begin
    for beer in select be.id as "id", be.name as "name",
               array_agg(distinct b.name order by b.name) as "brewires",
               array_agg(distinct h.name order by h.name) as "hops",
               array_agg(distinct g.name order by g.name) as "grains",
               array_agg(distinct a.name order by a.name) as "adjuncts"
        from beers be
            left join brewed_by bb on be.id = bb.beer
            left join breweries b on b.id = bb.brewery
            left join contains c on be.id = c.beer
            left join (
                select id as "id", name as "name"
                from ingredients
                where itype = 'hop') h on h.id = c.ingredient
            left join (
                select id as "id", name as "name"
                from ingredients
                where itype = 'grain') g on g.id = c.ingredient
            left join (
                select id as "id", name as "name"
                from ingredients
                where itype = 'adjunct') a on a.id = c.ingredient
        where lower(be.name) like '%' || lower(partial_name) || '%'
        group by be.id
        order by be.id
    loop
        beer_data.beer = beer.name;
        beer_data.brewer = array_to_string(array(SELECT UNNEST(beer.brewires)), ' + ');
        beer_data.info = '';

        temp_text := array_to_string(array(SELECT UNNEST(beer.hops)), ',');
        if temp_text != '' then
            beer_data.info := 'Hops: ' || temp_text ;
        end if;

        temp_text := array_to_string(array(SELECT UNNEST(beer.grains)), ',');
        if temp_text != '' then
            if beer_data.info != '' then
                 beer_data.info := beer_data.info || E'\n';
            end if;
            beer_data.info := beer_data.info || 'Grain: ' || temp_text ;
        end if;

        temp_text := array_to_string(array(SELECT UNNEST(beer.adjuncts)), ',');
        if temp_text != '' then
            if beer_data.info != '' then
                 beer_data.info := beer_data.info || E'\n';
            end if;
            beer_data.info := beer_data.info || 'Extras: ' || temp_text ;
        end if;
        return next beer_data;
    end loop;
end;
$$ language plpgsql
;

