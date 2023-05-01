-- COMP3311 23T1 Assignment 1
--
-- BeerDB Schema
-- Original version: John Shepherd (Sept 2021)
-- Current version: John Shepherd (Feb 2023)
--
-- To keep the schema a little shorter, I have ignored my usual
-- convention of putting foreign key definitions at the end of
-- the table definition.
--
-- Some general naming principles:
--   max 10 chars in field names
--   all entity tables are named using plural nouns
--   for tables with unique numeric identifier, always call the field "id"
--   for cases where there's a long name and a short name for something,
--      use "name" for the short version of the name (typically for display),
--      and use "longname" for the complete version of the name (which might
--      typically be used in lists of items)
--   for foreign keys referring to an "id" field in the foreign relation,
--      use the singular-noun name of the relation as the field name
--      OR use the name of the relationship being represented
--
-- Null values:
--  for each relation, a collection of fields is identified as being
--    compulsory (i.e. without them the data isn't really usable) and
--    they are all defined as NOT NULL
--  reminder: all of the primary keys (e.g. "id") are non-NULL
--  note also that fields that are allowed to be NULL will need to be
--    handled specially whenever they are displayed e.g. in a web-based
--    interface to this schema
--

-- Types/Domains

create type IngredientType as enum ('hop','grain','adjunct');
create type ContainerType as enum ('bottle','can','growler','keg');

create domain YearValue as integer check (value between 1000 and 2100);
create domain MilliLiters as integer check (value > 0);
create domain URLvalue as text check (value like '%.%');  -- weak check
create domain ABVvalue as real check (value between 0.0 and 100.0);
create domain IBUvalue as integer check (value between 0 and 200);

-- Tables

create table Countries (
	id          integer,  -- would normally use serial in PostgreSQL
	code        char(3) not null,
	name        text not null,
	primary key (id)
);

create table Locations (
	id          integer,  -- would normally use serial in PostgreSQL
	within      integer  not null references Countries(id),
	region      text,  -- state or shire or ...
	metro       text,  -- metroploitan area (e.g. Sydney)
	town        text,  -- in metro area => suburb, outside metro => town
	primary key (id)
);

create table Styles (
	id          integer,  -- would normally use serial in PostgreSQL
	name        text not null,  -- name of style (e.g. lager, IPA)
	min_abv     ABVvalue,
	max_abv     ABVvalue,
	primary key (id)
);

create table Ingredients (
	id          integer,  -- would normally use serial in PostgreSQL
	itype       IngredientType not null,
	name        text not null,
	origin      integer references Countries(id),
	primary key (id)
);

create table Breweries (
	id          integer,  -- would normally use serial in PostgreSQL
	name        text not null,
	founded     YearValue,
	website     URLvalue,
	located_in  integer not null references Locations(id),
	primary key (id)
);

create table Beers (
	id          integer,  -- would normally use serial in PostgreSQL
	name        text not null,
	brewed      YearValue,
	style       integer not null references Styles(id),
	ABV         ABVvalue not null,  -- strength
	IBU         IBUvalue,           -- bitterness
	vintage     YearValue,          -- year brewed
	sold_in     ContainerType,
	volume      MilliLiters,
	notes       text,
	rating      integer not null check (rating between 0 and 10),
	primary key (id)
);

create table Contains (
	beer        integer references Beers(id),
	ingredient  integer references Ingredients(id),
	primary key (beer,ingredient)
);

create table Brewed_by (
	beer        integer references Beers(id),
	brewery     integer references Breweries(id),
	primary key (beer,brewery)
);
