-- COMP3311 21T3 Exam Q4
-- Return address for a property, given its ID
-- Format: [UnitNum/]StreetNum StreetName StreetType, Suburb Postode
-- If property ID is not in the database, return 'No such property'

create or replace function address(propID integer) returns text
as
$$
declare
	... your PLpgSQL variable declarations go here
begin
	... your PLpgSQL function code goes here ...
end;
$$ language plpgsql;
