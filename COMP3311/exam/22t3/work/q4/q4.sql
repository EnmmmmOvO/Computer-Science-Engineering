-- COMP3311 22T3 Final Exam Q4
-- Function to return average winnings for horses matching a partial name

drop type if exists horse_winnings cascade;
create type horse_winnings as (horse text, average integer);

-- put helper views (if any) here

-- answer: Q4(part_name text) -> setof horse_winnings

create or replace function
    Q4(part_name text) returns setof horse_winnings
as $$
... put PLpgSQL code here ..
$$ language plpgsql;
