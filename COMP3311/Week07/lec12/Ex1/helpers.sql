-- COMP3311 21T3 Ass2 ... extra database definitions
-- add any views or functions you need into this file
-- note: it must load without error into a freshly created mymyunsw database
-- you must submit this even if you add nothing to it

create or replace view marks(subj,term,name,zid,mark,grade)
as
select s.code, t.code, s.name, e.student, e.mark, e.grade
from   Subjects s
       join Courses c on s.id = c.subject
       join Course_enrolments e on c.id = e.course
       join Terms t on t.id = c.term
;

create or replace function
    ts(_zid integer) returns setof TranscriptRecord
as $$
select s.code, t.code as term, s.name, e.mark, e.grade, s.uoc
from   Subjects s
       join Courses c on c.subject = s.id
       join Terms t on c.term = t.id
       join Course_enrolments e on e.course = c.id
where  e.student = _zid
$$
language sql;

