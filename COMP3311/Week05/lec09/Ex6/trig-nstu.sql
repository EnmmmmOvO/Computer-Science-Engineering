-- Classes(id,name,room,day,start,end,quota,nstu)
-- ClassEnrolments(student,class)

create trigger nstu_fix
after insert or delete or update on ClassEnrolments
for each row execute
procedure fix_nstu();

create function
	fix_nstu() returns trigger
as $$
declare
	_nstu integer;
	_quota integer;
begin
	if (TG_OP = 'INSERT') then
		select nstu,quota into _nstu,_quota
		from classes where classes.id=new.class;
		if (_nstu = _quota) then
			raise exception 'Class % is full',new.class;
			return null;
		end if;
		update classes set nstu = nstu+1
		where classes.id = new.class;
	else if (TG_OP = 'DELETE') then
		update classes set nstu = nstu-1
		where classes.id = old.class;
	else if (TG_OP = 'UPDATE') then
		update classes set nstu = nstu+1
		where classes.id = new.class;
		update classes set nstu = nstu-1
		where classes.id = old.class;
	end if;
	return new;
end;
$$ language plpgsql;
