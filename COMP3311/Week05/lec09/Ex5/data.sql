create table R (id integer primary key, val text);
create table S (r integer references R(id), value text);

insert into R values (1,'John'), (2,'Andrew'), (3,'Susan'), (4,'Sapna');

insert into S values (1, 'old'), (1, 'fat'), (2,'smart');
