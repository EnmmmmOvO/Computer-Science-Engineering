# COMP3311 21T3 Ass2 ... Python helper functions
# add here any functions to share between Python scripts 
# you must submit this even if you add nothing

def getProgram(db,code):
  cur = db.cursor()
  cur.execute("select * from Programs where code = %s",[code])
  info = cur.fetchone()
  cur.close()
  if not info:
    return None
  else:
    return info

def getProgID(db,code):
  if code:
    info = getProgram(db,code)
    if not info:
      return None
    else:
      return info[0]

def getStream(db,code):
  cur = db.cursor()
  cur.execute("select * from Streams where code = %s",[code])
  info = cur.fetchone()
  cur.close()
  if not info:
    return None
  else:
    return info

def getStreamID(db,code):
  if code:
    info = getStream(db,code)
    if not info:
      return None
    else:
      return info[0]

def getLastPlan(db,stuID):
  cur = db.cursor()
  pqry = '''
   select p.id, p.code, p.name, pe.id
   from   program_enrolments pe join programs p on pe.program = p.id
   where  pe.student = %s
          and pe.term=(select max(term) from program_enrolments where student = %s)
  '''
  sqry = '''
    select s.id, s.code, s.name
    from   stream_enrolments se join streams s on se.stream = s.id
    where  se.partof = %s
  '''
  cur.execute(pqry, [stuID, stuID])
  pinfo = cur.fetchone()
  if not pinfo:
    return None
  cur.execute(sqry, [pinfo[3]])
  sinfo = cur.fetchone()
  cur.close()
  return (pinfo[0],pinfo[1],pinf0[2],sinfo[0],sinfo[1],sinfo[2])

def getStudent(db,zid):
  cur = db.cursor()
  qry = """
  select p.*, c.name
  from   People p
         join Students s on s.id = p.id
         join Countries c on p.origin = c.id
  where  p.id = %s
  """
  cur.execute(qry,[zid])
  info = cur.fetchone()
  cur.close()
  if not info:
    return None
  else:
    return info

def progName(db,pcode):
  cur = db.cursor()
  cur.execute("select name from Programs where code=%s",[pcode])
  name = cur.fetchone()
  cur.close()
  if not name:
    return "???"
  else:
    return name[0]

def streamName(db,scode):
  cur = db.cursor()
  cur.execute("select name from Streams where code=%s",[scode])
  name = cur.fetchone()
  cur.close()
  if not name:
    return "???"
  else:
    return name[0]

def subjName(db,code):
  cur = db.cursor()
  cur.execute("select name from Subjects where code=%s",[code])
  name = cur.fetchone()
  cur.close()
  if not name:
    return "???"
  else:
    return name[0]

def unitName(db,uid):
  cur = db.cursor()
  cur.execute("select longname from Orgunits where id=%s",[uid])
  name = cur.fetchone()
  cur.close()
  if not name:
    return "???"
  else:
    return name[0]
