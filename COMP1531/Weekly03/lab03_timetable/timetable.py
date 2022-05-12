from datetime import date, time, datetime


def timetable(dates, times):
    tt = []
    for date in dates:
        for time in times:
            tt.append(datetime.combine(date, time))
    tt.sort()
    return tt
