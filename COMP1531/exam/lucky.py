'''
lucky
'''

def lucky(startnumber, endnumber, numberofreemoves):
    '''
    input
    '''
    init_list = [x for x in range(startnumber, endnumber + 1, 1)]
    temp_list = init_list
    used_flags = []
    index = 0
    while index <= numberofreemoves:
        index += 1
        for item in temp_list:
            if item not in used_flags:
                flag = item
                used_flags.append(flag)
                break
        if flag == 1:
            continue
        else:
            new_temp_list = []
            for temp_index in range(0, len(temp_list), 1):
                if (temp_index + 1) % flag == 0:
                    continue
                else:
                    new_temp_list.append(temp_list[temp_index])
        temp_list = new_temp_list
    return temp_list
