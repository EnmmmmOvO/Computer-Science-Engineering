'''
acronym
'''

def acronym_make(inputs):
    '''
	input
    '''
    if not inputs:
        raise ValueError
    else:
        res = []
        for input_ in inputs:
            temp = ""
            words = input_.split(" ")
            if len(words) >= 10:
                res.append("N/A")
                continue
            else:
                for word in words:
                    first_letter = word[0].upper()
                    if first_letter not in ["A", "E", "I", "O", "U"]:
                        temp = temp + first_letter
                res.append(temp)
        return res
