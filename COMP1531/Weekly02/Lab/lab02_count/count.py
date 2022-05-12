def count_char(input):
    dictionary = {}
    
    length = len(input)
    leep = 0
    while leep < length:
        if input[leep] in dictionary:
            dictionary[input[leep]] += 1
        else:
            dictionary[input[leep]] = 1
        leep += 1
    
    return dictionary

if __name__ == "__main__":
    print(count_char("HelloOo!"))
        





    '''
    Counts the number of occurrences of each character in a string. The result should be a dictionary where the key is the character and the dictionary is its count.

    For example,
    >>> count_char("HelloOo!")
    {'H': 1, 'e': 1, 'l': 2, 'o': 2, 'O': 1, '!': 1}
    '''
    pass
