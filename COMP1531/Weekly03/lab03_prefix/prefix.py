def prefix_search(dictionary, key_prefix):
    new_dict = {}
    length = len(key_prefix)
    for key, value in dictionary.items():
        if len(key) >= length and key[:length] == key_prefix:
            new_dict[key] = value
    return new_dict