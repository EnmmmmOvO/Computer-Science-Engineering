def reverse_words(string_list):
    length = len(string_list)
    leep = 0
    while leep < length:
        words = string_list[leep].split(" ")
        rev = " ".join(reversed(words))
        string_list[leep] = rev
        leep += 1
    return string_list

if __name__ == "__main__":
    print(reverse_words(["Hello World", "I am here"]))
    # it should print ['World Hello', 'here am I']
