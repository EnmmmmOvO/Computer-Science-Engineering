def check_password(password):
    
    if password == "password":
        return "Horrible password"
    if password == "123456":
        return "Horrible password"
    if password == "iloveyou":
        return "Horrible password"

    length = len(password)
    cap = 0
    low = 0
    num = 0

    for letter in password:
        if ord(letter) in range(97, 122):
            low += 1
        if ord(letter) in range(65, 91):
            cap +=1
        if ord(letter) in range(48, 57):
            num += 1
    

    if length >= 8 and num >=1:
        if length >= 12 and cap >= 1:
            if low >= 1:
                return "Strong password"
            else:
                return "Moderate password"
        else:
            return "Moderate password"
    else:
        return "Poor password"

if __name__ == '__main__':
    print(check_password("ihearttrimesters"))
    # What does this do?
 