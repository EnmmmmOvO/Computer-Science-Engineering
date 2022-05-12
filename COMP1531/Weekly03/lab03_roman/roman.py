def roman(numerals):

    ret=0
    data={('1',"I"),('2',"II"),('4',"IV"),('5',"V"),('6',"VI"),('9',"IX"),('10',"X"),('50',"L"),('100',"C"),('500',"D"),('1000',"M")}
    i=0
    while(i<len(numerals)):
        isFound=False
        for (m,n) in data:
                if((i+1 < len(numerals)) and (str(numerals[i]+numerals[i+1])==n)):
                    ret=ret+int(m)
                    i=i+1
                    isFound=True
                    break
        if(isFound==False):   
            for (m,n) in data:
                if(numerals[i]==n):
                    ret=ret+int(m)
                    break
        i=i+1
    return ret

print(roman("II"))
print(roman("IV"))
print(roman("IX"))
print(roman("XIX"))
print(roman("XX"))
print(roman("MDCCLXXVI"))
print(roman("MMXIX"))