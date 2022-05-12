'''
TODO Complete this file by following the instructions in the lab exercise.
'''

integers = [1, 2, 3, 4, 5]
integers[len(integers):] = [6]
total = 0
for number in integers:
    total += number
print(total)

print(sum(integers))