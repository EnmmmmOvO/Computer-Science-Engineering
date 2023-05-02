
with open('stepsperepisode.txt', 'r') as f:
    file1 = f.read()

with open('stepsperepisodeQLearning.txt', 'r') as f:
    file2 = f.read()

with open('stepsperepisodeSARSA.txt', 'r') as f:
    file3 = f.read()

if file1 == file2:
    print('Test is same as * QLearning *')
elif file1 == file3:
    print('Test is same as * SARSA *')
else:
    print('Test wrong')

