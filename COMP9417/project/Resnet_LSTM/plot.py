import matplotlib.pyplot as plt

train_losses = [475.25749111175537, 387.7689185142517, 349.1760115623474, 322.4096703529358, 306.59865283966064,
                299.7450485229492, 295.9956750869751, 292.76387071609497, 287.28673219680786, 283.2317090034485,
                275.6252541542053, 270.3070135116577, 263.4680771827698, 257.66494941711426, 250.23087739944458,
                246.2524757385254]
valid_losses = [418.494345664978, 362.4117307662964, 332.0487208366394, 308.16444063186646, 298.35606622695923,
                293.3205804824829, 289.55892753601074, 285.6541757583618, 279.7811789512634, 274.1253914833069,
                265.9090414047241, 259.0818934440613, 253.65500402450562, 243.86913394927979, 240.23712873458862,
                235.96835899353027]


plt.figure(figsize=(10, 7))
plt.title(f'BATCH_SIZE: 20; LEARNING_RATE: 1e-4; DATASET: 1k')
steps = [50 * i for i in range(1, len(train_losses) + 1)]  # create a new x axis where each value is the index times 50
plt.plot(steps, train_losses, label='Train loss', color='blue')  # specify color as blue
plt.plot(steps, valid_losses, label='Test loss', color='orange')  # specify color as orange
plt.xlabel('Step')
plt.ylabel('Loss')
plt.legend()
plt.savefig("losses.png", format="png")
plt.show()