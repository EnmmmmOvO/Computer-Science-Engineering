from pylab import *

BUCKETSIZE = 1000

def main():
    steps = [n for n in loadtxt("./log")]
    buckets = [sum(steps[i:i+BUCKETSIZE]) / BUCKETSIZE for i in range(0, len(steps), BUCKETSIZE)]
    
    plot(buckets, label="Average delta per {:,d} steps".format(BUCKETSIZE))
    legend()
    
    title("Learning curve over {:,d} steps".format(len(steps)))
    xlabel("{:,d}-step bucket".format(BUCKETSIZE))
    savefig("learncurve.png", bbox_inches='tight')
    
if __name__ == '__main__':
    main()
    show()
