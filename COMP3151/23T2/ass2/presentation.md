

Good day, everyone. Today, I will discuss an concurrency algorithm in distributed systems known as the Suzuki-Kasami algorithm. This algorithm was proposed by Ichiro Suzuki and Tadao Kasami in 1985 and is an enhancement over the Ricart-Agrawala algorithm, which is a fundamental distributed mutual exclusion algorithm.





-

The Ricart-Agrawala algorithm, a little different from lecutre show, is that in a distributed system, where each node is equal, the algorithm decision is timestamped, and the earlier the sending, the higher the priority. It providing mutual exclusion in a distributed environment, had several limitations. Firstly, it had high communication complexity, It needs to send and recieve message to other node, totally need 2*N message for a critical section. Secondly, it relied on global clock synchronization, which can be challenging to achieve in a distributed system. Lastly, it didn't guarantee fairness, potentially leading to a situation where some processes could starve.

The Suzuki-Kasami algorithm overcomes these limitations. It uses a privilege token for controlling access to the critical section. Only the process holding the token is allowed to enter the critical section, thereby ensuring mutual exclusion. In terms of communication complexity, it only requires N messages per request. Moreover, the Suzuki-Kasami algorithm does not rely on global clock synchronization, making it more suitable for distributed systems.

-

First, let's look at the data structures. Each process maintains two arrays, RN, which records the largest request number for each process, and LN, which records the last request number granted access. We also have a queue, Q, which keeps track of requests. A privilege message is composed of the queue and LN array.

The algorithm consists of two parts: sending requests and receiving requests. When a process wants to enter its critical section, it increments its sequence number in RN and sends a request message to every other process. If the process holds the token and is not in its critical section, it sends the privilege message to the requester. After a process enters its critical section, it updates the corresponding element in LN to its sequence number in RN. It then checks for other processes whose request number is one more than the last granted request and are not in the queue and enqueues them. If the queue is not empty, the process sends the privilege message to the process at the head of the queue.

Now, let's move on to the  receiving part. When a process receives a request, it updates its RN array with the sequence number in the request. If it holds the token and is not in its critical section, it sends the privilege message to the requester.

In this algorithm, send ensures that the token is passed to the next required node the first time when the exit critical section. If there is no waiting node in the queue, send by receives guarantees that the lock can be issued when send is not triggered but holds the lock.

-

Let me introduce the implementation language of the algurithm, Go, also known as Golang. It announced publicly in 2009 by Google and was widely used in server-side development primarily because of its excellent support for concurrency. Go provides the goroutine mechanism as a native concurrency mechanism. Each goroutine requires very little memory, and in practice, you can start many goroutines to respond to concurrent connections. It also provides a unique communication mechanism for goroutines - channel. By default, the channel is a synchronous blocking communication. When it reads or writes, it will hang the goroutine currently operating the channel, which achieves the purpose of communication and realizes synchronization. It can also be set up as an asynchronous channel, where channels have a buffer that allows specific values to be sent without any receiver. The send operation blocks only when the buffer is full.

-

Due to these advantages, the go language was chosen by me to implement this algorithm. First, I defined two structures, a message structure for the request, which contains the node number of the node that issued the request and its current RN value. The other is the token, I put the priority into the token which includes an array of RN and a queue that conforms to FIFO. In addition, there is a process structure, which has an id number, a location where the token is stored, an array of rn's, a marker for wanting to enter the cs, a lock, and two other arrays that record the channel of all nodes, which simulates that each node knows the IP address of the other nodes and the port that accepts requests and token.

For all the channels that accept requests, it simulates the port that carries them, so I set them asynchronous channels that don't block no matter how many requests the port accepts, and may not accept immediately. So I give them ample cache space of 1000.
For all the channels that accept token, since the algorithm is set so that the token is not lost. For the privatege channel , I set it as a synchronous channel to ensure certain acquisitions. In the initialization section, I randomly give a node a token, and when all the settings are complete, I let the process start running.

I give two processes to each system; one is sent, more precisely interpreted as the part where the request enters the critical section. It may be triggered by some other request; Therefore, in my implementation, I replace it with a random time. The other one is recieve, which is asked to keep monitoring the channel to accept the request.

Although in a distributed system, no two nodes will enter the critical section at the same time due to the presence of the token, there is a possibility that both send and receive processes may read or modify the RN array, token and request at the same time, so I have set that when I need to change these values, I need to request a lock before I have set the lock to be requested before changing these values.

The implementation of sending is the same as that mentioned in the algorithm. Still, due to the simulation of network uncertainty in a distributed scenario, I added a random number in the requests sending part, so there is a two per cent chance that the request will be lost. I added a random time to match the delay of the message.

For the receive implementation, after my testing, due to the existence of the lock, it is possible that most of the time, the program is waiting for the token, resulting in a large number of requests will be accumulated in the channel, so I let the receiving part of the request to the lock, all the messages in the channel will be processed. Avoid deadlocks caused by an entire channel while the code is running.



-

Let's look at how the Suzuki-Kasami algorithm addresses some key concerns in concurrent systems:

First, The Suzuki-Kasami algorithm ensures mutual exclusion through the privilege token mechanism for Safety Properties. Only the process of possessing the token can enter the critical section at anytime.

Then, for Liveness Property, The algorithm guarantees freedom from deadlock and starvation. Any process that requests the critical section will eventually receive the token, as the token is always passed to the following process in the request queue. This mechanism prevents deadlock. Furthermore, the use of a queue ensures fairness, avoiding starvation.

The algorithm requires every process to be aware of all other processes in the system, which might be impractical in large-scale systems. Despite the improvements that the Suzuki-Kasami algorithm brings over the Ricart-Agrawala algorithm, it does have some limitations:

First, Its reliance on reliable communication is a potential failure, as the loss of the token can incapacitate the system.

Second, The need for each process to be aware of all other processes can be impractical in large-scale systems.

Lastly, The Suzuki-Kasami algorithm, while employing a queue to store requests, does not explicitly dictate how the following process to receive the token should be selected and, thus, does not fully address the fairness concern present in the Ricart-Agrawala algorithm.

Thus the Suzuki-Kasami algorithm is only a theoretical model for studying and understanding the mutual exclusion problem in distributed systems, which may not be used directly in natural production environments, and will not be used directly due to the instability of network communications.

-

That's all the research I've done on this concurrency algorithm. Please point out any imperfections or errors directly in the comments. Thanks for watching!