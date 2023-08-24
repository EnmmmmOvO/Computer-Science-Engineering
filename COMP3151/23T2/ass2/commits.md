## Assignment 2 Peer Review Task



- #### Producer Consumer / Scala-Akka

  1. Names of the team members reviewed: 

     >  *Manmeet Dhaliwal*

  2.  What did you learn from this video?

     > - The video explained how the actor model could solve the consumer-producer problem in a highly concurrent and distributed system. The actor model ensures that multiple threads or processes can operate without stepping on each other's toes, as they all communicate via messages. It helps prevent issues like deadlocks.
     > - The actor model's core components, such as identity, behaviour, and asynchronous message passing, were well-explained. It helps create a clear picture of how actors work and interact with each other.
     > - The description and live demonstration of Scala's implementation of actors was quite effective. It gives a practical understanding of how to use actors in real-world scenarios.

  3.  What were the best aspects of the video?

     > - The overall flow of the presentation was good, with a clear introduction to the topic, an explanation of key concepts, a demonstration, and a conclusion.
     > - The video draws a diagram several times to show the consumer producers and the buffer's behaviour, visualizing their relationship.
     >
     > - The explanation of how actors can be used to solve the consumer-producer problem was clear and insightful. It effectively shows the practical applications of the actor model.

  4. How could the video be improved?

     > - The part about Scala, Akka and asynchronous programming was a little rushed.
     > - Some explanations could have been clearer. For example, talking about the actor's behaviour and the message queue could be more clearly explained with more precise language and examples.









- #### AVL Trees / Rust

  1. Names of the team members reviewed: 

     > *Khant Zarni* and *Weiyuan (Felix) Li*

  2.  What did you learn from this video?

     > - The discussion about AVL trees and the difficulties associated with implementing concurrency was enlightening. AVL trees, often used for databases due to their fast searching and data storage capabilities, can become disoriented when multiple processes attempt to handle data concurrently.
     > - The video explained different attempts to address these issues, such as Ellis's parallelizing techniques and Kelly's focus on optimizing AVL tree operations to local atomic steps.
     > - The presentation provided an in-depth look at the Rust programming language's concurrency capabilities, including its ability to detect concurrency defects and use object-based concurrency controls, message passing, and send/receive traits.
     > - Applying these Rust concurrency constructs to solve the AVL tree concurrency problem was well-explained and demonstrated.

  3.  What were the best aspects of the video?

     > - The presentation was well-structured, clear introduction, a detailed discussion of concurrency problems with AVL trees, an in-depth exploration of Rust's concurrency constructs, and a demonstration of these constructs' application to solve the AVL tree problem.
     > - The use of Rust to address the concurrency issues in AVL trees was a unique and interesting angle, providing a practical application of the language's concurrency capabilities.

  4. How could the video be improved?

     > - Some parts of the video are obscured by the background, resulting in some words and codes that are harder to recognize.
     > - The presentation could have been more engaging with more visuals or diagrams to help illustrate the concepts, particularly the more complex aspects of Rust's concurrency constructs.