<div id="content">
<h1 class="title">Homework (Week 4)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org8315c88">1. Cigarette Smokers Problem (6 marks)</a></li>
<li><a href="#orgf380f32">2. Semaphores with Monitors (6 marks)</a></li>
</ul>
</div>
</div>
<p>
<b>Submission</b>: Due on Friday, 1st of July, 11am Sydney Time. Please submit using the <a href="https://cgi.cse.unsw.edu.au/~give/Student/give.php">CSE Give System</a> either online or via this command on a CSE terminal:
</p>

<div class="org-src-container">
<pre class="src src-sh">give cs3151 hw4 *Semaphore.java CigaretteSmokers.java 
</pre>
</div>

<p>
Late submissions are accepted up to five days after the deadline, but
at a penalty: 5% off your total mark per day.
</p>

<p>
You may also submit any other files with a <code>.java</code> extension, but these are the only ones we need.
</p>

<p>
Download the <a href="../statics/hw4.zip">code</a> to get started with this homework.
</p>

<p>
To avoid name conflicts, <code>signal</code> is here called <code>V()</code> and <code>wait</code> is called <code>P()</code>.
</p>

<div id="outline-container-org8315c88" class="outline-2">
<h2 id="org8315c88"><span class="section-number-2">1</span> Cigarette Smokers Problem (6 marks)</h2>
<div class="outline-text-2" id="text-1">
<p>
Three smokers are rolling their own cigarettes and smoking them. In order to do so, they need three resources: paper, tobacco, and matches.
Each smoker has their own limitless supply of one of the three ingredients. For the other two ingredients, they must acquire them from an 
<i>Agent</i>. They can ask for an Agent to distribute resources to them by signalling on the <code>agent</code> semaphore. One of the <code>Agent</code> threads will then awaken,
and produce two of the three different resources by signalling on two of the three semaphores <code>tobacco</code>, <code>paper</code> and <code>match</code>.
 Note that the smoker has no control over which <code>Agent</code> thread awakens and which resources are produced.
</p>

<p>
The existing code where smokers get resources directly from the agents is highly vulnerable to a deadlock scenario. 
In this exercise, we will implement a solution to this problem that ensures progress by introducing a "middle-man" between the agents and smokers.
</p>

<dl class="org-dl">
<dt>Step One</dt><dd>Introduce a dedicated semaphore for each smoker, and the smoker will just wait on that semaphore, smoke a cigarette, and signal an agent forever.</dd>
<dt>Step Two</dt><dd>Add a thread called a <i>pusher</i> for each of the three resources. The pusher will perpetually:
<ol class="org-ol">
<li>Wait for its resource to become available.</li>
<li>Update some shared state (shared with the other pushers) regarding what resources are available.</li>
<li>If two of the three resources are available, update the shared state to remove those resources, and signal the smoker that requires those two resources, to indicate that they may smoke the cigarette.</li>
</ol></dd>
<dt>Caution</dt><dd>You must make the loop body of the pusher a critical section - mutual exclusion is required when accessing the shared state. You can accomplish this by adding another semaphore for the pushers to use.</dd>
</dl>
</div>
</div>

<div id="outline-container-orgf380f32" class="outline-2">
<h2 id="orgf380f32"><span class="section-number-2">2</span> Semaphores with Monitors (6 marks)</h2>
<div class="outline-text-2" id="text-2">
<p>
In the <code>ProducerConsumer</code> module you will find an implementation of the Producer-Consumer problem we analysed in class. This (and the Cigarette Smokers example from earlier) use a semaphore class called <code>JavaSemaphore</code> that wraps around Java's built-in semaphores. We have two other classes, <code>BusyWaitSemaphore</code> and <code>WeakSemaphore</code>, without implementations added.
</p>

<dl class="org-dl">
<dt>Step One</dt><dd>Using <b>only</b> Java's built-in concurrency primitives, specifically <code>synchronized</code> blocks/methods and <code>Thread.yield()</code>, implement a busy-wait semaphore in <code>BusyWaitSemaphore</code>. You can test it using <code>ProducerConsumer</code> or <code>CigaretteSmokers</code>. (3 marks)</dd>
<dt>Step Two</dt><dd>Using <b>only</b> Java's built-in concurrency primitives and monitor-like constructs, specifically <code>synchronized</code> blocks, <code>Object.wait()</code> and <code>Object.notify()</code>, implement a weak semaphore in <code>WeakSemaphore</code>. You can test it using the same examples. (3 marks)</dd>
<dt>For a Meaningless Brownie Point</dt><dd>Using <b>only</b> Java's built-in concurrency primitives and monitor-like constructs, as well as an <code>ArrayDeque</code> of <code>Object</code>, implement a strong semaphore in <code>StrongSemaphore</code>. You may use <code>Object.notifyAll()</code> so long as the first process to <i>leave</i> its await is the first process in the queue.</dd>
</dl>

<p>
<i>Hint:</i> your solution probably shouldn't depend on a <code>Thread.yield()</code>
for correctness.  <code>Thread.yield()</code> is a hint to the scheduler that a thread is
willing to yield its scheduling slice.  There's no guarantee that the
scheduler will take the hint.
</p>
</div>
</div>
</div>