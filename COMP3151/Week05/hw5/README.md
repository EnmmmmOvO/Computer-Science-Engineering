<div id="content">
<h1 class="title">Homework (Week 5)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org72426ee">1. Reasoning about message passing (5 marks)</a></li>
<li><a href="#org9b81a69">2. Philosophers (4 marks)</a></li>
<li><a href="#org009b645">3. Fair Merge (4 marks)</a></li>
</ul>
</div>
</div>
<p>
<b>Submission</b>: Due on Friday, 15th of July, 11am Sydney Time. Please submit using the <a href="https://cgi.cse.unsw.edu.au/~give/Student/give.php">CSE Give System</a> either online or via this command on a CSE terminal:
</p>

<div class="org-src-container">
<pre class="src src-sh">give cs3151 hw5 hw5.pdf philosophers.pml merge.pml
</pre>
</div>

<p>
Late submissions are accepted up to five days after the deadline, but
at a penalty: 5% off your total mark per day.
</p>

<p>
Develop solutions to each of the following problems in Promela, in a separate Promela file.
</p>

<div id="outline-container-org72426ee" class="outline-2">
<h2 id="org72426ee"><span class="section-number-2">1</span> Reasoning about message passing (5 marks)</h2>
<div class="outline-text-2" id="text-1">
<p>
Here is a critical section algorithm that uses synchronous message passing:
</p>


<div class="figure">
<p><img src="DV_demand1.png" alt="hw5mutex.png">
</p>
</div>

<p>
Only processes <b>x</b> and <b>y</b> are competing for the critical section; <b>z</b> is an auxiliary process.
The critical sections are at lines <code>x2</code> and <code>y2</code>; <code>x_1</code> and <code>y_1</code> are the non-critical sections.
The program variables x,y,z are just dummies; their values and types are unimportant.
</p>

<p>
The transition diagrams for these processes are as follows.
</p>


<div class="figure">
<p><img src="DV_demand2.png" alt="hw5mutex2.png">
</p>
</div>

<p>
(The self-loop is not depicted in the code above; it represents the ability to stay in the non-critical section forever).
</p>

<ol class="org-ol">
<li>Construct the closed product of these transition diagrams.
The initial state will be <span class="MathJax_Preview" style="color: inherit; display: none;"></span><span class="MathJax" id="MathJax-Element-1-Frame" tabindex="0" data-mathml="<math xmlns=&quot;http://www.w3.org/1998/Math/MathML&quot;><mo fence=&quot;false&quot; stretchy=&quot;false&quot;>&amp;#x27E8;</mo><msub><mi>x</mi><mn>1</mn></msub><mo>,</mo><msub><mi>y</mi><mn>1</mn></msub><mo>,</mo><msub><mi>z</mi><mn>1</mn></msub><mo fence=&quot;false&quot; stretchy=&quot;false&quot;>&amp;#x27E9;</mo></math>" role="presentation" style="position: relative;"><nobr aria-hidden="true"><span class="math" id="MathJax-Span-1" style="width: 4.929em; display: inline-block;"><span style="display: inline-block; position: relative; width: 4.239em; height: 0px; font-size: 116%;"><span style="position: absolute; clip: rect(1.48em, 1004.14em, 2.663em, -999.998em); top: -2.313em; left: 0em;"><span class="mrow" id="MathJax-Span-2"><span class="mo" id="MathJax-Span-3" style="font-family: STIXGeneral-Regular;">⟨</span><span class="msubsup" id="MathJax-Span-4"><span style="display: inline-block; position: relative; width: 0.889em; height: 0px;"><span style="position: absolute; clip: rect(3.401em, 1000.45em, 4.14em, -999.998em); top: -3.988em; left: 0em;"><span class="mi" id="MathJax-Span-5" style="font-family: STIXGeneral-Italic;">x<span style="display: inline-block; overflow: hidden; height: 1px; width: 0.002em;"></span></span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span><span style="position: absolute; top: -3.84em; left: 0.446em;"><span class="mn" id="MathJax-Span-6" style="font-size: 70.7%; font-family: STIXGeneral-Regular;">1</span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span></span></span><span class="mo" id="MathJax-Span-7" style="font-family: STIXGeneral-Regular;">,</span><span class="msubsup" id="MathJax-Span-8" style="padding-left: 0.2em;"><span style="display: inline-block; position: relative; width: 0.889em; height: 0px;"><span style="position: absolute; clip: rect(3.401em, 1000.45em, 4.337em, -999.998em); top: -3.988em; left: 0em;"><span class="mi" id="MathJax-Span-9" style="font-family: STIXGeneral-Italic;">y</span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span><span style="position: absolute; top: -3.84em; left: 0.446em;"><span class="mn" id="MathJax-Span-10" style="font-size: 70.7%; font-family: STIXGeneral-Regular;">1</span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span></span></span><span class="mo" id="MathJax-Span-11" style="font-family: STIXGeneral-Regular;">,</span><span class="msubsup" id="MathJax-Span-12" style="padding-left: 0.2em;"><span style="display: inline-block; position: relative; width: 0.84em; height: 0px;"><span style="position: absolute; clip: rect(3.401em, 1000.4em, 4.239em, -999.998em); top: -3.988em; left: 0em;"><span class="mi" id="MathJax-Span-13" style="font-family: STIXGeneral-Italic;">z</span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span><span style="position: absolute; top: -3.84em; left: 0.397em;"><span class="mn" id="MathJax-Span-14" style="font-size: 70.7%; font-family: STIXGeneral-Regular;">1</span><span style="display: inline-block; width: 0px; height: 3.993em;"></span></span></span></span><span class="mo" id="MathJax-Span-15" style="font-family: STIXGeneral-Regular;">⟩</span></span><span style="display: inline-block; width: 0px; height: 2.318em;"></span></span></span><span style="display: inline-block; overflow: hidden; vertical-align: -0.283em; border-left: 0px solid; width: 0px; height: 1.203em;"></span></span></nobr><span class="MJX_Assistive_MathML" role="presentation"><math xmlns="http://www.w3.org/1998/Math/MathML"><mo fence="false" stretchy="false">⟨</mo><msub><mi>x</mi><mn>1</mn></msub><mo>,</mo><msub><mi>y</mi><mn>1</mn></msub><mo>,</mo><msub><mi>z</mi><mn>1</mn></msub><mo fence="false" stretchy="false">⟩</mo></math></span></span><script type="math/tex" id="MathJax-Element-1">\langle x_1, y_1, z_1 \rangle</script>.</li>
<li>It's obvious from inspection of the closed product that this
algorithm satisfies mutual exclusion. Why?</li>
<li>Does this algorithm satisfy eventual entry? Briefly motivate.</li>
<li>Does this algorithm still work if we flip all inputs to outputs,
and vice versa? Brifely motivate.</li>
<li>The algorithm behaves oddly if we make <b>ch</b> asynchronous.
Describe a scenario that (a) assumes an asynchronous, reliable channel;
(b) goes on forever in a cycle; and (c) takes transitions other than
the self-loops at <code>x1</code> and <code>y1</code> infinitely often; and (d)
never visits locations <code>x2</code> and <code>y2</code>.</li>
</ol>

<p>
Submit your answers in a pdf file called <code>hw5.pdf</code>.
</p>
</div>
</div>

<div id="outline-container-org9b81a69" class="outline-2">
<h2 id="org9b81a69"><span class="section-number-2">2</span> Philosophers (4 marks)</h2>
<div class="outline-text-2" id="text-2">
<p>
Develop a solution for the dining philosophers problem using only message passing, under the additional restriction that each channel must be connected to exactly one sender
and exactly one receiver. 
</p>

<p>
By way of a hint, the following things do not work:
</p>
<ul class="org-ul">
<li>Having only 5 processes, one for each philosopher.</li>
<li>Having only 5 channels, one for each fork.</li>
</ul>

<p>
Configure the solution to run forever, in a 5 philosopher scenario. 
</p>

<p>
Put all your work in a file called <code>philosophers.pml</code>. Do not include any other files.
</p>
</div>
</div>

<div id="outline-container-org009b645" class="outline-2">
<h2 id="org009b645"><span class="section-number-2">3</span> Fair Merge (4 marks)</h2>
<div class="outline-text-2" id="text-3">
<p>
Develop an algorithm to merge
two sequences of data. A process called <code>merge</code> is given three channel parameters of type <code>byte</code>, receives data on two input channels and interleaves the data
on the output channel, such that if the two inputs are sorted (in ascending order), then the output is sorted.
</p>

<p>
Try to implement a fair merge that is free from starvation of both input
channels when possible. This means that you should try to make sure every
input stream is always eventually read from.
This requirement will sometimes be impossible to reconcile with the
sortedness requirement.
If so, keeping the outputs sorted takes priority.
For example, if the two input channels transmit
infinite streams of 1:s and 2:s, respectively, no 2:s
should be sent on the output channel.
</p>

<p>
Assume that the value 255 is a special <code>EOF</code> signal, and no further data will
be sent on a channel after <code>EOF</code> is sent. Your merge process should terminate if all data
has been transmitted. Assume that an <code>EOF</code> will be sent at the end of the data stream
(if it ends).
</p>

<p>
Put all your work in a file called <code>merge.pml</code>. Do not include any other files.
</p>
</div>
</div>
</div>