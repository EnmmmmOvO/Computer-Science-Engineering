<div id="content">
<h1 class="title">Homework (Week 2)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orga1d1ef8">1. No skip (4 marks)</a></li>
<li><a href="#orgde87e71">2. Dekker's Algorithm (8 marks)</a></li>
</ul>
</div>
</div>
<p>
<b>Submission</b>: Due on Friday, 17th of June, 11am Sydney Time. Please submit using the <a href="https://cgi.cse.unsw.edu.au/~give/Student/give.php">CSE Give System</a> either online or via this command on a CSE terminal:
</p>

<div class="org-src-container">
<pre class="src src-sh">give cs3151 hw2 hw2.pdf hw2.pml
</pre>
</div>

<p>
Late submissions are accepted up to five days after the deadline, but
at a penalty: 5% off your total mark per day.
</p>

<div id="outline-container-orga1d1ef8" class="outline-2">
<h2 id="orga1d1ef8"><span class="section-number-2">1</span> No skip (4 marks)</h2>
<div class="outline-text-2" id="text-1">
<p>
Consider the following trivial Promela model:
</p>

<div class="org-src-container">
<pre class="src src-promela"><span class="org-type">byte</span> <span class="org-variable-name">x</span> = <span class="org-constant">0</span>;

<span class="org-keyword">active</span> <span class="org-keyword">proctype</span> <span class="org-function-name">P</span>() {
  x = 1;
  x = 2;
  x = 3;
}

<span class="org-keyword">ltl</span> <span class="org-function-name">skip_2</span> { &lt;&gt;(x == 1 until x == 3) }
</pre>
</div>

<p>
Here we would be surprised if the value of <code>x</code> becomes <code>3</code>
immediately after being <code>1</code>. Yet Spin verifies that the
property <code>skip_2</code> holds.
</p>

<p>
Explain why this model nonetheless satisfies <code>skip_2</code>.  Also,
give an LTL formula that better captures the intent stated above.
</p>

<p>
Submit your answer in a PDF file called <code>hw2.pdf</code>.  Use of LaTeX is
encouraged but not required. Please make your answers as <b>concise as
possible</b>
</p>

<p>
<i>Hint:</i> the issue is to do with the semantics of LTL; it's not about
any implementation detail of Spin. You can work out the answer without
ever running Spin at all.
</p>
</div>
</div>

<div id="outline-container-orgde87e71" class="outline-2">
<h2 id="orgde87e71"><span class="section-number-2">2</span> Dekker's Algorithm (8 marks)</h2>
<div class="outline-text-2" id="text-2">
<p>
Dekker's algorithm (aka attempt 5 from the lectures) was presented
with two processes.
But does the algorithm work for three or more processes?
</p>

<ol class="org-ol">
<li>Write a Promela model for Dekker's algorithm with three processes.
Use the same general idea for the pre- and post-protocol
with <code>wantX</code> variables and a <code>turn</code> counter (you'll need three
<code>wantX</code>:s and three distinct <code>turn</code> values). Make sure your
Promela model obeys the limited critical reference
restriction.</li>
<li>Use Spin to check if your generalisation of Dekker's algorithm
satisfies mutual exclusion and eventual entry.
Include the LTL properties you used in your Promela file,
along with <code>/* comments */</code> explaining what verification
options you used and what the result was.</li>
</ol>

<p>
Submit your answer in a Promela file called <code>hw2.pml</code>
</p>

<p>
<i>Hint 1:</i> Feel free to assume that <a href="https:/www.cse.unsw.edu.au/~cs3151/22T2/statics/critical2.h">this Promela header file</a> is present
in the same directory as your .pml file, if you want to use the same
critical section boilerplate as in the lectures.
</p>

<p>
<i>Hint 2:</i> The limited critical reference restriction also applies to the
guards of <code>do</code> and <code>if</code> statements. In particular, the following does
<i>not</i> obey limited critical reference, because <code>wantp</code> and <code>wantq</code>
cannot be checked atomically.
</p>

<div class="org-src-container">
<pre class="src src-promela"><span class="org-keyword">do</span>
:: wantp -&gt; ...
:: wantq -&gt; ...
:: <span class="org-keyword">else</span>  -&gt; ...
<span class="org-keyword">od</span>
</pre>
</div>
</div>
</div>
</div>