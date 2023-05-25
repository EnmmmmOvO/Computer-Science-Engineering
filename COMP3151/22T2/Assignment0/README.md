<div id="content">
<h1 class="title">Spec (Warm-up Assignment)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orgfaa3cf8">1. Task</a></li>
<li><a href="#org214c2c4">2. Deliverables</a></li>
<li><a href="#orge1a3931">3. Testing</a></li>
<li><a href="#org507d38e">4. Submission Instructions</a></li>
</ul>
</div>
</div>
<p>
Start working on this assignment after the Week 1 lectures.
<i>You will need some Week 2 material to finish it</i>.
</p>

<p>
This assignment is worth 10% and due before <b>Monday June 20th, 6pm</b> local time
Sydney.
</p>

<p>
Late submissions are accepted up to five days after the deadline, but
at a penalty: 5% off your total mark per day.
</p>

<p>
The purpose of this assignment is to ensure that every student in this
course is familiar with the tools we will be using.
</p>

<p>
<i>This assignment has to be done individually</i>.
</p>

<p>
The task involving Spin is supposed to be relatively easy. Finding
the assertion network however can be hard. This component serves to
(a) re-inforce understanding of the Owicki/Gries method and (b)
provide a modest challenge.
</p>

<div id="outline-container-orgfaa3cf8" class="outline-2">
<h2 id="orgfaa3cf8"><span class="section-number-2">1</span> Task</h2>
<div class="outline-text-2" id="text-1">
<p>
Consider the following algorithm presented in Ben-Ari's notation.
</p>


<div class="figure">
<p><img src="DV_demand.png" alt="algorithmy.png">
</p>
</div>

<ol class="org-ol">
<li><i>(40 marks)</i> Use Spin to check whether Algorithm Y is a solution to the
critical section problem.
Address all four desiderata from the lectures
(mutual exclusion, eventual entry, absence of deadlock,
 absence of unnecessary delay).</li>
<li><i>(40 marks)</i> Encode Algorithm Y as a parallel composition of two transition
diagrams. Define an assertion network <span class="MathJax_Preview" style="color: inherit; display: none;"></span><span class="MathJax" id="MathJax-Element-1-Frame" tabindex="0" data-mathml="<math xmlns=&quot;http://www.w3.org/1998/Math/MathML&quot;><mi>Q</mi></math>" role="presentation" style="position: relative;"><nobr aria-hidden="true"><span class="math" id="MathJax-Span-1" style="width: 0.889em; display: inline-block;"><span style="display: inline-block; position: relative; width: 0.741em; height: 0px; font-size: 116%;"><span style="position: absolute; clip: rect(1.48em, 1000.74em, 2.663em, -999.998em); top: -2.313em; left: 0em;"><span class="mrow" id="MathJax-Span-2"><span class="mi" id="MathJax-Span-3" style="font-family: STIXGeneral-Italic;">Q</span></span><span style="display: inline-block; width: 0px; height: 2.318em;"></span></span></span><span style="display: inline-block; overflow: hidden; vertical-align: -0.283em; border-left: 0px solid; width: 0px; height: 1.089em;"></span></span></nobr><span class="MJX_Assistive_MathML" role="presentation"><math xmlns="http://www.w3.org/1998/Math/MathML"><mi>Q</mi></math></span></span><script type="math/tex" id="MathJax-Element-1">Q</script> such that the assertions
at the locations representing the critical sections express mutual
exclusion. Prove that <span class="MathJax_Preview" style="color: inherit; display: none;"></span><span class="MathJax" id="MathJax-Element-2-Frame" tabindex="0" data-mathml="<math xmlns=&quot;http://www.w3.org/1998/Math/MathML&quot;><mi>Q</mi></math>" role="presentation" style="position: relative;"><nobr aria-hidden="true"><span class="math" id="MathJax-Span-4" style="width: 0.889em; display: inline-block;"><span style="display: inline-block; position: relative; width: 0.741em; height: 0px; font-size: 116%;"><span style="position: absolute; clip: rect(1.48em, 1000.74em, 2.663em, -999.998em); top: -2.313em; left: 0em;"><span class="mrow" id="MathJax-Span-5"><span class="mi" id="MathJax-Span-6" style="font-family: STIXGeneral-Italic;">Q</span></span><span style="display: inline-block; width: 0px; height: 2.318em;"></span></span></span><span style="display: inline-block; overflow: hidden; vertical-align: -0.283em; border-left: 0px solid; width: 0px; height: 1.089em;"></span></span></nobr><span class="MJX_Assistive_MathML" role="presentation"><math xmlns="http://www.w3.org/1998/Math/MathML"><mi>Q</mi></math></span></span><script type="math/tex" id="MathJax-Element-2">Q</script> is inductive. (It is ok to focus on the
processes after the initialisation of <span class="MathJax_Preview" style="color: inherit; display: none;"></span><span class="MathJax" id="MathJax-Element-3-Frame" tabindex="0" data-mathml="<math xmlns=&quot;http://www.w3.org/1998/Math/MathML&quot;><mi>b</mi></math>" role="presentation" style="position: relative;"><nobr aria-hidden="true"><span class="math" id="MathJax-Span-7" style="width: 0.594em; display: inline-block;"><span style="display: inline-block; position: relative; width: 0.495em; height: 0px; font-size: 116%;"><span style="position: absolute; clip: rect(1.48em, 1000.45em, 2.466em, -999.998em); top: -2.313em; left: 0em;"><span class="mrow" id="MathJax-Span-8"><span class="mi" id="MathJax-Span-9" style="font-family: STIXGeneral-Italic;">b</span></span><span style="display: inline-block; width: 0px; height: 2.318em;"></span></span></span><span style="display: inline-block; overflow: hidden; vertical-align: -0.054em; border-left: 0px solid; width: 0px; height: 0.917em;"></span></span></nobr><span class="MJX_Assistive_MathML" role="presentation"><math xmlns="http://www.w3.org/1998/Math/MathML"><mi>b</mi></math></span></span><script type="math/tex" id="MathJax-Element-3">b</script>. It is not ok to make the
assertions at the entry locations unreasonably strong.)</li>
<li><i>(20 marks)</i> Identify any superfluous statements in the algorithm. That is,
can any statements be replaced by <code>skip</code> without changing the
behaviour of Algorithm Y? Justify your answers, preferrably
using your transition diagram and assertion network.</li>
</ol>

<p>
Prepare a report that explains your findings. Make it concise and
convincing.
</p>
</div>
</div>

<div id="outline-container-org214c2c4" class="outline-2">
<h2 id="org214c2c4"><span class="section-number-2">2</span> Deliverables</h2>
<div class="outline-text-2" id="text-2">
<dl class="org-dl">
<dt>algY.pml</dt><dd>faithful implementations of Algorithm Y in Promela.
Feel free to assume that <a href="https:/www.cse.unsw.edu.au/~cs3151/22T2/statics/critical2.h">this Promela header file</a> is
present in the same directory as your .pml file, if you
want to use the same critical section boilerplate as in
the lectures.</dd>
<dt>algY.pdf</dt><dd>A PDF of your report. Diagrams may be hand-drawn (but
must be readable). Prose must be typeset, preferably
with LaTeX (although not mandatory).  List your student
ID near the top of the document.  The document should
describe your efforts, incorporate the previous
deliverables, quote some output of Spin as evidence if
that is helpful, and contain the Owicki/Gries-style
proof.
Make sure your Spin results are reproducible by
specifying which (if any) non-default options you used
for checking each property.</dd>
</dl>
</div>
</div>

<div id="outline-container-orge1a3931" class="outline-2">
<h2 id="orge1a3931"><span class="section-number-2">3</span> Testing</h2>
<div class="outline-text-2" id="text-3">
<p>
Submissions will be tested on CSE servers, where Spin's command line
interface is available. A compatible version of the ispin GUI is
accessible for vlab users with this command:
</p>

<div class="org-src-container">
<pre class="src src-sh">% ~cs3151/bin/ispin
</pre>
</div>

<p>
…and can be used remotely over SSH as follows:
</p>

<div class="org-src-container">
<pre class="src src-sh">% ssh -Y z&lt;my_digits&gt;@login.cse.unsw.edu.au ~cs3151/bin/ispin
</pre>
</div>

<p>
You may also wish to install Spin locally. Instructions here:
<a href="http://spinroot.com">http://spinroot.com</a>
</p>
</div>
</div>

<div id="outline-container-org507d38e" class="outline-2">
<h2 id="org507d38e"><span class="section-number-2">4</span> Submission Instructions</h2>
<div class="outline-text-2" id="text-4">
<p>
The <code>give</code> command to be run is:
</p>
<div class="org-src-container">
<pre class="src src-sh">% give cs3151 assn0 algY.pml algY.pdf
</pre>
</div>
<p>
You may also use the online <code>give</code> interface to submit. 
Beware of rather tight submission size limits. 
</p>
</div>
</div>
</div>