Eldarica
========

Eldarica is a model checker for Horn clauses, Numerical Transition
Systems, and software programs. Inputs can be read in a variety of
formats, including SMT-LIB 2 and Prolog for Horn clauses, and fragments of
Scala and C for software programs, and are analysed using a variant of the
Counterexample-Guided Abstraction
Refinement (CEGAR) method. Eldarica is fast and includes sophisticated
interpolation-based techniques for synthesising new predicates for
CEGAR, enabling it to solve a wide range of verification problems.

The Eldarica C parser accepts programs augmented with various primitives
from the timed automata world: supporting concurrency, clocks, communication
channels, as well as analysis of systems with an unbounded number of
processes (parameterised analysis).

There is also a variant of Eldarica for analysing Petri nets: http://www.philipp.ruemmer.org/eldarica-p.shtml

Eldarica has been developed by Hossein Hojjat and Philipp Ruemmer,
with further contributions by Zafer Esen, Filip Konecny, and Pavle Subotic.

There is a simple **web interface** to experiment with the C interface
of Eldarica:
http://logicrunch.it.uu.se:4096/~wv/eldarica

The latest **nightly build** is available from: http://logicrunch.it.uu.se:4096/~wv/eldarica/eldarica-bin-nightly.zip

Documentation
-------------

You can either download a binary release of Eldarica, or compile the Scala
code yourself. Since Eldarica uses <code>sbt</code>, compilation is quite
simple: you just need <code>sbt</code> installed on your machine,
and then type <code>sbt assembly</code> to download the compiler, all
required libraries, and produce a binary of Eldarica.

After compilation (or downloading a binary release), calling Eldarica
is normally as easy as saying

  <code>./eld regression-tests/horn-smt-lib/rate_limiter.c.nts.smt2</code>

When using a binary release, one can instead also call

  <code>java -jar target/scala-2.\*/Eldarica-assembly\*.jar regression-tests/horn-smt-lib/rate_limiter.c.nts.smt2</code>

A set of examples is provided on http://logicrunch.it.uu.se:4096/~wv/eldarica, and included
in the distributions directory <code>regression-tests</code>.

You can use the script <code>eld-client</code> instead of
<code>eld</code> in order to run Eldarica in a server-client mode,
which significantly speeds up processing of multiple problems.

A full list of options can be obtained by calling <code>./eld
-h</code>.<br> In particular, the options <code>-disj</code>,
<code>-abstract</code>, <code>-stac</code> can be used to control
predicate generation.

Papers
------

* The canonical Eldarica reference:
  "The Eldarica Horn Solver"
  http://uu.diva-portal.org/smash/get/diva2:1268767/FULLTEXT01.pdf
* An older tool paper covering, among others, Eldarica:
  "A Verification Toolkit for Numerical Transition Systems - Tool Paper."
  http://link.springer.com/chapter/10.1007%2F978-3-642-32759-9_21
* "Guiding Craig Interpolation with Domain-specific Abstractions"
  http://link.springer.com/article/10.1007%2Fs00236-015-0236-z
* "Accelerating Interpolants"
  http://link.springer.com/chapter/10.1007%2F978-3-642-33386-6_16
* "Disjunctive Interpolants for Horn-Clause Verification"
  http://link.springer.com/chapter/10.1007%2F978-3-642-39799-8_24
* "Exploring interpolants"
  http://dx.doi.org/10.1109/FMCAD.2013.6679393

Related Links
-------------

* A library of Horn clause benchmarks:
  https://github.com/sosy-lab/sv-benchmarks/tree/master/clauses
* Numerical transition system benchmarks:
  http://nts.imag.fr/index.php/Main_Page

