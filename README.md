Eldarica
========

Eldarica is a model checker for Horn clauses, Numerical Transition
Systems, and Scala programs.  Inputs can be read in a variety of
formats, including SMT-LIB 2 and Prolog for Horn clauses, and are
analysed using a variant of the Counterexample-Guided Abstraction
Refinement (CEGAR) method. Eldarica is fast and includes sophisticated
interpolation-based techniques for synthesising new predicates for
CEGAR, enabling it to solve a wide range of verification problems.

Eldarica has been developed by Hossein Hojjat and Philipp Ruemmer,
with further contributions by Filip Konecny and Pavle Subotic.

Documentation
-------------

After compilation (or downloading a binary release), calling Eldarica
is normally as easy as saying

  <code>./eld regression-tests/horn-smt-lib/rate_limiter.c.nts.smt2</code>

You can use the script <code>eld-client</code> instead of
<code>eld</code> in order to run Eldarica in a server-client mode,
which significantly speeds up processing of multiple problems.

A full list of options can be obtained by calling <code>./eld
-h</code>.<br> In particular, the options <code>-disj</code>,
<code>-abstract</code>, <code>-stac</code> can be used to control
predicate generation.

Papers
------

* The canonical reference to Eldarica:
  "A Verification Toolkit for Numerical Transition Systems - Tool Paper."
  http://link.springer.com/chapter/10.1007%2F978-3-642-32759-9_21
* "Accelerating Interpolants"
  http://link.springer.com/chapter/10.1007%2F978-3-642-33386-6_16
* "Disjunctive Interpolants for Horn-Clause Verification"
  http://link.springer.com/chapter/10.1007%2F978-3-642-39799-8_24
* "Exploring interpolants"
  http://dx.doi.org/10.1109/FMCAD.2013.6679393

Related Links
-------------

* A library of Horn clause benchmarks:
  https://svn.sosy-lab.org/software/sv-benchmarks/trunk/clauses/LIA/Eldarica/
* Numerical transition system benchmarks:
  http://richmodels.epfl.ch/ntscomp/ntslib
