/**
 * Copyright (c) 2011-2019 Philipp Ruemmer and Pavle Subotic.
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.bottomup

import lazabs.horn.abstractions.{AbsLattice, TermSubsetLattice, ProductLattice,
                                 TermExtendingLattice, MUXSearcher,
                                 TermIneqLattice, PredicateLattice,
                                 AbstractionRecord}
import AbstractionRecord.AbstractionMap

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.TheoryCollector
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience, Term, OneTerm, Formula}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.equations.ReduceWithEqs
import ap.terfor.substitutions.{ConstantSubst, VariableSubst}
import ap.proof.{ModelSearchProver, QuantifierElimProver}
import ap.util.Seqs
import ap.util.Timeout

import lazabs.prover.{Tree, Leaf}
import Util._
import DisjInterpolator._

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashMap, LinkedHashSet, ArrayBuffer}
import ap.SimpleAPI
import SimpleAPI.{ProverStatus, TimeoutException}


object TemplateInterpolator {

  import HornPredAbs._
  import TerForConvenience._

  //////////////////////////////////////////////////////////////////////////////

  def interpolatingPredicateGenCEXAbsUpp(absMap : Map[String, AbsLattice])
                                        (clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] =
    DagInterpolator.cexGuidedExpansion(DagInterpolator.stripOrNodes(clauseDag)) match {
      case Left(partialTree) => {
        // let's try some abstraction ...
        createAbstractConstraintTreesUpp(partialTree, absMap) match {
          case Some((vocabularyTree, constraintTrees)) => {
            val allPredMaps =
              for ((constrTree, order) <- constraintTrees) yield {
                DagInterpolator.callInterpolator(partialTree, constrTree, vocabularyTree, order) match {
                  case Left(preds) => preds.toMap
                  case Right(_) => throw new UnsupportedOperationException
                }
              }
            val allRelSyms =
              (for (m <- allPredMaps.iterator; p <- m.keysIterator) yield p).toSet

            Left(for (p <- allRelSyms.toSeq) yield (
                   p, (for (m <- allPredMaps.iterator;
                            c <- m.getOrElse(p, Seq()).iterator) yield c).toSet.toSeq))
          }
          case None =>
            DagInterpolator.partialPredicateGen(partialTree, false) match {
              case Left(preds) =>
                Left(preds)
              case _ => { assert(false); null }
            }
        }
      }
      case Right(cex) =>
        Right(cex)
    }


  //////////////////////////////////////////////////////////////////////////////

  def interpolatingPredicateGenCEXAbsGen(absMap : AbstractionMap, timeout : Long) =
    abstractInterpolatingPredicateGen(x => createAbstractConstraintTreesGen(x, absMap, timeout),
                                      true) _

  private def abstractInterpolatingPredicateGen(
                constraintGen : Tree[Either[NormClause, RelationSymbol]] =>
                                Option[(Tree[Seq[ConstantTerm]],
                                        Seq[(Tree[Conjunction], TermOrder)])],
                alwaysAddOrdinaryInterpolants : Boolean)
                (clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] =
    DagInterpolator.cexGuidedExpansion(DagInterpolator.stripOrNodes(clauseDag)) match {
      case Left(partialTree) => {
        // let's try some abstraction ...
        val abstractPreds =
          constraintGen(partialTree) match {
            case Some((vocabularyTree, constraintTrees)) => {
                for ((constrTree, order) <- constraintTrees) yield {
                  DagInterpolator.callInterpolator(partialTree, constrTree,
                                                   vocabularyTree, order) match {
                    case Left(preds) => preds
                    case Right(_) => throw new UnsupportedOperationException
                  }
                }
            }
            case None =>
              List()
          }

        val allPreds =
          if (alwaysAddOrdinaryInterpolants || abstractPreds.isEmpty) {
            // also compute normal interpolants
            val Left(basicPreds) = DagInterpolator.partialPredicateGen(partialTree, false)
            basicPreds :: abstractPreds.toList
          } else {
            abstractPreds
          }

        val allPredMaps = allPreds map (_.toMap)

        val allRelSyms = new LinkedHashSet[Predicate]
        for (m <- allPreds)
          for ((p, _) <- m)
            allRelSyms += p

        Left(for (p <- allRelSyms.toSeq) yield (
               p, (for (m <- allPredMaps;
                        c <- m.getOrElse(p, Seq())) yield c).distinct))
      }
      case Right(cex) =>
        Right(cex)
    }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generate predicates using template-based tree interpolation
   */
  def interpolatingPredicateGenCEXAbs(clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] =
    DagInterpolator.cexGuidedExpansion(DagInterpolator.stripOrNodes(clauseDag)) match {
      case Left(partialTree) => {
        // let's try some abstraction ...
        createAbstractConstraintTrees(partialTree) match {
          case Some((vocabularyTree, constraintTrees)) => {
/*            val (constrTree, order) = constraintTrees.head // Note we are just taking the head
            DagInterpolator.callInterpolator(partialTree, constrTree, vocabularyTree, order) match {
              case Left(preds) =>
                Left(preds)
            } */

            val allPredMaps =
              for ((constrTree, order) <- constraintTrees) yield {
                DagInterpolator.callInterpolator(partialTree, constrTree, vocabularyTree, order) match {
                  case Left(preds) => preds.toMap
                  case Right(_) => throw new UnsupportedOperationException
                }
              }
            val allRelSyms =
              (for (m <- allPredMaps.iterator; p <- m.keysIterator) yield p).toSet

            Left(for (p <- allRelSyms.toSeq) yield (
                   p, (for (m <- allPredMaps.iterator;
                            c <- m.getOrElse(p, Seq()).iterator) yield c).toSet.toSeq))
          }
          case None =>
            DagInterpolator.partialPredicateGen(partialTree, false) match {
              case Left(preds) =>
                Left(preds)
              case _ => { assert(false); null }
            }
        }
      }
      case Right(cex) =>
        Right(cex)
    }


  //////////////////////////////////////////////////////////////////////////////

  object ExplorationResult extends Enumeration {
    val Timeout, Bottom, Normal = Value
  }  

  def exploreLattice(clauseTree : Tree[Either[NormClause, RelationSymbol]],
                     decompositions : Seq[(List[Int], AbsLattice)],
                     timeout : Long)
                    : ((Tree[Seq[ConstantTerm]],
                             Seq[(Tree[Conjunction], TermOrder)]),
                       ExplorationResult.Value) =
    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      import p._

      val coll = new TheoryCollector

      val (decompositionPoints, relAbstractions) = decompositions.unzip
 
      val decPointVocabulary =
        new MHashMap[List[Int], (Seq[ConstantTerm], Seq[ConstantTerm], Seq[ConstantTerm])]

      val vocabularyTree = {
        var symNum = 0

        def vocHelp(path : List[Int],
                    t : Tree[Either[NormClause, RelationSymbol]])
                   : Tree[Either[Seq[ConstantTerm],
                                 (Seq[ConstantTerm], Seq[ConstantTerm], Seq[ConstantTerm])]] = {
        val Tree(c, children) = t
        val vocSyms = c match {
            case Left(NormClause(_, _, (rs, _))) if (decompositionPoints contains path) => {
              // Need three copies of the symbols
              val voc = (createConstantsRaw(rs.name + "_" + symNum + "_a_", 0 until rs.arity),
                         createConstantsRaw(rs.name + "_" + symNum + "_", 0 until rs.arity),
                         createConstantsRaw(rs.name + "_" + symNum + "_b_", 0 until rs.arity))
              decPointVocabulary.put(path, voc)
              Right(voc)
            }
            case Left(NormClause(_, _, (rs, _))) =>
              Left(createConstantsRaw(rs.name + "_" + symNum + "_", 0 until rs.arity))
            case Right(rs) =>
              Left(createConstantsRaw(rs.name + "_" + symNum + "_", 0 until rs.arity))
          }
          symNum = symNum + 1
          Tree(vocSyms,
             for ((c, i) <- children.zipWithIndex) yield vocHelp(i :: path, c))
        }
        vocHelp(List(), clauseTree)
      }
    
      val rawConstraintTree =
        for (p <- clauseTree zip vocabularyTree.subtrees;
             (maybeClause, Tree(rsSyms, subVocTrees)) = p) yield
          maybeClause match {
            case Left(clause) => {
              val newLocalSyms =
                createConstantsRaw("local", 0 until clause.localSymbols.size)
              val newHeadSyms = rsSyms match {
                case Left(syms) => syms
                case Right((_, _, syms)) => syms
              }
              val newBodySymbols = for (Tree(syms, _) <- subVocTrees) yield syms match {
                case Left(syms) => syms
                case Right((syms, _, _)) => syms
              }

              clause collectTheories coll
              addTheories(coll.newTheories)
              coll.reset

              val constraint = clause.substituteSyms(newLocalSyms, newHeadSyms, newBodySymbols)(order)
              addAssertion(constraint)
              constraint
            }
            case Right(_) => Conjunction.TRUE
          }

      // Construct the abstraction lattice

      val rawAbstraction = (for ((path, abs) <- decompositions) yield {
        val (_, x_const, _) = decPointVocabulary(path)
        abs.asInstanceOf[AbsLattice]
      }) reduceLeft (ProductLattice(_, _))

      val abstraction = rawAbstraction //.reducedLattice

      // Find minimal feasible abstractions

      //println("abstraction: ")
      //println(abstraction)

      val (xa_vocs, x_vocs, xb_vocs) = (for (path <- decompositionPoints) yield {
        val (xa_consts, x_consts, xb_consts) = decPointVocabulary(path)
        import IExpression._
        (xa_consts map (i(_)), x_consts map (i(_)), xb_consts map (i(_)))
      }).unzip3

      val feasibleAbstractions = abstraction.lSearch(obj => scope {
        Timeout.unfinished {
          for (a <- abstraction.asRelation(obj, xa_vocs, xb_vocs))
            !! (a)
          checkSat(false)
          while (getStatus(100) == ProverStatus.Running)
            Timeout.check
          ??? == ProverStatus.Unsat 
        } {
          case x : Any => {
            stop
            x
          }
        }
      },
      timeout
      ).toList

      // Demo of printing costs
      //val costs = for(f <- feasibleAbstractions) yield {
      //  val c = abstraction.getObjectCost(f)
      //  println("Cost: " + f + " -> " + c)
      //}

      // build the constraint tree for the discovered feasible abstractions
      // (this has to be generalised when simultaneously applying abstractions
      // at multiple points)

      // NOTE: Added a filter of to use costs, remove if not using costs
      val constraintTrees = for (obj <- feasibleAbstractions) yield {
        val rels = abstraction.asRelation(obj, xa_vocs, x_vocs, xb_vocs)

        val relMap =
          (for ((path, (lr, rr)) <- decompositionPoints.iterator zip rels.iterator) yield {
             (decPointVocabulary(path)._2.head,
              (!asConjunction(~lr), !asConjunction(~rr)))
           }).toMap

        val relTree = for (v <- vocabularyTree) yield v match {
          case Left(_) => (Conjunction.TRUE, Conjunction.TRUE)
          case Right((_, Seq(x, _*), _)) => relMap(x)
        }

        for (p <- rawConstraintTree zip relTree.subtrees;
             (rawConstraint, Tree((_, headRel), subRelTrees)) = p) yield {
          implicit val o = order
          val bodyRels = for (Tree((leftRel, _), _) <- subRelTrees) yield 
            leftRel
          conj(List(rawConstraint, headRel) ++ bodyRels)
        }
      }

      ((for (t <- vocabularyTree) yield t match {
         case Left(x) => x
         case Right((_, x, _)) => x
       },
       for (ct <- constraintTrees) yield (ct, order)),
       feasibleAbstractions match {
         case List(x) if (x == abstraction.bottom) => ExplorationResult.Bottom
         case List()                               => ExplorationResult.Timeout
         case _                                    => ExplorationResult.Normal
       })
    }


  //////////////////////////////////////////////////////////////////////////////

  private def getModVars(path : List[Int], newClauses : List[NormClause]) : Seq[Int] = {
    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      import p._

      // First clause
      val hc = newClauses.head

      var lastHeadSyms = Seq() : Seq[ConstantTerm]
      implicit val order1 = order
    
      val initc = newClauses.head
      //println("initc is")
      //println(initc)

      val initBodySyms = for ((syms, j) <- initc.bodySyms.reverse.zipWithIndex) yield createConstantsRaw("bs_0_" + j + "_", 0 until syms.size)
      val initLocalSyms = createConstantsRaw("ls", 0 until initc.localSymbols.size)
      val initHeadSyms = createConstantsRaw("hs", 0 until initc.headSyms.size)

      //println("local Syms: = " + initLocalSyms)
      //println("body Syms: = " + initBodySyms)
      //println("head Syms: = " + initHeadSyms)
      //println("printing path")
      //println(newClauses)
      //println(path)

      // Causing problems
      val modClause = (initc.substituteSyms(initLocalSyms, initHeadSyms, initBodySyms)(order))
      addAssertion (modClause)

      //println("mod clause is ")
      //println(modClause)
      assert(path.size > 0)
      lastHeadSyms = initBodySyms.reverse(path.head) // select right predicate in body

      // Final clauses

      //println("NEW CLAUSES TAIL : " + newClauses.tail )
      //println("PATH TAIL : " + path.tail )


      for (((c, p), i) <- newClauses.tail.zip(path.tail).zipWithIndex) {
        //println("!!!!new Clause is :")
        //println(c)
        val newBodySyms = for ((syms,j) <- c.bodySyms.zipWithIndex) yield {
          //println("syms = " + syms)
          createConstantsRaw("bs_" + (i+1) + "_" + j + "_", 0 until syms.size)
        }

        val newLocalSyms = createConstantsRaw("ls", 0 until c.localSymbols.size)

        //println("new body syms = " + newBodySyms.reverse)
       // println("new local syms = " + newLocalSyms)
       // println("order is " + order)
        val modClause = (c.substituteSyms(newLocalSyms, lastHeadSyms, newBodySyms)(order))

        addAssertion (modClause)
        //println("p is = " + p + " new bod sym size is " + newBodySyms.size)
        //println("p is = " + p + " new bod sym " + newBodySyms)
        lastHeadSyms = newBodySyms(p) // select
      }

      val lHIndex = lastHeadSyms.zip(0 until lastHeadSyms.size)
      val eqList = lHIndex.zip(initHeadSyms).filter{ case ((c, i), d) =>
        scope {
          ?? (IConstant(c) === IConstant(d))
          (! (??? == ProverStatus.Valid))
        }
      }

      eqList.unzip._1.unzip._2 // return indecies

    }
  }


  // returns loop paths 
  private def getPath(clauseTree : Tree[Either[NormClause, RelationSymbol]]) : Seq[(List[Int], List[RelationSymbol])] =
  {
    def search(path : List[Int], ids : List[RelationSymbol], 
      t : Tree[Either[NormClause, RelationSymbol]]) : Seq[(List[Int], List[RelationSymbol])] = t match {

      case Tree(Left(NormClause(constr, body, (rel, _))), children) =>

        if (ids.contains(rel)){
          //println("!Cutting : " + rel + " in path : " + ids)
          val fcut = (path, rel::ids)
          assert(path.size == ids.size)
          //val fcut = (path, ids)
          //println("fcut is  " + fcut)
          //println(children)

          val subres = for ((c, i) <- children.zipWithIndex; 
                            res <- search(i :: path, rel :: ids, c)) yield res

          if (!subres.isEmpty){
             val hd = (fcut)
             val bd = subres
//             println("subres = " + subres)
             val fin = Seq(hd) ++ bd
             fin
          }
          else{
            Seq(fcut)
          }

        }
        else{           
//          println("Child size is " + children.size)
          val subres = for ((c, i) <- children.zipWithIndex; 
          res <- search(i :: path, rel :: ids, c)) yield res

          if (!subres.isEmpty){
              subres
          }
          else{
            Seq()
          } 
        }
      case Tree(_, children) => {
//        println("Child size is'' " + children.size)
//        val subres = for ((c, i) <- children.iterator.zipWithIndex;
//                          res <- search(i :: path, ids, c).iterator) yield res
//        if (subres.hasNext)
//          Seq(subres.next)
//        else
          Seq()
      }
    }

    val retv = search(List(), List(), clauseTree)   
    //println("returning from search " + retv + " it has sizei " + retv.size)
    retv
  }

  private def getModVarIndex(decompositionPoint : List[Int], idPath : List[RelationSymbol], 
    clauseTree : Tree[Either[NormClause, RelationSymbol]] ) : (List[NormClause], List[Int]) = {

    def cutPoint(ids : List[RelationSymbol]) : (Int, Int) = {

      val duplicates = ids.diff(ids.distinct)
      assert(!ids.isEmpty && !duplicates.isEmpty)
      //println("Duplicates are : " + duplicates)
      //println("Taking Duplicate : " + duplicates.head)

      val sIndex = ids.indexOf(duplicates.head)
      val lIndex = ids.lastIndexOf(duplicates.head)
      assert(ids(sIndex) == duplicates.head &&
             ids(lIndex) == duplicates.head)

      (sIndex, lIndex+1) 
    }

    // Get a list of clauses following the path
    def getNewClauses(path : List[Int], t : Tree[Either[NormClause, RelationSymbol]], ids : List[RelationSymbol],
      clauses : List[NormClause] ) : List[NormClause] =
    {
      if(path.isEmpty)
         clauses
      else{
        val p = path.head
        val (clauses2, children) = t match{ 
          case Tree(Left(cl@NormClause(constr, body, (rel, _))), children) =>
            if (ids.contains(rel)){
              //println("cycle = ids contains: " + rel )
              (cl::clauses, children)
            }             
            else{
              (clauses, children)
            }
          case Tree(_, children) => 
            (clauses, children)
        }

        //println("path p is " + p + " children size is " + children.size)
        assert(p < children.size)
        getNewClauses(path.tail, children(p), ids, clauses2)
      }
    }

    //println("In get mod var index ")
    //println("Path is : " + decompositionPoint)
    //println("Ids is : " + idPath)
    //println("Clause Tree is : " + clauseTree)
     
    // Check to see if we have a cycle
    //idPath.tail.contains(idPath.head) FIX!!
    val hasCut = idPath.distinct.size != idPath.size

    if (idPath.size > 0 && hasCut){
    //println("Found cut !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" )
      val (ind1, ind2) = cutPoint(idPath)
      //println("cut is at : " + ind1 + ", " + ind2 + " Slice is " + idPath.slice(ind1, ind2))
      //println("decomposition point is " + decompositionPoint)
 
      val newClauses = getNewClauses(decompositionPoint, clauseTree, idPath.slice(ind1, ind2), List()).reverse
 
      //println("New Clauses are " + newClauses)

      // new Clauses is already sliced  DO NIT SLICE!!
      val slicedClauses = newClauses

      //println("Sliced clauses" + slicedClauses)

      val slicedPath = decompositionPoint.slice(ind1, ind2)
      //assert(slicedPath.size == newClauses.size)

      //println("Sliced Path " + slicedPath)

      val modVars = getModVars(slicedPath, newClauses).toList

      (slicedClauses, modVars)
    }
    else{
      (List(), List())
    }
  }

  private def buildOctagonAbstraction(modVars : List[Int], arity : Int) : AbsLattice = {
    val modInds = for( l <- modVars.combinations(2).toList) yield (l(0), l(1))
    //println("Size of xa, x, xb : " + xa.size + " -- " + " mod inds size is " + modInds.size + " mod ins = " + modInds )
    
    val abslst1 = (for (i <- 0 until arity) yield (IExpression.v(i) -> 10))
    val abslst2 = (for ((i,j) <- modInds) yield (IExpression.v(i) - IExpression.v(j) -> 1))
    val abslst3 = (for ((i,j) <- modInds) yield (IExpression.v(i) + IExpression.v(j) -> 2)) toMap

    //println ("Abstraction is (list 1 size is ) = " + abslst1.size + "list 2 size is = " + abslst2.size )
    //println(for (i <- abslst1 ++ abslst2 ++ abslst3) yield i) 
    val terms = abslst1 ++ abslst2 ++ abslst3
//    println("Abstraction templates: " + terms)
   // TermExtendingLattice(
     TermSubsetLattice(terms.unzip._1, terms.toMap)
    //)
  }

  private def buildZoneAbstraction( 
       vocabularyTree : Tree[Either[Seq[ConstantTerm], (Seq[ConstantTerm], Seq[ConstantTerm], Seq[ConstantTerm])]], 
       modVars : List[Int],
       xa : Seq[ITerm],
       x : Seq[ITerm],
       xb : Seq[ITerm]) : AbsLattice = {
 
    val modInds = for( l <- modVars.combinations(2).toList) yield (l(0), l(1))
    //println("Size of xa, x, xb : " + xa.size + " -- " + " mod inds size is " + modInds.size + " mod ins = " + modInds )
    
    val abslst1 = (for (i <- 0 until x.size) yield (IExpression.v(i) -> 10))
    val abslst2 = (for ((i,j) <- modInds) yield ((IExpression.v(i) - IExpression.v(j)) -> 1))

    //println ("Abstraction is (list 1 size is ) = " + abslst1.size + "list 2 size is = " + abslst2.size )
    //println(for (i <- abslst1 ++ abslst2) yield i) 
    val terms = abslst1 ++ abslst2

    TermSubsetLattice(terms.unzip._1, terms.toMap)
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * TODO: merge with the normal function for this!
   */
  private def createAbstractConstraintTreesUpp(
                 clauseTree : Tree[Either[NormClause, RelationSymbol]],
                 absMap : Map[String, AbsLattice]
               )
                    : Option[(Tree[Seq[ConstantTerm]],
                              Seq[(Tree[Conjunction], TermOrder)])] = {


    def firstOccurrences(path : List[Int], ids : Set[RelationSymbol],
      t : Tree[Either[NormClause, RelationSymbol]]) : Seq[(List[Int], AbsLattice)] = t match {

      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex; 
                          res <- firstOccurrences(i :: path, ids + rel,  c)) yield res

        if ( /* !ids.contains(rel) && */ rel.arity > 0) {
          //println("!!!!!!!!!!!!!!!!rel is " + rel)
          //println("ids is " + ids)
          val relAbs = absMap.get(rel.name)

          //println("adding rel" + rel)
          //println("new ids id " + rel::ids)

          relAbs match {
            case Some(x) => List((path, x)) ++ subres
            case None => subres
          }
        } else {
          subres
        }
      }
      case Tree(_, children) =>
        Seq() 
    }

    def firstN(stepsLeft : Int,
               path : List[Int],
               t : Tree[Either[NormClause, RelationSymbol]])
              : List[(List[Int], AbsLattice)] =
      if (stepsLeft == 0)
        List()
      else t match {
        case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
          val subres = for ((c, i) <- children.zipWithIndex; 
                            res <- firstN(stepsLeft - 1, i :: path, c)) yield res
          (absMap get rel.name) match {
            case Some(lat) => List((path, lat)) ++ subres
            case _ => subres
          }
        }
        case _ =>
          List()
      }

   def lastOccurrences(path : List[Int],
                        t : Tree[Either[NormClause, RelationSymbol]])
                       : (List[(List[Int], AbsLattice)], Set[RelationSymbol]) = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val (subpaths, subsets) =
          (for ((c, i) <- children.zipWithIndex)
                yield lastOccurrences(i :: path, c)).unzip
        val flatSubpaths = for (s <- subpaths; p <- s) yield p
        val subOccurrences = (for (s <- subsets; rs <- s) yield rs).toSet
        (absMap get rel.name) match {
          case Some(lat) if (!(subOccurrences contains rel)) =>
            (List((path, lat)) ++ flatSubpaths, subOccurrences + rel)
          case _ =>
            (flatSubpaths, subOccurrences)
        }
      }
      case Tree(_, children) =>
        (List(), Set())
    }

    def getLongestPath(path : List[Int],
                       t : Tree[Either[NormClause, RelationSymbol]])
                      : List[(List[Int], AbsLattice)] = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex)
                     yield getLongestPath(i :: path, c)
        val maxSubPath : List[(List[Int], AbsLattice)] =
          if (subres.isEmpty) List() else (subres maxBy { x => x.size })
        (absMap get rel.name) match {
          case Some(lat) => List((path, lat)) ++ maxSubPath
          case None => maxSubPath
        }
      }
      case _ =>
        List()
    }

    def getLeafPaths(path : List[Int],
                     t : Tree[Either[NormClause, RelationSymbol]])
                    : List[(List[Int], AbsLattice)] = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex; 
                          res <- getLeafPaths(i :: path, c)) yield res
        (absMap get rel.name) match {
          case Some(lat) if (subres.size < 3) => List((path, lat)) ++ subres
          case _ => subres
        }
      }
      case _ =>
        List()
    }

    val maxProdSize = 5

//    clauseTree.prettyPrint
//    println("path is " + pathInfo)

    val (decompositionPoints, relAbstractions) =
//      firstOccurrences(List(), Set(), clauseTree).take(maxProdSize).unzip
      firstN(5, List(), clauseTree).take(maxProdSize).unzip
//      (firstN(3, List(), clauseTree).take(maxProdSize / 2) ++
//       getLeafPaths(List(), clauseTree).take(maxProdSize / 2)).toMap.toList.unzip

    if (decompositionPoints.isEmpty)
      return None

/*    val pathAbstractions = getLeafPaths(List(), clauseTree)
    println(pathAbstractions)

    val (decompositionPoints, relAbstractions) =
      if (pathAbstractions.size <= maxProdSize)
        pathAbstractions.unzip
      else
        (for (i <- 0 until maxProdSize)
         yield pathAbstractions((i * pathAbstractions.size) / maxProdSize)).unzip */

    println(decompositionPoints)

    Some(exploreLattice(clauseTree, decompositionPoints zip relAbstractions, 2000)._1)
  }


  //////////////////////////////////////////////////////////////////////////////


  private def createAbstractConstraintTreesGen(
                clauseTree : Tree[Either[NormClause, RelationSymbol]],
                absMap : AbstractionMap,
                timeout : Long
              )
              : Option[(Tree[Seq[ConstantTerm]],
                        Seq[(Tree[Conjunction], TermOrder)])] = {

/*    (for (c <- clauseTree) yield c match {
      case Left(NormClause(_, _, (rel, _))) => rel.pred.name
      case _ => "X"
    }).prettyPrint */

    def firstOccurrences(path : List[Int], ids : Set[RelationSymbol],
      t : Tree[Either[NormClause, RelationSymbol]]) : Seq[(List[Int], AbsLattice)] = t match {

      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex; 
                          res <- firstOccurrences(i :: path, ids + rel,  c)) yield res

        if ( /* !ids.contains(rel) && */ rel.arity > 0) {
          //println("!!!!!!!!!!!!!!!!rel is " + rel)
          //println("ids is " + ids)

          //println("adding rel" + rel)
          //println("new ids id " + rel::ids)

          absMap.get(rel.pred) match {
            case Some(r) => List((path, r.lattice)) ++ subres
            case None => subres
          }
        } else {
          subres
        }
      }
      case Tree(_, children) =>
        Seq() 
    }

    def firstN(stepsLeft : Int,
               path : List[Int],
               t : Tree[Either[NormClause, RelationSymbol]])
              : List[(List[Int], AbsLattice)] =
      if (stepsLeft == 0)
        List()
      else t match {
        case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
          val subres = for ((c, i) <- children.zipWithIndex; 
                            res <- firstN(stepsLeft - 1, i :: path, c)) yield res
          (absMap get rel.pred) match {
            case Some(r) => List((path, r.lattice)) ++ subres
            case _ => subres
          }
        }
        case _ =>
          List()
      }

   def lastOccurrences(path : List[Int],
                        t : Tree[Either[NormClause, RelationSymbol]])
                       : (List[(List[Int], AbsLattice)], Set[RelationSymbol]) = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val (subpaths, subsets) =
          (for ((c, i) <- children.zipWithIndex)
                yield lastOccurrences(i :: path, c)).unzip
        val flatSubpaths = for (s <- subpaths; p <- s) yield p
        val subOccurrences = (for (s <- subsets; rs <- s) yield rs).toSet
        (absMap get rel.pred) match {
          case Some(r) if (!(subOccurrences contains rel)) =>
            (List((path, r.lattice)) ++ flatSubpaths, subOccurrences + rel)
          case _ =>
            (flatSubpaths, subOccurrences)
        }
      }
      case Tree(_, children) =>
        (List(), Set())
    }

    def getLongestPath(path : List[Int],
                       t : Tree[Either[NormClause, RelationSymbol]])
                      : List[(List[Int], AbsLattice)] = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex)
                     yield getLongestPath(i :: path, c)
        val maxSubPath : List[(List[Int], AbsLattice)] =
          if (subres.isEmpty) List() else (subres maxBy { x => x.size })
        (absMap get rel.pred) match {
          case Some(r) => List((path, r.lattice)) ++ maxSubPath
          case None => maxSubPath
        }
      }
      case _ =>
        List()
    }

    def getLeafPaths(path : List[Int],
                     t : Tree[Either[NormClause, RelationSymbol]])
                    : List[(List[Int], AbsLattice)] = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex; 
                          res <- getLeafPaths(i :: path, c)) yield res
        (absMap get rel.pred) match {
          case Some(r) if (subres.size < 3) => List((path, r.lattice)) ++ subres
          case _ => subres
        }
      }
      case _ =>
        List()
    }

    val loopHeadSeq = absMap.keys.toList

    def getKthLoopHeadOccurrences(
             path : List[Int],
             t : Tree[Either[NormClause, RelationSymbol]])
           : (Seq[(List[Int], AbsLattice)], List[Int]) = t match {
      case Tree(Left(NormClause(constr, body, (rel, _))), children) => {
        val subres = for ((c, i) <- children.zipWithIndex)
                     yield getKthLoopHeadOccurrences(i :: path, c)
        val (subres1, subres2) = subres.unzip
        val subAbstractions = subres1.flatten
        val newLoopHeadCounts =
          (for ((loopHead, i) <- loopHeadSeq.iterator.zipWithIndex) yield {
             if (!(absMap(loopHead).loopBody contains rel.pred)) {
               0
             } else {
               val submax = (0 /: (for (l <- subres2.iterator) yield l(i))) (_ max _)
               if (loopHead == rel.pred)
                 submax + 1
               else
                 submax
             }
           }).toList

        val newAbstractions =
           (for ((loopHead, cnt) <- loopHeadSeq.iterator zip newLoopHeadCounts.iterator;
                 if (loopHead == rel.pred &&
                     cnt >= absMap(loopHead).loopIterationAbstractionThreshold))
            yield (path, absMap(loopHead).lattice)).toList ::: subAbstractions

        (newAbstractions, newLoopHeadCounts)
      }
      case _ =>
        (List(), for (_ <- loopHeadSeq) yield 0)
    }

    ////////////////////////////////////////////////////////////////////////////

    val maxProdSize = 10

//    clauseTree.prettyPrint
//    println("path is " + pathInfo)

    val decompositions =
      getKthLoopHeadOccurrences(List(), clauseTree)._1.sortBy(p => p._1.size).take(maxProdSize)
//      firstOccurrences(List(), Set(), clauseTree).take(maxProdSize)
//      lastOccurrences(List(), clauseTree)._1.take(maxProdSize)
//      firstN(5, List(), clauseTree).take(maxProdSize)
//      (firstN(3, List(), clauseTree).take(maxProdSize / 2) ++
//       getLeafPaths(List(), clauseTree).take(maxProdSize / 2)).toMap.toList

    if (decompositions.isEmpty)
      return None

    if (lazabs.GlobalParameters.get.log) {
      println
      println("Searching for interpolation abstractions ...")
    }

    Some(exploreLattice(clauseTree, decompositions, timeout)._1)
  }


  //////////////////////////////////////////////////////////////////////////////


  def createAbstractConstraintTrees(clauseTree : Tree[Either[NormClause, RelationSymbol]])
                                   : Option[(Tree[Seq[ConstantTerm]],
                                             Seq[(Tree[Conjunction], TermOrder)])] = {

    val maxProdSize = 20
    val pathInfo = getPath(clauseTree) match {
      case Seq() => return None
      case x => x // change this!!!!!
    }

    // Remove identical and subsumed paths .filter(  (!(ppi.toSet.contains(pi.toSet)) && pi != pp
    val reducedPathInfo = pathInfo
    //println("Path is " + pathInfo)
         //(for( (pi, l) <- pathInfo; (ppi, _) <- pathInfo) yield (pi, l)).distinct

    val toMerge = reducedPathInfo.size > maxProdSize

    // For now - if loops > 4 then we revert to using longest cycle otherwise 
    // we use the product lattice
    val (loopDecPoints, idPaths) = {
       val (loop, paths) = reducedPathInfo.unzip
       if (!toMerge) 
         (loop, paths) 
       else{
         // remove identical paths
         val slist = for( p <- paths) yield { p.size }
         val maxv = slist.max
         val ind = slist.indexOf(maxv)
         (List(loop(ind)), List(paths(ind)))
       }
    } 

    //println("clauseTree" + clauseTree)
    //println("loopDecPoints" + loopDecPoints)
    //println("Id Paths" + idPaths)

    /*
    val randGen = new scala.util.Random(12345)
    var psize = 0

    //val redPath = 


    if(reducedPathInfo.size > maxProdSize)
    {
      reducedPathInfo.filter{
        x => psize += 1
        val bv = randGen.nextBoolean
        //println("size is " + psize + "bool is " + bv)
        (bv && psize < maxProdSize)
      }.reverse
    }
    else
      reducedPathInfo.reverse
    

    val clModVars = for ((d, i) <- redPath) yield {
      getModVarIndex(d.reverse, i, clauseTree)

    }*/

    val clModVars = if (toMerge){
                      //println("merging")
                      List(getModVarIndex(loopDecPoints.head.reverse, idPaths.head.reverse, clauseTree))
                    }
                    else{ 
                      for ((d, i) <- reducedPathInfo.reverse) yield {
                        getModVarIndex(d.reverse, i.reverse, clauseTree)
                      }
                    }

    val (newClausesList, modVarsList) = clModVars.unzip

    // Lets check our modified variables
    //val modSyms = for(i <- modVars) yield idPath.head.arguments(i)

    val decompositionPoints = loopDecPoints

    //println("loop dec points " + loopDecPoints);
    ///val decompositionPoints = List(chosenDecPoint)

//    println("Predicates")
//    println(decompositionPoints) 

    def treeData[A](t : Tree[A], path : List[Int]) : A = path match {
      case i :: remPath => treeData(t.children(i), remPath)
      case List() => t.d
    }

    Some(exploreLattice(clauseTree,
                   for ((d, m) <- decompositionPoints zip modVarsList) yield {
                     treeData(clauseTree, d.reverse) match {
                       case Left(NormClause(_, _, (rs, _))) =>
                         (d, buildOctagonAbstraction(m, rs.arity))
                       case Right(rs) =>
                         (d, buildOctagonAbstraction(m, rs.arity))
                     }
                   },
                   2000)._1)
  }


  //////////////////////////////////////////////////////////////////////////////

  def interpolatingPredicateGenCEXAbsPetri(allActions : Seq[List[Int]],
                                           accelerateSingleActions : Boolean,
                                           accelerateIncreasingCycles : Boolean,
                                           globalOrthogonalSpace : Boolean) = {
    // Possibly check the orthogonal space of all actions

    val assertionTerms =
    if (globalOrthogonalSpace)
      SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
        import p._
        import IExpression._

        print("Computing orthogonal space of all actions ... ")
  
        val assertionTerms = new LinkedHashSet[(List[IdealInt], Int)]
  
        val consts = createConstants(allActions.head.size).toList
        !! (!and(for (c <- consts) yield (c === 0)))
  
        scope {
          for (vec <- allActions)
            !! (consts *:* (vec map (i(_))) === 0)
  
          while (??? == ProverStatus.Sat) {
            val coeffs = for (c <- consts) yield eval(c)
  
            assertionTerms +=
              ((coeffs.toList, 1),
               (for (c <- coeffs.toList) yield -c, 1))
  
            !! (consts *:* (coeffs map (i(_))) === 0)
          }
        }
  
        if (assertionTerms.isEmpty)
          println("empty")
        else
          println("" + (assertionTerms.size / 2) + " dimensions")
  
          // fill up with orthogonal terms, to ensure existence of
          // feasible abstractions

          def isInv(coeffs : List[IdealInt]) =
            !(allActions exists {
                vec => (for ((c, v) <- coeffs.iterator zip vec.iterator)
                        yield (c * v)).sum > 0
              })

          for ((termVector, _) <- assertionTerms)
            !! (consts *:* (termVector map (i(_))) === 0)
  
          while (??? == ProverStatus.Sat) {
            val coeffs = for (c <- consts) yield eval(c)
            val negCoeffs = for (c <- coeffs) yield -c

            assertionTerms +=
              ((coeffs, if (isInv(coeffs)) 2 else 5),
               (negCoeffs, if (isInv(negCoeffs)) 2 else 5))
    
            !! (consts *:* (coeffs map (i(_))) === 0)
          }

          assertionTerms.toList

      }
    else
      null

    abstractInterpolatingPredicateGen(
      createAbstractConstraintTreesPetri(assertionTerms,
                                         accelerateSingleActions,
                                         accelerateIncreasingCycles,
                                         _),
      false) _
  }

  //////////////////////////////////////////////////////////////////////////////

  var petriAbstractionNum = 10
  val PetriAbstractionNumUpper = 15
  val PetriAbstractionNumLower = 3

  private def createAbstractConstraintTreesPetri(
                globalTemplateTerms : List[(List[IdealInt], Int)],
                accelerateSingleActions : Boolean,
                accelerateIncreasingCycles : Boolean,
                clauseTree : Tree[Either[NormClause, RelationSymbol]]
              )
              : Option[(Tree[Seq[ConstantTerm]],
                        Seq[(Tree[Conjunction], TermOrder)])] = {

/*    (for (c <- clauseTree) yield c match {
      case Left(NormClause(_, _, (rel, _))) => rel.pred.name
      case _ => "X"
    }).prettyPrint */

    // counterexample should be linear
    assert(clauseTree.subtrees.iterator forall {
             case Tree(_, children) => children.size <= 1 })

    ////////////////////////////////////////////////////////////////////////////

    type Action = (Predicate, Seq[IdealInt], Predicate)

    val actions : List[Action] =
      (for (Left(c@NormClause(constraint, Seq((preRS, _)), (postRS, _))) <-
              clauseTree.iterator;
            if (postRS.pred != HornClauses.FALSE)) yield {
         implicit val order = c.order

         val reducer = ReduceWithEqs(constraint.arithConj.positiveEqs, order)
         val diffs = for ((a, b) <- c.headSyms zip c.bodySyms.head) yield (a - b)
         val vector = for (t <- diffs) yield {
           val r = reducer(t)
           assert(r.constants.isEmpty)
           r.constant
         }

         (preRS.pred, vector, postRS.pred)
       }).toList

    println
    for (((x, y, z), i) <- actions.iterator.zipWithIndex)
      println("" + i + ":\t" + x + " -> (" +
              ((for (v <- y.iterator) yield
                (if (v.signum < 0) ("" + v) else (" " + v))) mkString ", ") +
              ") -> " + z)

    val firstPred =
      (for (Left(NormClause(_, Seq((preRS, _)), _)) <- clauseTree.iterator)
       yield preRS.pred).toSeq.last

    val predicates =
      (for ((a, _, b) <- actions; x <- List(a, b)) yield x).distinct

    ////////////////////////////////////////////////////////////////////////////
    // Determine all minimal cycles occurring on the trace
    
    val minimalCycles = new ArrayBuffer[(List[Int], Int)]
    val decompositionTerms =
      new MHashMap[Action, LinkedHashSet[(List[IdealInt], Int)]]
    val decompositionFormulas =
      new MHashMap[Action, LinkedHashSet[(IFormula, Int)]]

    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
    import p._
    import IExpression._

    if (accelerateIncreasingCycles) try { withTimeout(1000) {
      print("Computing cycles ... ")

      val uniqueActions = actions.distinct
      val multiplicity = createConstants(uniqueActions.size)

      !! (multiplicity >= 0)

      val sums = Array.fill(firstPred.arity + predicates.size)(i(0))

      for (((pre, vec, post), actionNum) <- uniqueActions.iterator.zipWithIndex) {
        val mult = multiplicity(actionNum)

        for ((c, i) <- vec.iterator.zipWithIndex; if (!c.isZero))
          sums(i) = sums(i) + (c * mult)

        if (pre != post) {
          val preInd = firstPred.arity + (predicates indexOf pre)
          val postInd = firstPred.arity + (predicates indexOf post)
          sums(preInd) = sums(preInd) - mult
          sums(postInd) = sums(postInd) + mult
        }
      }

      !! (and(for (t <- sums.iterator) yield (t >= 0)))
      !! (!(multiplicity <= 0))

      if (accelerateSingleActions)    {
        // if also single actions are accelerated,
        // don't select those here
        !! (and(for ((m, (p1, a, p2)) <- multiplicity.iterator zip uniqueActions.iterator;
                    if (p1 == p2 && !(a exists (_.signum < 0))))
               yield (m === 0)))
      }

      while (??? == ProverStatus.Sat) {
        var mults = for (m <- multiplicity) yield eval(m)

        def assertDecrease = {
          for ((m, v) <- multiplicity.iterator zip mults.iterator)
            !! (m <= v)
          !! (or(for ((m, v) <- multiplicity.iterator zip mults.iterator)
                 yield (m < v)))
        }

        // can this loop be minimised?
        scope {
          var cont = true
          while (cont) {
            cont = false

            assertDecrease

            if (??? == ProverStatus.Sat) {
              cont = true

              mults = for (m <- multiplicity) yield eval(m)
              assertDecrease
            }
          }
        }

        val enabledActions =
          (for ((v, act) <- mults.iterator zip uniqueActions.iterator;
                if (!v.isZero)) yield (actions indexOf act)).toList

        minimalCycles += ((enabledActions, 3))

        !! (or(for ((m, v) <- multiplicity.iterator zip mults.iterator)
               yield (m < v)))
      }

      println("done")
    }} catch {
      case TimeoutException => println("T/O")
    }

    ////////////////////////////////////////////////////////////////////////////
    // Accelerate the cycles

    reset
    println

      val consts = createConstants(firstPred.arity)
      !! (!and(for (c <- consts) yield (c === 0)))

      try { withTimeout(1000) {
      for ((cycle, cost) <- minimalCycles) scope {
        println("Accelerating cycle: " + cycle)

        val sums = (for (i <- 0 until firstPred.arity)
                    yield (for (j <- cycle.iterator)
                           yield actions(j)._2(i)).sum).toList
//        println(sums)

        !! (consts *:* (sums map (i(_))) === 0)

        for (actionNum <- cycle.iterator /* ;
             if (!(cycle contains (actionNum + 1))) */ ) scope {
          val act@(_, actionVector, _) = actions(actionNum)
          !! (consts *:* (actionVector map (i(_))) === 0)

          val otherVectors =
            (for (num <- cycle; if (num != actionNum)) yield actions(num)._2).distinct

          while (??? == ProverStatus.Sat) {
            // try to add as many orthogonality constraints as possible
            var levels = 0
            var remOtherVectors = otherVectors

            while (!remOtherVectors.isEmpty) {
              val vec :: remVectors = remOtherVectors

              push
              !! (consts *:* (vec map (i(_))) === 0)

              ??? match {
                case ProverStatus.Sat => levels = levels + 1
                case ProverStatus.Unsat => pop
              }

              remOtherVectors = remVectors
            }

            ???

            // extract a new orthogonal vector
            val coeffs = for (c <- consts) yield eval(c)
//            println("  " + coeffs)

            decompositionTerms.getOrElseUpdate(
              act, new LinkedHashSet[(List[IdealInt], Int)]) +=
                ((coeffs.toList, cost),
                 (for (c <- coeffs.toList) yield -c, cost))
            
            for (_ <- 0 until levels) pop
            !! (consts *:* (coeffs map (i(_))) === 0)
          }
        }
      }
      }} catch {
        case TimeoutException =>
          println("T/O")
      }

      //////////////////////////////////////////////////////////////////////////

      // fill up with orthogonal terms, to ensure existence of
      // feasible abstractions
      for ((act, terms) <- decompositionTerms.toList) scope {
        for ((termVector, _) <- terms)
          !! (consts *:* (termVector map (i(_))) === 0)
        
        while (??? == ProverStatus.Sat) {
          // extract a new orthogonal vector
          val coeffs = for (c <- consts) yield eval(c)
//          println("Complement: " + coeffs)
          
          decompositionTerms(act) +=
              ((coeffs.toList, 15),
               (for (c <- coeffs.toList) yield -c, 15))
            
          !! (consts *:* (coeffs map (i(_))) === 0)
        }
      }

      //////////////////////////////////////////////////////////////////////////

      // accelerate transitions that occur repeatedly

      if (accelerateSingleActions) {
      val accelerated = new MHashSet[Action]
      for (index <- 0 until (actions.size - 1);
           if (!(accelerated contains actions(index)) &&
               actions(index) == actions(index + 1))) scope {
          println("Accelerating transition: " + index)
          accelerated += actions(index)

          val a@(_, vector, _) = actions(index)

          decompositionTerms.getOrElseUpdate(
            a, new LinkedHashSet[(List[IdealInt], Int)])
          decompositionFormulas.getOrElseUpdate(
            a, new LinkedHashSet[(IFormula, Int)])

          !! (consts *:* (vector map (i(_))) === 0)
          
          while (??? == ProverStatus.Sat) {
            // extract a new orthogonal vector
            val coeffs = for (c <- consts) yield eval(c)
          
            decompositionTerms(a) +=
              ((coeffs.toList, 3),
               (for (c <- coeffs.toList) yield -c, 3))
            
            !! (consts *:* (coeffs map (i(_))) === 0)
          }

          decompositionTerms(a) ++=
            (for (j <- 0 until firstPred.arity; if (vector(j).signum > 0))
             yield (List.tabulate(firstPred.arity) {
                      case `j` => IdealInt.MINUS_ONE
                      case _ => IdealInt.ZERO
                    }, 3))

          decompositionFormulas(a) ++=
            (for (j <- 0 until firstPred.arity; if (vector(j).signum < 0))
             yield (v(j) < 0, 3))
        }
      }

    }

    ////////////////////////////////////////////////////////////////////////////
    // Check the globally orthogonal vectors

    val gradedGlobalTemplateTerms =
      if (globalTemplateTerms == null) {
        null
      } else {
        for ((coeffs, cost) <- globalTemplateTerms)
        yield (coeffs,
               if (actions exists {
                     case (_, vec, _) => (for ((c, v) <- coeffs.iterator zip vec.iterator)
                                          yield (c * v)).sum > 0
                   })
                 (cost + 10) else cost)
      }

    ////////////////////////////////////////////////////////////////////////////

    val decompositions = {
      import IExpression._

      val termLattices =
        decompositionTerms mapValues { termVectors =>
           val lowerTerms =
             for ((vector, cost) <- termVectors.toList) yield
               (sum(for ((c, i) <- vector.iterator.zipWithIndex;
                         if (!c.isZero)) yield (v(i) *** c)),
                cost)
           TermIneqLattice(lowerTerms)
        }

      val formulaLattices =
        decompositionFormulas.filterNot({ case (_, f) => f.isEmpty })
                             .mapValues { formulas =>
                                          PredicateLattice(formulas.toList) }

      val cycleDecompositions =
        (for (act <- (termLattices.keySet ++ formulaLattices.keySet).iterator;
              lattice = (termLattices get act, formulaLattices get act) match {
                case (Some(l1), Some(l2)) => ProductLattice(l1, l2, true)
                case (Some(l), None) => l
                case (None, Some(l)) => l
                case _ => { assert(false); null }
              };
              indexes = List(actions indexOf act, actions lastIndexOf act).distinct;
              j <- indexes.iterator)
         yield (List.fill(j + 1)(0), lattice)).toList

/*      val initialValueDecomposition =
        List(List.fill(actions.size + 1)(0) ->
             TermIneqLattice((for (j <- 0 until firstPred.arity;
                                   t <- List(v(j), -v(j))) yield (t -> 10)))) */

      val globalDecompositions =
        if (gradedGlobalTemplateTerms == null) {
          List()
        } else {
          val assertionLattice = {
               val lowerTerms =
                 for ((vector, cost) <- gradedGlobalTemplateTerms) yield
                   (sum(for ((c, i) <- vector.iterator.zipWithIndex;
                             if (!c.isZero)) yield (v(i) *** c)),
                    cost)
               TermIneqLattice(lowerTerms)
          }

          List((List(0), assertionLattice),
               (List.fill(actions.size + 1)(0), assertionLattice))
        }

//      cycleDecompositions ++ initialValueDecomposition

      (globalDecompositions ++ cycleDecompositions).toMap.toList sortBy (_._1.size) take petriAbstractionNum
    }

    println("" + decompositions.size + " decomposition points")
//    println(decompositions)

    ////////////////////////////////////////////////////////////////////////////

//    clauseTree.prettyPrint
//    println("path is " + pathInfo)

    if (decompositions.isEmpty)
      return None

    println
    println("Searching for interpolation abstractions ...")

    val (res, status) = exploreLattice(clauseTree, decompositions, 1000)

    status match {
      case ExplorationResult.Timeout
        if (petriAbstractionNum > PetriAbstractionNumLower) =>
          petriAbstractionNum = petriAbstractionNum - 1
      case ExplorationResult.Bottom
        if (petriAbstractionNum < PetriAbstractionNumUpper) =>
          petriAbstractionNum = petriAbstractionNum + 1
      case _ =>
          // nothing
    }

    Some(res)
  }

}
