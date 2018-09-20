/* 
 * Adapted from 
 * NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * 
 */
package boolalg

import org.scalatest._

/**
 * Testing CNF conversion via Tseitin vs NNF & expansion.
 * JUnit -> ScalaTest
 */
class SolvingTest extends FlatSpec {


import scala.collection.mutable
import boolalg.Solver.{ Prop, True }
import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers
import boolalg.Solver._


  object SymName {
    def unapply(s: Sym): Option[String] = {
      Some(s.variable)
    }
  }

  implicit val ModelOrd: Ordering[Model] = Ordering.by {
    _.toSeq.sortWith {
      case ((sym1, v1), (sym2, v2)) =>
        val SymName(name1) = sym1
        val SymName(name2) = sym2
        if (name1 < name2)
          true
        else if (name1 > name2)
          false
        else
          v1 < v2
    }.toIterable
  }

  implicit val SolutionOrd: Ordering[Solution] =
    Ordering.by(_.model)

  def formatSolution(solution: Solution): String = {
    formatModel(solution.model)
  }

  def formatModel(model: Model): String = {
    (for {
      (SymName(name), value) <- model
    } yield {
      val v = if (value) "T" else "F"
      s"$name -> $v"
    }).mkString(", ")
  }

  def sym(name: String) = Sym(name)

  def testSymCreation() {
    val s1 = sym("hello")
    val s2 = sym("hello")
    assertEquals(s1, s2)
  }

  
  def test() {
    // NOT (1007)) OR ( NOT ( {1008} OR {1009} ) ) 

    val f1 = Not(sym("1007"))
    val f2 = Or(sym("1008"), sym("1009"))
    val f = Or(f1, Not(f2))

    println("f: " + f)
    println("feq " + eqFreePropToSolvableViaDistribution(f))
  }
    
  def testTseitinCnf() {
    //NOT (1007)) OR ( NOT ( {1008} OR {1009} OR {1010} OR {1011} OR {1012} OR {1013} OR {1014} OR {1015} ) ) 

    val f1 = Not(sym("1007"))
    val f2 = Or(sym("1008"), sym("1009"), sym("1010"), sym("1011"), sym("1012"), sym("1013"), sym("1014"), sym("1015"))
    val f = Or(f1, Not(f2))

    val tseitinCnf = propToSolvable(f)
    println("tseitinCnf: " + tseitinCnf)

    val tseitinSolutions = findAllModelsFor(tseitinCnf)
    assert(tseitinSolutions.size > 0)
  }



  /**
   * Simplest possible test: solve a formula and check the solution(s)
   */

  def testUnassigned() {
    val pSym = sym("p")
    val solvable = propToSolvable(Or(pSym, Not(pSym)))
    val solutions = findAllModelsFor(solvable)
    val expected = List(Solution(Map(), List(pSym)))
    assertEquals(expected, solutions)
  }

  /**
   * Unassigned variables must be expanded
   * for stable results
   */

  def testNoUnassigned() {
    val pSym = sym("p")
    val qSym = sym("q")
    val solvable = propToSolvable(Or(pSym, Not(qSym)))
    val solutions = findAllModelsFor(solvable)
    val expanded = solutions.flatMap(expandUnassigned).sorted
    val expected = Seq(
      Map(pSym -> false, qSym -> false),
      Map(pSym -> true, qSym -> false),
      Map(pSym -> true, qSym -> true)).sorted

    assertEquals(expected, expanded)
  }

 
  def testTseitinVsExpansionFrom_t7020() {
    val formulas = Seq(
      And(And(And(Not(sym("V1=null")),
        sym("V1=scala.collection.immutable.::[?]")), And(Not(sym("V1=null")),
        And(Or(sym("V2=4"), Or(sym("V2=5"), sym("V2=6"))), sym("V3=Nil")))),
        And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
          Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
          Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
          Not(sym("V3=null"))),
          And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
            Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
            Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
              sym("V1=null")))))))), And(Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))))),

      And(And(And(Not(sym("V1=null")),
        sym("V1=scala.collection.immutable.::[?]")), And(Not(sym("V1=null")),
        And(sym("V2=7"), sym("V3=Nil")))),
        And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
          Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
          Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
          Not(sym("V3=null"))),
          And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
            Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
            Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
              sym("V1=null")))))))), And(And(Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))), Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
            Not(sym("V3=Nil")))))))),

      And(And(Not(sym("V1=null")),
        sym("V1=scala.collection.immutable.::[?]")), And(Not(sym("V1=null")),
        And(Or(sym("V2=4"), Or(sym("V2=5"), sym("V2=6"))), sym("V3=Nil")))),

      And(And(Not(sym("V1=null")), sym("V1=scala.collection.immutable.::[?]")),
        And(Not(sym("V1=null")), And(sym("V2=7"), sym("V3=Nil")))),

      And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
        Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
        Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
        Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null")))))))), And(And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))))),

      And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
        Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
        Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
        Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null")))))))), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil"))))))),

      And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
        Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
        Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
        Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null")))))))), And(sym("V1=Nil"), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil"))))))))),

      And(And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))), And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))), And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=7")), Not(sym("V3=Nil"))))), Not(sym("V1=Nil"))))),

      And(And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil")))))),

      And(And(Or(sym("V3=scala.collection.immutable.::[?]"), sym("V3=Nil")),
        Or(sym("V1=scala.collection.immutable.::[?]"), sym("V1=Nil"))),
        And(And(Or(Or(False, Not(sym("V1=scala.collection.immutable.::[?]"))),
          Or(False, Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(False,
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
          Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))), And(Or(Or(False,
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
          Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
            Not(sym("V3=Nil"))))), And(Or(Or(False,
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
          Or(Not(sym("V2=7")), Not(sym("V3=Nil"))))), Not(sym("V1=Nil")))))),

      And(Not(sym("V1=null")), And(Or(sym("V2=4"), Or(sym("V2=5"), sym("V2=6"))),
        sym("V3=Nil"))),

      And(Not(sym("V1=null")), And(sym("V2=7"), sym("V3=Nil"))),

      And(Not(sym("V1=null")), sym("V1=scala.collection.immutable.::[?]")),

      And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),

      And(Not(sym("V2=5")), Not(sym("V2=6"))),

      And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
        Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
          sym("V1=null")))),

      And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
        Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
        Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
        Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null")))))))),

      And(Or(Not(sym("V3=Nil")), Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null")))))),

      And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
        Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
        Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
          sym("V1=null"))))),

      And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))), And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=7")), Not(sym("V3=Nil"))))), Not(sym("V1=Nil")))),

      And(Or(Or(False, Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))),

      And(Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=7")), Not(sym("V3=Nil"))))), Not(sym("V1=Nil"))),

      And(Or(Or(sym("V1=null"), Not(sym("V1=scala.collection.immutable.::[?]"))),
        Or(sym("V1=null"), Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")),
          Not(sym("V2=6")))), Not(sym("V3=Nil"))))), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil"))))))),

      And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))),

      And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=7")), Not(sym("V3=Nil"))))),
        And(And(Or(Not(sym("V1=scala.collection.immutable.::[?]")),
          Not(sym("V1=null"))), And(Or(sym("V3=scala.collection.immutable.::[?]"),
          Or(sym("V3=Nil"), sym("V3=null"))), And(Or(Not(sym("V3=Nil")),
          Not(sym("V3=null"))),
          And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
            Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
            Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
              sym("V1=null")))))))), And(sym("V1=Nil"), And(Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
            Not(sym("V3=Nil"))))), And(Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
          Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
          Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))))))),

      And(Or(sym("V2=4"), Or(sym("V2=5"), sym("V2=6"))), sym("V3=Nil")),

      And(Or(sym("V3=scala.collection.immutable.::[?]"), Or(sym("V3=Nil"),
        sym("V3=null"))), And(Or(Not(sym("V3=Nil")), Not(sym("V3=null"))),
        And(Or(Not(sym("V3=scala.collection.immutable.::[?]")),
          Not(sym("V3=null"))), And(Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),
          Or(sym("V1=scala.collection.immutable.::[?]"), Or(sym("V1=Nil"),
            sym("V1=null"))))))),

      And(Or(sym("V3=scala.collection.immutable.::[?]"),
        sym("V3=Nil")), Or(sym("V1=scala.collection.immutable.::[?]"),
        sym("V1=Nil"))),

      And(sym("V1=Nil"), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))), And(Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))), Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=2")), Not(sym("V3=Nil")))))))),

      And(sym("V2=7"), sym("V3=Nil")),

      False,

      Not(sym("V1=Nil")),

      Or(And(Not(sym("V2=4")),
        And(Not(sym("V2=5")), Not(sym("V2=6")))), Not(sym("V3=Nil"))),

      Or(False, Not(sym("V1=scala.collection.immutable.::[?]"))),

      Or(False,
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil")))),

      Or(False, Or(Not(sym("V2=1")), Not(sym("V3=Nil")))),

      Or(Not(sym("V1=Nil")), Not(sym("V1=null"))),

      Or(Not(sym("V3=scala.collection.immutable.::[?]")), Not(sym("V3=null"))),

      Or(Or(False, Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))),

      Or(Or(False,
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(False,
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))),

      Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil"))))),

      Or(Or(sym("V1=null"),
        Not(sym("V1=scala.collection.immutable.::[?]"))), Or(sym("V1=null"),
        Or(Not(sym("V2=1")), Not(sym("V3=Nil"))))),

      Or(sym("V1=null"), Not(sym("V1=scala.collection.immutable.::[?]"))),

      Or(sym("V1=null"),
        Or(And(Not(sym("V2=4")), And(Not(sym("V2=5")), Not(sym("V2=6")))),
          Not(sym("V3=Nil")))),

      Or(sym("V1=null"), Or(Not(sym("V2=1")), Not(sym("V3=Nil")))),

      Or(sym("V1=scala.collection.immutable.::[?]"),
        Or(sym("V1=Nil"), sym("V1=null"))),

      Or(sym("V1=scala.collection.immutable.::[?]"), sym("V1=Nil")),

      Or(sym("V2=4"), Or(sym("V2=5"), sym("V2=6"))),

      sym("V3=scala.collection.immutable.::[?]"))

    formulas foreach {
      f =>
        // build CNF
        val tseitinCnf = propToSolvable(f)
        // ALL-SAT
        val tseitinSolutions = findAllModelsFor(tseitinCnf)
        // expand unassigned variables
        // (otherwise solutions can not be compared)
        val tseitinNoUnassigned = tseitinSolutions.flatMap(expandUnassigned).sorted
    }
  }

  def pairWiseEncoding(ops: List[Sym]) = {
    And(ops.combinations(2).collect {
      case a :: b :: Nil => Or(Not(a), Not(b))
    }.toSet[Prop])
  }

  def testAtMostOne() {
    val dummySym = sym("dummy")
    val syms = "pqrstu".map(c => sym(c.toString)).toList
    // expand unassigned variables
    // (otherwise solutions can not be compared)
    val expected = findAllModelsFor(propToSolvable(And(dummySym, pairWiseEncoding(syms)))).flatMap(expandUnassigned)
    val actual = findAllModelsFor(propToSolvable(And(dummySym, AtMostOne(syms)))).flatMap(expandUnassigned)
    assertEquals(expected.toSet, actual.toSet)
  }

  def assertEquals( a: Object, b: Object) = assert((a == null && b == null) || (a != null && a.equals(b)))

  "tests " should " succeed " in {
  	 test()
	 testTseitinCnf()
	 testAtMostOne()
	 testUnassigned()
	 testNoUnassigned()
	 testTseitinVsExpansionFrom_t7020()
	 //assertEquals("2","4")
  }
}


