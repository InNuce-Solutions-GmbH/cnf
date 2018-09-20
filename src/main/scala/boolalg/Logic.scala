/* 
 * Adapted from 
 * NSC -- new Scala compiler
 *
 * @author Adriaan Moors
  * Copyright 2011-2013 LAMP/EPFL
 * 
 */
package boolalg

import scala.language.postfixOps
import scala.collection.mutable
import scala.collection.mutable.HashMap

trait PropositionalLogic extends Output {

  class Prop

  def uncheckedWarning(msg: String): Unit

  def reportWarning(message: String): Unit

  final case class And(ops: Set[Prop]) extends Prop {
    override def toString = "(" + ops.mkString(" AND ") + ")"
  }

  object And {
    def apply(ops: Prop*) = new And(ops.toSet)
  }

  final case class Or(ops: Set[Prop]) extends Prop {
    override def toString = "(" + ops.mkString(" OR ") + ")"
  }
  object Or {
    def apply(ops: Prop*) = new Or(ops.toSet)
  }

  final case class Not(a: Prop) extends Prop {
    override def toString = s"NOT ($a)"

  }

  // mutually exclusive (i.e., not more than one symbol is set)
  final case class AtMostOne(ops: List[Sym]) extends Prop

  case object True extends Prop
  case object False extends Prop

  // symbols are propositions
  final class Sym(val variable: String) extends Prop {

    override def equals(other: scala.Any): Boolean = other match {
      case that: Sym => this.variable == that.variable
      case _         => false
    }

    override def hashCode(): Int = {
      variable.hashCode
    }

    private val id: Int = Sym.nextSymId

    override def toString = {
      s"$variable"
    }
  }

  object Sym {
    private val uniques: HashMap[Sym, Sym] = new HashMap()
    def apply(variable: String): Sym = {
      val newSym = new Sym(variable)
      uniques.get(newSym) match {
        case Some(sym) => sym
        case None      => { uniques.put(newSym, newSym); newSym }
      }

    }
    def nextSymId = { _symId += 1; _symId }; private var _symId = 0
    implicit val SymOrdering: Ordering[Sym] = Ordering.by(_.id)
  }

  def /\(props: Iterable[Prop]) = if (props.isEmpty) True else And(props.toSeq: _*)
  def \/(props: Iterable[Prop]) = if (props.isEmpty) False else Or(props.toSeq: _*)

  /**
   * Simplifies propositional formula according to the following rules:
   * - eliminate double negation (avoids unnecessary Tseitin variables)
   * - flatten trees of same connectives (avoids unnecessary Tseitin variables)
   * - removes constants and connectives that are in fact constant because of their operands
   * - eliminates duplicate operands
   * - convert formula into NNF: all sub-expressions have a positive polarity
   * which makes them amenable for the subsequent Plaisted transformation
   * and increases chances to figure out that the formula is already in CNF
   *
   * Complexity: DFS over formula tree
   *
   * See http://www.decision-procedures.org/slides/propositional_logic-2x3.pdf
   */
  def simplify(f: Prop): Prop = {

    // limit size to avoid blow up
    def hasImpureAtom(ops: Seq[Prop]): Boolean = ops.size < 10 &&
      ops.combinations(2).exists {
        case Seq(a, Not(b)) if a == b => true
        case Seq(Not(a), b) if a == b => true
        case _                        => false
      }

    // push negation inside formula
    def negationNormalFormNot(p: Prop): Prop = p match {
      case And(ops) => Or(ops.map(negationNormalFormNot)) // De'Morgan
      case Or(ops)  => And(ops.map(negationNormalFormNot)) // De'Morgan
      case Not(p)   => negationNormalForm(p)
      case True     => False
      case False    => True
      case s: Sym   => Not(s)
    }

    def negationNormalForm(p: Prop): Prop = p match {
      case And(ops)     => And(ops.map(negationNormalForm))
      case Or(ops)      => Or(ops.map(negationNormalForm))
      case Not(negated) => negationNormalFormNot(negated)
      case True
        | False
        | (_: Sym)
        | (_: AtMostOne) => p
    }

    def simplifyProp(p: Prop): Prop = p match {
      case And(fv) =>
        // recurse for nested And (pulls all Ands up)
        val ops = fv.map(simplifyProp) - True // ignore `True`

        // build up Set in order to remove duplicates
        val opsFlattened = ops.flatMap {
          case And(fv) => fv
          case f       => Set(f)
        }.toSeq

        if (hasImpureAtom(opsFlattened) || opsFlattened.contains(False)) {
          False
        } else {
          opsFlattened match {
            case Seq()  => True
            case Seq(f) => f
            case ops    => And(ops: _*)
          }
        }
      case Or(fv) =>
        // recurse for nested Or (pulls all Ors up)
        val ops = fv.map(simplifyProp) - False // ignore `False`

        val opsFlattened = ops.flatMap {
          case Or(fv) => fv
          case f      => Set(f)
        }.toSeq

        if (hasImpureAtom(opsFlattened) || opsFlattened.contains(True)) {
          True
        } else {
          opsFlattened match {
            case Seq()  => False
            case Seq(f) => f
            case ops    => Or(ops: _*)
          }
        }
      case Not(Not(a)) =>
        simplify(a)
      case Not(p) =>
        Not(simplify(p))
      case p =>
        p
    }

    val nnf = negationNormalForm(f)
    simplifyProp(nnf)
  }

  trait PropTraverser {
    def apply(x: Prop): Unit = x match {
      case And(ops)       => ops foreach apply
      case Or(ops)        => ops foreach apply
      case Not(a)         => apply(a)
      case s: Sym         => applySymbol(s)
      case AtMostOne(ops) => ops.foreach(applySymbol)
      case _              =>
    }
    def applySymbol(x: Sym): Unit = {}
  }

  def gatherSymbols(p: Prop): Set[Sym] = {
    val syms = new mutable.HashSet[Sym]()
    (new PropTraverser {
      override def applySymbol(s: Sym) = syms += s
    })(p)
    syms.toSet
  }

  trait PropMap {
    def apply(x: Prop): Prop = x match {
      case And(ops) => And(ops map apply)
      case Or(ops)  => Or(ops map apply)
      case Not(a)   => Not(apply(a))
      case p        => p
    }
  }

  // to govern how much time we spend analyzing matches for unreachability/exhaustivity
  object AnalysisBudget {
    val maxDPLLdepth = 100
    val maxFormulaSize = 100 * math.min(Int.MaxValue / 100, maxDPLLdepth)

    def recursionDepthReached =
      s"Exhaustivity analysis reached max recursion depth, not all missing cases are reported.\n"

    abstract class Exception(val advice: String) extends RuntimeException("CNF budget exceeded")

    object formulaSizeExceeded extends Exception(s"The analysis required more space than allowed.\n")

  }

  type Solvable

  def propToSolvable(p: Prop): Solvable = {
    eqFreePropToSolvable(p)
  }

  def eqFreePropToSolvable(f: Prop): Solvable

  type Model = Map[Sym, Boolean]
  val EmptyModel: Model
  val NoModel: Model

  final case class Solution(model: Model, unassigned: List[Sym])

  def findModelFor(solvable: Solvable): Model

  def findAllModelsFor(solvable: Solvable): List[Solution]

}


