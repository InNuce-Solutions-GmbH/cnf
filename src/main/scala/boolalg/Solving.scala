/* 
 * Adapted from 
 * NSC -- new Scala compiler
 *
 * @author Adriaan Moors
 * Copyright 2011-2013 LAMP/EPFL
 * 
 */
package boolalg

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.language.postfixOps

// a literal is a (possibly negated) variable
class Lit(val v: Int) extends AnyVal {
  def unary_- : Lit = Lit(-v)

  def variable: Int = Math.abs(v)

  def positive = v >= 0

  override def toString(): String = if(positive) {s"$v" } else {s"NOT $v"} 
}

object Lit {
  def apply(v: Int): Lit = new Lit(v)

  implicit val LitOrdering: Ordering[Lit] = Ordering.by(_.v)
}

trait CNF extends PropositionalLogic {

  type Clause = Set[Lit]

  // a clause is a disjunction of distinct literals
  def clause(l: Lit*): Clause = l.toSet

  /**
   * Conjunctive normal form (of a Boolean formula).
   *  A formula in this form is amenable to a SAT solver
   *  (i.e., solver that decides satisfiability of a formula).
   */
  type Cnf = Array[Clause]

  class SymbolMapping(symbols: Set[Sym]) {
    val variableForSymbol: Map[Sym, Int] = {
      symbols.zipWithIndex.map {
        case (sym, i) => sym -> (i + 1)
      }.toMap
    }

    val symForVar: Map[Int, Sym] = variableForSymbol.map(_.swap)

    val relevantVars: Set[Int] = symForVar.keySet.map(math.abs)

    def lit(sym: Sym): Lit = Lit(variableForSymbol(sym))

    def size = symbols.size
    
    def symbolString(variable: Int) = symForVar.getOrElse(variable, Sym("notfound:" + variable)).toString
    
  }

  def cnfString(f: Array[Clause]): String
  
  final case class Solvable(cnf: Cnf, symbolMapping: SymbolMapping) {
    def ++(other: Solvable) = {
      require(this.symbolMapping eq other.symbolMapping)
      Solvable(cnf ++ other.cnf, symbolMapping)
    }

    override def toString: String = {
       alignAcrossRows(toSymbols.toList, "\\/", " /\\\n")
    }
    
    val toSymbols : Array[List[String]] =  cnf map (c => c.map( l => { (if(l.positive){ "" } else { "NOT " }) + symbolMapping.symbolString(l.variable)}).toList)
    
    def toFormulaString: String = toSymbols.map( l => l.mkString(" OR ")).mkString("(", " ) AND (", ")")
  }

  trait CnfBuilder {
    private[this] val buff = ArrayBuffer[Clause]()

    var literalCount: Int

    /**
     * @return new Tseitin variable
     */
    def newLiteral(): Lit = {
      literalCount += 1
      Lit(literalCount)
    }

    lazy val constTrue: Lit = {
      val constTrue = newLiteral()
      addClauseProcessed(clause(constTrue))
      constTrue
    }

    def constFalse: Lit = -constTrue

    def isConst(l: Lit): Boolean = l == constTrue || l == constFalse

    def addClauseProcessed(clause: Clause) {
      if (clause.nonEmpty) {
        buff += clause
      }
    }

    def buildCnf: Array[Clause] = {
      val cnf = buff.toArray
      buff.clear()
      cnf
    }

  }

  /**
   * Plaisted transformation: used for conversion of a
   * propositional formula into conjunctive normal form (CNF)
   * (input format for SAT solver).
   * A simple conversion into CNF via Shannon expansion would
   * also be possible but it's worst-case complexity is exponential
   * (in the number of variables) and thus even simple problems
   * could become untractable.
   * The Plaisted transformation results in an _equisatisfiable_
   * CNF-formula (it generates auxiliary variables)
   * but runs with linear complexity.
   * The common known Tseitin transformation uses bi-implication,
   * whereas the Plaisted transformation uses implication only, thus
   * the resulting CNF formula has (on average) only half of the clauses
   * of a Tseitin transformation.
   * The Plaisted transformation uses the polarities of sub-expressions
   * to figure out which part of the bi-implication can be omitted.
   * However, if all sub-expressions have positive polarity
   * (e.g., after transformation into negation normal form)
   * then the conversion is rather simple and the pseudo-normalization
   * via NNF increases chances only one side of the bi-implication
   * is needed.
   */
  class TransformToCnf(symbolMapping: SymbolMapping) extends CnfBuilder {

    // new literals start after formula symbols
    var literalCount: Int = symbolMapping.size

    def convertSym(sym: Sym): Lit = symbolMapping.lit(sym)

    def apply(p: Prop): Solvable = {

      def convert(p: Prop): Option[Lit] = {
        p match {
          case And(fv) =>
            Some(and(fv.flatMap(convert)))
          case Or(fv) =>
            Some(or(fv.flatMap(convert)))
          case Not(a) =>
            convert(a).map(not)
          case sym: Sym =>
            Some(convertSym(sym))
          case True =>
            Some(constTrue)
          case False =>
            Some(constFalse)
          case AtMostOne(ops) =>
            atMostOne(ops)
            None
        }
      }

      def and(bv: Set[Lit]): Lit = {
        if (bv.isEmpty) {
          // this case can actually happen because `removeVarEq` could add no constraints
          constTrue
        } else if (bv.size == 1) {
          bv.head
        } else if (bv.contains(constFalse)) {
          constFalse
        } else {
          // op1 /\ op2 /\ ... /\ opx <==>
          // (o -> op1) /\ (o -> op2) ... (o -> opx) /\ (!op1 \/ !op2 \/... \/ !opx \/ o)
          // (!o \/ op1) /\ (!o \/ op2) ... (!o \/ opx) /\ (!op1 \/ !op2 \/... \/ !opx \/ o)
          val new_bv = bv - constTrue // ignore `True`
          val o = newLiteral() // auxiliary Tseitin variable
          new_bv.map(op => addClauseProcessed(clause(op, -o)))
          o
        }
      }

      def or(bv: Set[Lit]): Lit = {
        if (bv.isEmpty) {
          constFalse
        } else if (bv.size == 1) {
          bv.head
        } else if (bv.contains(constTrue)) {
          constTrue
        } else {
          // op1 \/ op2 \/ ... \/ opx <==>
          // (op1 -> o) /\ (op2 -> o) ... (opx -> o) /\ (op1 \/ op2 \/... \/ opx \/ !o)
          // (!op1 \/ o) /\ (!op2 \/ o) ... (!opx \/ o) /\ (op1 \/ op2 \/... \/ opx \/ !o)
          val new_bv = bv - constFalse // ignore `False`
          val o = newLiteral() // auxiliary Tseitin variable
          addClauseProcessed(new_bv + (-o))
          o
        }
      }

      // no need for auxiliary variable
      def not(a: Lit): Lit = -a

      /**
       * This encoding adds 3n-4 variables auxiliary variables
       * to encode that at most 1 symbol can be set.
       * See also "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints"
       * http://www.carstensinz.de/papers/CP-2005.pdf
       */
      def atMostOne(ops: List[Sym]) {
        (ops: @unchecked) match {
          case hd :: Nil => convertSym(hd)
          case x1 :: tail =>
            // sequential counter: 3n-4 clauses
            // pairwise encoding: n*(n-1)/2 clauses
            // thus pays off only if n > 5
            if (ops.lengthCompare(5) > 0) {

              @inline
              def /\(a: Lit, b: Lit) = addClauseProcessed(clause(a, b))

              val (mid, xn :: Nil) = tail.splitAt(tail.size - 1)

              // 1 <= x1,...,xn <==>
              //
              // (!x1 \/ s1) /\ (!xn \/ !sn-1) /\
              //
              //     /\
              //    /  \ (!xi \/ si) /\ (!si-1 \/ si) /\ (!xi \/ !si-1)
              //  1 < i < n
              val s1 = newLiteral()
              /\(-convertSym(x1), s1)
              val snMinus = mid.foldLeft(s1) {
                case (siMinus, sym) =>
                  val xi = convertSym(sym)
                  val si = newLiteral()
                  /\(-xi, si)
                  /\(-siMinus, si)
                  /\(-xi, -siMinus)
                  si
              }
              /\(-convertSym(xn), -snMinus)
            } else {
              ops.map(convertSym).combinations(2).foreach {
                case a :: b :: Nil =>
                  addClauseProcessed(clause(-a, -b))
                case _ =>
              }
            }
        }
      }

      // add intermediate variable since we want the formula to be SAT!
      addClauseProcessed(convert(p).toSet)

      Solvable(buildCnf, symbolMapping)
    }
  }

  class AlreadyInCNF(symbolMapping: SymbolMapping) {

    object ToLiteral {
      def unapply(f: Prop): Option[Lit] = f match {
        case Not(ToLiteral(lit)) => Some(-lit)
        case sym: Sym            => Some(symbolMapping.lit(sym))
        case _                   => None
      }
    }

    object ToDisjunction {
      def unapply(f: Prop): Option[Array[Clause]] = f match {
        case Or(fv) =>
          val cl = fv.foldLeft(Option(clause())) {
            case (Some(clause), ToLiteral(lit)) =>
              Some(clause + lit)
            case (_, _) =>
              None
          }
          cl.map(Array(_))
        case True           => Some(Array()) // empty, no clauses needed
        case False          => Some(Array(clause())) // empty clause can't be satisfied
        case ToLiteral(lit) => Some(Array(clause(lit)))
        case _              => None
      }
    }

    /**
     * Checks if propositional formula is already in CNF
     */
    object ToCnf {
      def unapply(f: Prop): Option[Solvable] = f match {
        case ToDisjunction(clauses) => Some(Solvable(clauses, symbolMapping))
        case And(fv) =>
          val clauses = fv.foldLeft(Option(mutable.ArrayBuffer[Clause]())) {
            case (Some(cnf), ToDisjunction(clauses)) =>
              Some(cnf ++= clauses)
            case (_, _) =>
              None
          }
          clauses.map(c => Solvable(c.toArray, symbolMapping))
        case _ => None
      }
    }
  }

  def eqFreePropToSolvable(p: Prop): Solvable = {

    def doesFormulaExceedSize(p: Prop): Boolean = {
      p match {
        case And(ops) =>
          if (ops.size > AnalysisBudget.maxFormulaSize) {
            true
          } else {
            ops.exists(doesFormulaExceedSize)
          }
        case Or(ops) =>
          if (ops.size > AnalysisBudget.maxFormulaSize) {
            true
          } else {
            ops.exists(doesFormulaExceedSize)
          }
        case Not(a) => doesFormulaExceedSize(a)
        case _      => false
      }
    }

    val simplified = simplify(p)
    if (doesFormulaExceedSize(simplified)) {
      throw AnalysisBudget.formulaSizeExceeded
    }

    // collect all variables since after simplification / CNF conversion
    // they could have been removed from the formula
    val symbolMapping = new SymbolMapping(gatherSymbols(p))
    val cnfExtractor = new AlreadyInCNF(symbolMapping)
    val cnfTransformer = new TransformToCnf(symbolMapping)

    def cnfFor(prop: Prop): Solvable = {
      prop match {
        case cnfExtractor.ToCnf(solvable) =>
          // this is needed because t6942 would generate too many clauses with Tseitin
          // already in CNF, just add clauses
          solvable
        case p =>
          cnfTransformer.apply(p)
      }
    }

    simplified match {
      case And(props) =>
        // SI-6942:
        // CNF(P1 /\ ... /\ PN) == CNF(P1) ++ CNF(...) ++ CNF(PN)
        props.map(cnfFor).reduce(_ ++ _)
      case p =>
        cnfFor(p)
    }
  }

  def eqFreePropToSolvableViaDistribution(p: Prop) = {
    val symbolMapping = new SymbolMapping(gatherSymbols(p))

    type Formula = Array[Clause]

    def formula(c: Clause*): Formula = c.toArray

    def merge(a: Clause, b: Clause) = a ++ b

    def negationNormalFormNot(p: Prop): Prop = p match {
      case And(ps) => Or(ps map negationNormalFormNot)
      case Or(ps)  => And(ps map negationNormalFormNot)
      case Not(p)  => negationNormalForm(p)
      case True    => False
      case False   => True
      case s: Sym  => Not(s)
    }

    def negationNormalForm(p: Prop): Prop = p match {
      case Or(ps)       => Or(ps map negationNormalForm)
      case And(ps)      => And(ps map negationNormalForm)
      case Not(negated) => negationNormalFormNot(negated)
      case True
        | False
        | (_: Sym) => p
    }

    val TrueF: Formula = Array()
    val FalseF = Array(clause())
    def lit(sym: Sym) = Array(clause(symbolMapping.lit(sym)))
    def negLit(sym: Sym) = Array(clause(-symbolMapping.lit(sym)))

    def conjunctiveNormalForm(p: Prop): Formula = {
      def distribute(a: Formula, b: Formula): Formula =
        (a, b) match {
          // true \/ _ = true
          // _ \/ true = true
          case (trueA, trueB) if trueA.size == 0 || trueB.size == 0 => TrueF
          // lit \/ lit
          case (a, b) if a.size == 1 && b.size == 1                 => formula(merge(a(0), b(0)))
          // (c1 /\ ... /\ cn) \/ d = ((c1 \/ d) /\ ... /\ (cn \/ d))
          // d \/ (c1 /\ ... /\ cn) = ((d \/ c1) /\ ... /\ (d \/ cn))
          case (cs, ds) =>
            val (big, small) = if (cs.size > ds.size) (cs, ds) else (ds, cs)
            big flatMap (c => distribute(formula(c), small))
        }

      p match {
        case True        => TrueF
        case False       => FalseF
        case s: Sym      => lit(s)
        case Not(s: Sym) => negLit(s)
        case And(ps) =>
          ps.toArray flatMap conjunctiveNormalForm
        case Or(ps) =>
          ps map conjunctiveNormalForm reduceLeft { (a, b) =>
            distribute(a, b)
          }
      }
    }
    val cnf = conjunctiveNormalForm(negationNormalForm(p))
    Solvable(cnf, symbolMapping)
  }

  def prepareNewAnalysis() = {}

  def uncheckedWarning(msg: String) = sys.error(msg)

  def reportWarning(msg: String) = sys.error(msg)

  /**
   * The DPLL procedure only returns a minimal mapping from literal to value
   * such that the CNF formula is satisfied.
   * E.g. for:
   * `(a \/ b)`
   * The DPLL procedure will find either {a = true} or {b = true}
   * as solution.
   *
   * The expansion step will amend both solutions with the unassigned variable
   * i.e., {a = true} will be expanded to {a = true, b = true} and
   * {a = true, b = false}.
   */
  def expandUnassigned(solution: Solution): List[Model] = {
    import solution._

    // the number of solutions is doubled for every unassigned variable
    val expandedModels = 1 << unassigned.size
    var current = mutable.ArrayBuffer[Model]()
    var next = mutable.ArrayBuffer[Model]()
    current.sizeHint(expandedModels)
    next.sizeHint(expandedModels)

    current += model

    // we use double buffering:
    // read from `current` and create a two models for each model in `next`
    for {
      s <- unassigned
    } {
      for {
        model <- current
      } {
        def force(s: Sym, pol: Boolean) = model + (s -> pol)

        next += force(s, pol = true)
        next += force(s, pol = false)
      }

      val tmp = current
      current = next
      next = tmp

      next.clear()
    }

    current.toList
  }

}
