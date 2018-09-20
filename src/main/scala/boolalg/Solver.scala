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

// simple solver using DPLL
object Solver extends CNF {
  import scala.collection.mutable.ArrayBuffer

  def cnfString(f: Array[Clause]): String = {
    val lits: Array[List[String]] = f map (_.map(_.toString).toList)
    val xss: List[List[String]] = lits toList
    val aligned: String = alignAcrossRows(xss, "\\/", " /\\\n")
    aligned
  }
  
  

  // adapted from http://lara.epfl.ch/w/sav10:simple_sat_solver (original by Hossein Hojjat)

  // empty set of clauses is trivially satisfied
  val EmptyModel = Map.empty[Sym, Boolean]

  // no model: originates from the encounter of an empty clause, i.e.,
  // happens if all variables have been assigned in a way that makes the corresponding literals false
  // thus there is no possibility to satisfy that clause, so the whole formula is UNSAT
  val NoModel: Model = null

  // this model contains the auxiliary variables as well
  type TseitinModel = Set[Lit]
  val EmptyTseitinModel = Set.empty[Lit]
  val NoTseitinModel: TseitinModel = null

  // returns all solutions, if any (TODO: better infinite recursion backstop -- detect fixpoint??)
  def findAllModelsFor(solvable: Solvable): List[Solution] = {
    debugln("find all models for\n" + cnfString(solvable.cnf))

    // we must take all vars from non simplified formula
    // otherwise if we get `T` as formula, we don't expand the variables
    // that are not in the formula...
    val relevantVars: Set[Int] = solvable.symbolMapping.relevantVars

    // debug.patmat("vars "+ vars)
    // the negation of a model -(S1=True/False /\ ... /\ SN=True/False) = clause(S1=False/True, ...., SN=False/True)
    // (i.e. the blocking clause - used for ALL-SAT)
    def negateModel(m: TseitinModel) = {
      // filter out auxiliary Tseitin variables
      val relevantLits = m.filter(l => relevantVars.contains(l.variable))
      relevantLits.map(lit => -lit)
    }

    final case class TseitinSolution(model: TseitinModel, unassigned: List[Int]) {
      def projectToSolution(symForVar: Map[Int, Sym]) = Solution(projectToModel(model, symForVar), unassigned map symForVar)
    }

    def findAllModels(clauses: Array[Clause],
                      models: List[TseitinSolution],
                      recursionDepthAllowed: Int = AnalysisBudget.maxDPLLdepth): List[TseitinSolution] =
      if (recursionDepthAllowed == 0) {
        uncheckedWarning(AnalysisBudget.recursionDepthReached)
        models
      } else {
        debugln("find all models for\n" + cnfString(clauses))
        val model = findTseitinModelFor(clauses)
        // if we found a solution, conjunct the formula with the model's negation and recurse
        if (model ne NoTseitinModel) {
          // note that we should not expand the auxiliary variables (from Tseitin transformation)
          // since they are existentially quantified in the final solution
          val unassigned: List[Int] = (relevantVars -- model.map(lit => lit.variable)).toList
          debugln("unassigned " + unassigned + " in " + model)

          val solution = TseitinSolution(model, unassigned)
          val negated = negateModel(model)
          findAllModels(clauses :+ negated, solution :: models, recursionDepthAllowed - 1)
        } else models
      }

    val tseitinSolutions = findAllModels(solvable.cnf, Nil)
    tseitinSolutions.map(_.projectToSolution(solvable.symbolMapping.symForVar))
  }

  private def withLit(res: TseitinModel, l: Lit): TseitinModel = {
    if (res eq NoTseitinModel) NoTseitinModel else res + l
  }

  /**
   * Drop trivially true clauses, simplify others by dropping negation of `unitLit`.
   *
   *  Disjunctions that contain the literal we're making true in the returned model are trivially true.
   *  Clauses can be simplified by dropping the negation of the literal we're making true
   *  (since False \/ X == X)
   */
  private def dropUnit(clauses: Array[Clause], unitLit: Lit): Array[Clause] = {
    val negated = -unitLit
    val simplified = new ArrayBuffer[Clause](clauses.size)
    clauses foreach {
      case trivial if trivial contains unitLit => // drop
      case clause                              => simplified += clause - negated
    }
    simplified.toArray
  }

  def findModelFor(solvable: Solvable): Model = {
    projectToModel(findTseitinModelFor(solvable.cnf), solvable.symbolMapping.symForVar)
  }

  def mforeach[A](xss: Traversable[Traversable[A]])(f: A => Unit) = xss foreach (_ foreach f)

  def findTseitinModelFor(clauses: Array[Clause]): TseitinModel = {
    @inline def orElse(a: TseitinModel, b: => TseitinModel) = if (a ne NoTseitinModel) a else b

    debugln(s"DPLL\n${cnfString(clauses)}")

    val satisfiableWithModel: TseitinModel =
      if (clauses isEmpty) EmptyTseitinModel
      else if (clauses exists (_.isEmpty)) NoTseitinModel
      else clauses.find(_.size == 1) match {
        case Some(unitClause) =>
          val unitLit = unitClause.head
          withLit(findTseitinModelFor(dropUnit(clauses, unitLit)), unitLit)
        case _ =>
          // partition symbols according to whether they appear in positive and/or negative literals
          val pos = new mutable.HashSet[Int]()
          val neg = new mutable.HashSet[Int]()
          mforeach(clauses)(lit => if (lit.positive) pos += lit.variable else neg += lit.variable)

          // appearing in both positive and negative
          val impures = pos intersect neg
          // appearing only in either positive/negative positions
          val pures = (pos ++ neg) -- impures

          if (pures nonEmpty) {
            val pureVar = pures.head
            // turn it back into a literal
            // (since equality on literals is in terms of equality
            //  of the underlying symbol and its positivity, simply construct a new Lit)
            val pureLit = Lit(if (neg(pureVar)) -pureVar else pureVar)
            // debug.patmat("pure: "+ pureLit +" pures: "+ pures +" impures: "+ impures)
            val simplified = clauses.filterNot(_.contains(pureLit))
            withLit(findTseitinModelFor(simplified), pureLit)
          } else {
            val split = clauses.head.head
            // debug.patmat("split: "+ split)
            orElse(findTseitinModelFor(clauses :+ clause(split)), findTseitinModelFor(clauses :+ clause(-split)))
          }
      }
    satisfiableWithModel
  }

  private def projectToModel(model: TseitinModel, symForVar: Map[Int, Sym]): Model =
    if (model == NoTseitinModel) NoModel
    else if (model == EmptyTseitinModel) EmptyModel
    else {
      val mappedModels = model.toList collect {
        case lit if symForVar isDefinedAt lit.variable => (symForVar(lit.variable), lit.positive)
      }
      if (mappedModels.isEmpty) {
        // could get an empty model if mappedModels is a constant like `True`
        EmptyModel
      } else {
        mappedModels.toMap
      }
    }
}


