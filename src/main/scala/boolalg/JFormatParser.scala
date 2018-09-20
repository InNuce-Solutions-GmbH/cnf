package boolalg

import boolalg.Solver.{ Prop, True }
import scala.util.matching.Regex
import scala.collection.mutable.ListBuffer
import scala.util.parsing.combinator.RegexParsers
import scala.collection.mutable.HashMap
import boolalg.Solver._
import scala.collection.mutable.HashSet

object JFormatParser extends RegexParsers {

  //Example: "NOT (1007) OR ( NOT ( {1008} OR {1009} OR {1010} OR {1011} OR {1012} OR {1013} OR {1014} OR {1015} ) )")

  private lazy val atom = """[a-z0-9-]+""".r ^^ { case x => Sym(x) }

  private lazy val parens: Parser[Prop] = "(" ~> exp <~ ")"
  
  private lazy val term: Parser[Prop] = parens | atom | not

  private lazy val andterm = and | term

  private lazy val or: Parser[Prop] = andterm ~ rep1("OR" ~ andterm) ^^ {
    case f1 ~ fs ⇒ {
      val ot = new HashSet[Prop]();
      ot.add(f1);
      fs.map(p => { ot.add(p._2) })
      new Or(ot.toSet)
    }
  }

  private lazy val not: Parser[Prop] = ("NOT" | "¬") ~ term ^^ { case f1 ~ f2 => { Not(f2) } };

  private lazy val and: Parser[Prop] = term ~ rep1("AND" ~ term) ^^ {
    case f1 ~ fs ⇒ {
      val ot = new HashSet[Prop]();
      ot.add(f1);
      fs.map(p => { ot.add(p._2) })
      new And(ot.toSet)
    }
  }

  private lazy val exp = (or | andterm)

  def lparse(asText: String): Option[Prop] = {
    val cleaned = asText.replaceAll("\\s", "").replaceAll("[{}]", "")
    parse(exp, cleaned) match {
      case Success(matched, _) => { Some(matched) }
      case Failure(msg, _)     => { None }
      case Error(msg, _)       => { None }
    }
  }
}


