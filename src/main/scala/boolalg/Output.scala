/* 
 * Adapted from 
 * NSC -- new Scala compiler
 *
 * Copyright 2011-2013 LAMP/EPFL
 * 
 */

package boolalg

trait Output {
  def debugln(s: String) = {}

  private def max(xs: Seq[Int]) = if (xs isEmpty) 0 else xs max

  private def alignedColumns(cols: Seq[Any]): Seq[String] = {
    def toString(x: Any) = if (x == null) "" else x.toString
    if (cols.isEmpty || cols.tails.isEmpty) cols map toString
    else {
      val colLens = cols map (c => toString(c).length)
      val maxLen = max(colLens)
      val avgLen = colLens.sum / colLens.length
      val goalLen = maxLen min avgLen * 2
      def pad(s: String) = {
        val toAdd = ((goalLen - s.length) max 0) + 2
        (" " * (toAdd / 2)) + s + (" " * (toAdd / 2 + (toAdd % 2)))
      }
      cols map (x => pad(toString(x)))
    }
  }

  def alignAcrossRows(xss: List[List[Any]], sep: String, lineSep: String = "\n"): String = {
    val maxLen = max(xss map (_.length))
    val padded = xss map (xs => xs ++ List.fill(maxLen - xs.length)(null))
    padded.transpose.map(alignedColumns).transpose map (_.mkString(sep)) mkString (lineSep)
  }

}

