package org.jetbrains.plugins.scala
package lang
package psi
package api
package expr

/** 
* @author Alexander Podkhalyuzin
* Date: 07.03.2008
*/

trait ScParenthesisedExpr extends ScInfixArgumentExpression {
  def expr: Option[ScExpression] = findChild(classOf[ScExpression])
}

object ScParenthesisedExpr {
  def unapply(p: ScParenthesisedExpr): Option[ScExpression] = p.expr
}