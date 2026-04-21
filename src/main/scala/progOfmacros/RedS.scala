package progOfmacros

import compiler.AST._
import compiler.ASTBfun.redop
import compiler.ASTL._
import compiler.ASTLfun._
import compiler.Circuit.iTabSymb
import compiler._

import scala.collection.immutable.HashMap

/** allows to automatically generate macro for simplicial reductions */
object RedS {
  /** memoizes all the already used Boolean reduction */
  private var redSmem: iTabSymb[Fundef1[(S, Ring), (S, Ring)]] = HashMap()

  /** how to build the name of simplicial reduction. The prefix ofthe name (until the point) informs about
   * name of the file where macro is to be stored
   * source and target simplicial locus, as well as reduction operation */
  private def redsfunName[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], p: repr[R]) = {
    val y = 0
    ("" + "redS" + r._1.name + "." + l.shortName + n.name.shortName ).toLowerCase
  }


  /**
   *
   * @param r
   * @param l
   * @param m
   * @param n
   * @param d  constant layer defining neighborhood which are undefined
   * @tparam S1 source simplicial type
   * @tparam S2 target simplicial type
   * @return computes the scala code of a whole  simplicial reduction, is done here because Broadcast Transfer and Redop are private to ASTL. */
  def redsDirect[S1 <: S, S2 <: S, R <: Ring](r: redop[R], arg: ASTLt[S1, R])
                                             (implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): ASTLt[S2, R] = {
    val broadcasted = broadcast[S1, S2, R](arg) //step 1 is broadcast
    val transfered: ASTLt[T[S2, S1], R] = transfer[S1, S2, R](broadcasted)(repr.nomT(n, m), q) //step 2 is transfer
    val res = reduce[S2, S1, R](r, transfered) //(n,m,d) yzeté implicit killerest
    res
  }
  /**
   *
   * @tparam S1 source
   * @tparam S2 target
   * @return
   */
  private def redSfunDef[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): //pour defVe S1=E,S2=V
  Fundef1[(S1, R), (S2, R)] = {
    val param = pL[S1, R]("p" + l.shortName + n.name.shortName) //parameter names inform about locus
    Fundef1(redsfunName(r, l)(m, n, q), redsDirect[S1, S2, R](r, param), param) // we compute a function of one argument. res is the body, param are the single parameter
  }
  /**
   *
   * @param S1 origine simplicial type
   * @param S2 target simplicial type
   * @param r  reduction applied
   * @return function in scala which does the corresponding simplicial reduction,  memoised in redSmem
   */
  def getRedSFun[S1 <: S, S2 <: S, R <: Ring](r: redop[R], l: S1)(implicit m: repr[S1], n: repr[S2], q: repr[R], d: chip[S2, S1]): Fundef1[(S1, R), (S2, R)] = {
    val funName = redsfunName(r, l)(m, n, q)
    if (!redSmem.contains(funName)) //redSmem memoizes so that we 'd compile the function only once.
      redSmem = redSmem + (funName -> redSfunDef(r, l)(m, n, q, d))
    redSmem(funName).asInstanceOf[Fundef1[(S1, R), (S2, R)]]
  }




}
