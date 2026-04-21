package compiler

import compiler.AST.Layer
import compiler.ASTLt.ConstLayer

import scala.collection.immutable.HashMap


/**
 * used to compute a string encoding the locus,and Ring at compile time. needs to be covariant, so that AST can also be.
 *
 * @param name
 * @tparam L
 */
class repr[+L](val name: L)

/**
 * used to compute the transfer field modeling the chip's frontier
 *
 * @param df boolean false when neighbor  is not definied
 * @tparam S1 main simplicial locus
 * @tparam S2 secondary simplicial locus
 */
class chip[S1 <: S, S2 <: S](val df: ConstLayer[T[S1, S2], B])
class chips[S1 <: S](val df: ConstLayer[S1, B])

object chip {
  /** trahsfer field near the  chip's border, can be undefined, the constant def layers indicates where it is defined,
   * so as to neutralize artefacts, when doing reductions.
   * obsolet: implicit is not longer in use, having been replaced by the miror, which result in much lighter code */
  implicit val borderVe = new chip[V, E](new ConstLayer[T[V, E], B](1, "def"))
  implicit val borderEv = new chip[E, V](null)
  implicit val borderVf = new chip[V, F](new ConstLayer[T[V, F], B](1, "def"))
  implicit val borderFv = new chip[F, V](null)
  implicit val borderFe = new chip[F, E](null)
  implicit val borderEf = new chip[E, F](new ConstLayer[T[E, F], B](1, "def"))
  implicit val borderE = new chips[E](new ConstLayer[E, B](1, "def"))
  implicit val borderF = new chips[F](new ConstLayer[F, B](1, "def"))
  //todo inclure tout les transfer locus, pas seulement Ve
  //val thinBorderV=new ConstLayer[V, B](1, "border")
}
/** this regroups layers which can be accessed from any macro $m$. the name of val correspond to
 * the name of the parameter in the javaloop method compiled for $m$,
 * therefore, A CA $c$ using m, will be able to find out the layer, generate the code that updates it, allocate it, */
object Layers {
  val layers:Map[String,Layer[_]]=HashMap(
  "defVe"->chip.borderVe.df)

}


object repr {
  def apply(a: Any) = new repr(a)

  implicit val nomV: repr[V] = new repr[V](V());
  implicit val nomE: repr[E] = new repr[E](E());
  implicit val nomF: repr[F] = new repr[F](F())

  implicit def nomT[L1 <: S, L2 <: S](implicit m1: repr[L1], m2: repr[L2]): repr[T[L1, L2]] =
    new repr[T[L1, L2]](T(m1.name, m2.name))
  implicit def nomCons[T1, T2](implicit m1: repr[T1], m2: repr[T2]): repr[(T1, T2)] =
    new repr[(T1, T2)]((m1.name, m2.name))

  implicit def nomLR[L <: Locus, R <: Ring](implicit m1: repr[L], m2: repr[R]): repr[(L, R)] =
    new repr[(L, R)]((m1.name, m2.name))
  def lpart[L <: Locus, R <: Ring](n: repr[(L, R)]): repr[L] = new repr[L](n.name._1)
  def rpart[L <: Locus, R <: Ring](n: repr[(L, R)]): repr[R] = new repr[R](n.name._2)

  implicit val nomB: repr[B] = new repr[B](B())
  implicit val nomR: repr[Ring] = new repr[Ring](new Ring())
  implicit val nomSI: repr[SI] = new repr[SI](SI())
  implicit val nomUI: repr[UI] = new repr[UI](UI())
  //implicit val nomUISI: repr[UISI] = new repr[UISI](UISI()); //nomI is not declared  as implicit, otherwise it would offer ambiguous implicit values.
  //implicit val nomUISIB: repr[UISIB] = new repr[UISIB](UISIB()); //nomI is not declared  as implicit, otherwise it would offer ambiguous implicit values.
  //implicit val nomToto: repr[Int] = new repr[Int](33); //used when we do not care anymore.

}

class AntiClock[S1 <: S, S2 <: S, S3 <: S]
object AntiClock {
  implicit val vef: AntiClock[V, E, F] = new AntiClock[V, E, F];
  implicit val vfe: AntiClock[V, F, E] = new AntiClock[V, F, E];
  implicit val evf: AntiClock[E, V, F] = new AntiClock[E, V, F];
  implicit val efv: AntiClock[E, F, V] = new AntiClock[E, F, V];
  implicit val fve: AntiClock[F, V, E] = new AntiClock[F, V, E];
  implicit val fev: AntiClock[F, E, V] = new AntiClock[F, E, V];
}

class CentralSym[S2, S1, S2new]
object CentralSym {
  implicit val vEv: CentralSym[V, E, V] = new CentralSym[V, E, V]
  implicit val fEf: CentralSym[F, E, F] = new CentralSym[F, E, F]
  implicit val vFe: CentralSym[V, F, E] = new CentralSym[V, F, E]
  implicit val eFv: CentralSym[E, F, V] = new CentralSym[E, F, V]
  implicit val eVe: CentralSym[E,V,E] = new CentralSym[E,V,E]
  implicit val fVf: CentralSym[F, V, F ] = new CentralSym[F,V,F]
}

class Red2[S1, S2, S3]
object Red2 {
  implicit val VEF: Red2[V, E, F] = new Red2[V, E, F]
}

