package compiler

import AST._
import ASTB._
import ASTBfun.{orRedop, _}
import ASTL.{ASTLg, Structural, redop, _}
import ASTLfun._
import dataStruc.Align2._
import Constraint._
import Circuit._
import repr._
import dataStruc.{Dag, Util}
import dataStruc.DagNode._

import scala.annotation.unused
import scala.collection.immutable.HashSet
import scala.collection.{mutable, _}
import scala.reflect.ClassTag
import scala.language.implicitConversions
import dataStruc.Util.{composeAll2, dupliqueOrTriplique, rot, rotPerm, rotR}
import sdn.{Compar, Compar3, ComparApex2, ComparDiff}

import scala.runtime.ScalaRunTime
/**
 * todo we must distinguish between the wrapper of the constructors, and the higher order function which can be defined in another object
 * At some point, we decided to store the type information for each distinct constructor, in order to have direct access to this info
 * when copying the constructor,
 * this enabled to enforce the covariance in L:Locus and R:Ring, which was intuitive and would therefore facilitate things later on.
 * but then we abandonned it, so we could come back to previous setting where type was not stored, and copied in case class copying (see ASTBs).
 * constructors are declared private and therefore, they are associated to a wrapper which can be used to build expressions.
 */
object ASTL {
  private val cache = scala.collection.mutable.HashMap[ASTLg,ASTLg]()

  val u = 1

  /** delayedL reprograms delayed, in order to add the trait ASTLt[L, R] */
  def delayedL[L <: Locus, R <: Ring](_arg: => ASTLt[L, R])(implicit m: repr[(L, R)]): ASTLt[L, R] = {
    lazy val delayed = _arg
    new Delayed[(L, R)](() => delayed) with ASTLt[L, R]
  }

  /** Implement structural equality for ASTL */
  trait Structural extends Product {
    @transient private lazy val cachedHash = ScalaRunTime._hashCode(this)
    override def hashCode(): Int = cachedHash

    protected def fastEq(other: Any): Boolean = other match {
      case that: AnyRef if that.getClass eq this.getClass =>
        if (this.asInstanceOf[AnyRef] eq that) true
        else if (this.hashCode != that.hashCode) false
        else this.productIterator.sameElements(that.asInstanceOf[Product].productIterator)
      case _ => false
    }
  }

  private[ASTL] case class Coonst[L <: Locus, R <: Ring](cte: ASTBt[R], m: repr[L], n: repr[R])
    extends ASTL[L, R]()(repr.nomLR(m, n)) with EmptyBag[AST[_]] with Structural
  {override def equals(other: Any): Boolean = fastEq(other)
  }

  def const[L <: Locus, R <: Ring](cte: ASTBt[R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] =
    {  val tmp=Coonst(cte, m, n);
      cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Coonst[L,R]]  }

  private[ASTL]
  final case class Broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R], m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural
    {override def equals(other: Any): Boolean = fastEq(other)
  }

  def broadcast[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[S1, R])(implicit m: repr[T[S1, S2]], n: repr[R]): ASTLt[T[S1, S2], R] =
  { val tmp =  new Broadcast[S1, S2, R](arg, m, n) //step 1 is broadcast
  cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Broadcast[S1, S2, R]]
  }
  /** a bit more subtle than broadcast, sends a distinct field to each of T[S1,S2]
   * size of the list is equal to fanout of locus for vertex it is 6, For edge it is 2.  */
  private[ASTL] final case class Send[S1 <: S, S2 <: S, R <: Ring](args: List[ASTLt[S1, R]])
                                                                  (implicit m: repr[T[S1, S2]], n: repr[R])
    extends ASTL[T[S1, S2], R]() with Neton[AST[_]]with Structural {override def equals(other: Any): Boolean = fastEq(other)
  }

  def send[S1 <: S, S2 <: S, R <: Ring](args: List[ASTLt[S1, R]])
                                       (implicit m: repr[T[S1, S2]], n: repr[R]): ASTLt[T[S1, S2], R] = {
    assert(args.length == 6 / args.head.locus.density); // check that the number of args is correct
   val tmp= Send[S1, S2, R](args);
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Send[S1, S2, R]]
  }
  /*  def sendv[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, V]], n: repr[R]): Send[S1, V, R] = {
      assert(args.length == 6 / args.head.locus.density);
      Send[S1, V, R](args);
    } //TODO check the length of args

    def sende[S1 <: S, R <: Ring](args: List[ASTLt[S1, R]])(implicit m: repr[T[S1, E]], n: repr[R]) =
      Send[S1, E, R](args);*/

  private[ASTL] final case class Transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R], m: repr[T[S2, S1]], n: repr[R])
    extends ASTL[T[S2, S1], R]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural
{override def equals(other: Any): Boolean = fastEq(other)
}

  def transfer[S1 <: S, S2 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])(implicit m: repr[T[S2, S1]], n: repr[R]):  ASTLt[T[S2, S1], R] =
  {val tmp= Transfer(arg, m, n)
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[ASTLt[T[S2, S1], R]]

  }


  import scala.runtime.ScalaRunTime



  /** Unop is not final, because we can add operators < */
  private[ASTL] case class Unop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Fundef1[R1, R2], arg: ASTLt[L, R1], m: repr[L], n: repr[R2])
    extends ASTL[L, R2]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural {
     override def equals(other: Any): Boolean = fastEq(other)


  }

  def unop[L <: Locus, Ri <: Ring, Ro <: Ring](f: Fundef1[Ri, Ro], arg: ASTLt[L, Ri])(implicit m: repr[L], n: repr[Ro]): ASTLt[L, Ro]
  = {
   val tmp= Unop[L, Ri, Ro](f, arg, m, n)
     cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Unop[L,Ri,Ro]]
  }

  private[ASTL] final case class Binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](
             op: Fundef2[R1, R2, R3], arg: ASTLt[L, R1], arg2: ASTLt[L, R2], m: repr[L], n: repr[R3])
    extends ASTL[L, R3]()(repr.nomLR(m, n)) with Doubleton[AST[_]] with Structural {
      override def equals(other: Any): Boolean =fastEq(other)
  }

  /** factory binop */
  def binop[L <: Locus, R1 <: Ring, R2 <: Ring, R3 <: Ring](op: Fundef2[R1, R2, R3], arg: ASTLt[L, R1], arg2: ASTLt[L, R2])
                                                           (implicit m: repr[L], n3: repr[R3]): ASTLt[L, R3]
  = {
    val tmp=new Binop[L, R1, R2, R3](op, arg, arg2, m, n3)
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Binop[L,R1,R2,R3]]

  } //with ASTLt[L, R2]

  /**
   * @tparam S1 towards wich we reduce
   */
  private[ASTL] final case class Redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R], m: repr[S1], n: repr[R])
    extends ASTL[S1, R]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural {
    override def equals(other: Any): Boolean = fastEq(other)
    /** used to compute the expression being reduced.  */
    override def redExpr: List[AST[_]] = List(arg)
  }

  def redop[S1 <: S, S2 <: S, R <: Ring](op: redop[R], arg: ASTLt[T[S1, S2], R])(implicit m: repr[S1], n: repr[R]): ASTLt[S1, R]
  = {val tmp =Redop[S1, S2, R](op, arg, m, n)
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Redop[S1, S2, R]]

  }

/** We can apply a binop on two Ev or two Ef */
  private[ASTL] final case class BinopEdge[ S2 <: S, R <: Ring, P<: Ring](op: Fundef2RP[R,P], arg: ASTLt[T[E, S2], R], m: repr[E], n: repr[R], n2: repr[P])
    extends ASTL[E, P]()(repr.nomLR(m, n2)) with Singleton[AST[_]] with Structural {
  override def equals(other: Any): Boolean = fastEq(other)
  override def binopEdgeExpr: List[AST[_]] = List(arg)
    /** used to compute the expression being reduced.  */
   // override def redExpr: List[AST[_]] = List(arg)
  }

  def binopEdge[S2 <: S, R <: Ring, P <: Ring](op:  Fundef2RP[R,P], arg: ASTLt[T[E,S2], R])(implicit m: repr[E], n: repr[R], n2: repr[P]): ASTLt[E, P]
  = {val tmp=BinopEdge[ S2, R, P](op, arg, m, n, n2)
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[BinopEdge[ S2, R, P]]

  }


  /** @param dir true if rotation is clockwise */
  private[ASTL] final case class Clock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](
                                                                              arg: ASTLt[T[S1, S2], R], dir: Boolean, t: AntiClock[S1, S2, S3], m: repr[T[S1, S3]], n: repr[R])
    extends ASTL[T[S1, S3], R]()(repr.nomLR(m, n)) with Singleton[AST[_]]with Structural {
    override def equals(other: Any): Boolean = fastEq(other)}

  def clock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                                 (implicit t: AntiClock[S1, S2, S3], m: repr[T[S1, S3]], n: repr[R]): ASTLt[T[S1, S3], R] =
    {val tmp=Clock[S1, S2, S3, R](arg, dir = true, t, m, n)
      cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Clock[S1, S2, S3, R]]}


      def anticlock[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
                                                     (implicit t: AntiClock[S1, S2, S3], m: repr[T[S1, S3]], n: repr[R]): ASTLt[T[S1, S3], R] =
   { val tmp= Clock[S1, S2, S3, R](arg, dir = false, t, m, n)
     cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[Clock[S1, S2, S3, R]]}



  /** central symmetry, used on vertices */
  private[ASTL] final case class Sym[S1 <: S, S2 <: S, S2new <: S, R <: Ring]
  (arg: ASTLt[T[S1, S2], R], m: repr[T[S1, S2new]], t: CentralSym[S2, S1, S2new], n: repr[R])
    extends ASTL[T[S1, S2new], R]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural
 {override def equals(other: Any): Boolean = fastEq(other)
 }

  def sym[S1 <: S, S2 <: S, S3 <: S, R <: Ring](arg: ASTLt[T[S1, S2], R])
               (implicit t: CentralSym[S2, S1, S3], m: repr[T[S1, S3]], n: repr[R]): ASTLt[T[S1, S3], R] = {
    val tmp=Sym(arg, m, t, n)
    cache.getOrElseUpdate(tmp.asInstanceOf[ASTLg], tmp.asInstanceOf[ASTLg]).asInstanceOf[ASTLt[T[S1, S3], R]]
  }


  /** the concat reduction takes a bool transfer, and produces an unsigned int. n=UI , I am not so sure I've used it*/
  private[ASTL] final case class RedopConcat[S1 <: S, S2 <: S](arg: ASTLt[T[S1, S2], B], m: repr[S1], n: repr[UI])
    extends ASTL[S1, UI]()(repr.nomLR(m, n)) with Singleton[AST[_]] with Structural
  {override def equals(other: Any): Boolean = fastEq(other)
  /** used to compute the expression being reduced. */
    override def redExpr: List[AST[_]] = List(arg)
  }


  /** Fields which have a value both  at time t, and t+1 ,todo layers should implement it */
  trait Strate[L <: Locus, R <: Ring] {
    val pred: ASTLt[L, R];
    val munext: ASTLt[L, R]
  }

  type ASTLg = ASTLt[_ <: Locus, _ <: Ring]
  type rewriteASTLt[L <: Locus, R <: Ring] = ASTLt[L, R] => ASTLt[L, R]


  /*

    def id[L <: Locus, R <: Ring](arg: ASTLt[L, R])(implicit m: repr[L], n: repr[R]): ASTL[L, R] = (arg.ring match {
      case B() => Unop(identityB, arg.asInstanceOf[ASTLt[L, B]], m, repr.nomB)
      case UI() => Unop(identityUI.asInstanceOf[Fundef1[R, R]], arg, m, n)
      case SI() => Unop(identitySI.asInstanceOf[Fundef1[R, R]], arg, m, n)
    }).asInstanceOf[ASTL[L, R]]
  */



}


object SpatialType {
  type ASTLtG = ASTLt[_ <: Locus, _ <: Ring]
  type IntV = ASTLt[V, SI];
  type IntE = ASTLt[E, SI];
  type IntF = ASTLt[F, SI]
  type IntEv = ASTLt[T[E, V], SI];
  type IntVe = ASTLt[T[V, E], SI]
  type IntFv = ASTLt[T[F, V], SI];
  type IntVf = ASTLt[T[V, F], SI]
  type IntEf = ASTLt[T[E, F], SI];
  type IntFe = ASTLt[T[F, E], SI]
  type UintV = ASTLt[V, UI];
  type SintV = ASTLt[V, SI];
  type SintE = ASTLt[E, SI];
  /** Unsigned int for which lt,gt,eq,le,ge are defined submembers */
  type UintVx = UintV with Compar with ComparApex2 with Compar3;
  type SintVx = SintV with ComparDiff[SI]
  type UintE = ASTLt[E, UI];
  type UintF = ASTLt[F, UI]
  type UintEv = ASTLt[T[E, V], UI];
  type UintVe = ASTLt[T[V, E], UI]
  type UintFv = ASTLt[T[F, V], UI];
  type UintVf = ASTLt[T[V, F], UI]
  type UintEf = ASTLt[T[E, F], UI];
  type UintFe = ASTLt[T[F, E], UI]
  type BoolV = ASTLt[V, B];
  type BoolE = ASTLt[E, B];
  type BoolF = ASTLt[F, B]
  type BoolVe = ASTLt[T[V, E], B];
  type BoolEv = ASTLt[T[E, V], B]
  type BoolFv = ASTLt[T[F, V], B];
  type BoolVf = ASTLt[T[V, F], B]
  type BoolEf = ASTLt[T[E, F], B];
  type BoolFe = ASTLt[T[F, E], B]

}
/**
 * AST of spatial type
 *
 * @tparam L : the locus in V,E or F   *  @tparam R: the  type   *  @constructor
 * @param m : implicit used to compute the locus and scala type
 *          made a lot of effort to make it covariant, but that seems useless, in fact.
 *          I've put the type locus + ring as part of  the case construct's fields, so that it becomes very easy to copy
 */
sealed abstract class ASTL[L <: Locus, R <: Ring]()(implicit m: repr[(L, R)]) extends ASTLt[L, R] {

  override def isRedop =
    this.asInstanceOf[ASTL[_, _]] match {
      case Redop(_, _, _, _) => true
      case _ => false
    }

  override def isCoonst =
    this.asInstanceOf[ASTL[_, _]] match {
      case Coonst(_, _, _) => true
      case _ => false
    }

  override def isBinopEdge =
    this.asInstanceOf[ASTL[_, _]] match {
      case BinopEdge(_, _, _, _,_) => true
      case _ => false
    }

  /*override def isElt =
    this.asInstanceOf[ASTL[_, _]] match {
      case Unop(elt: Elt[_], _, _, _) => true
      case _ => false
    }*/

  override def isSend=
    this.asInstanceOf[ASTL[_, _]] match {
      case Send(_) => true
      case _ => false
    }


  def opRedop =
    this.asInstanceOf[ASTL[_, _]] match {
      case Redop(op, _, _, _) => op
      case _ => throw new Exception("tried to take op of nonredop")
    }

  override def toString: String =
    this.asInstanceOf[ASTL[_, _]] match {
      //  case Layer(s, _)                 => "Layer " + this.name + ":" + locus.toString.charAt(0) + "-" + ring.toString.charAt(0)
      case Binop(op, _, _, _, _) => op.name
      case Coonst(cte, _, _) => "Const" + cte.toString + locus.toString.charAt(0) + "_" + ring.toString.substring(0, ring.toString.length() - 2);

      //  case Multop(op, args,_,_)      => op.toString
      case Unop(op, _, _, _) => op.name
      case Redop(op: (Fundef2R[Ring], ASTBt[Ring]), _, _, _) => "red" + op._1.name
      case BinopEdge(op, _, _, _, _) => "binopEdge" + op.name
      case RedopConcat(_, _, _) => "redConcat"
      case Clock(_, dir, _, _, _) => if (dir) "clock" else "anticlock"
      case e@Broadcast(_, _, _) => "Broadcast" + ("" + (e.locus.asInstanceOf[T[_, _]] match {
        case T(_, y) => y
      })).charAt(0)
      case e@Send(_) => "Send" + ("" + (e.locus.asInstanceOf[T[_, _]] match {
        case T(_, y) => y
      })).charAt(0)
      case Transfer(_, _, _) => "Transfer"
      case Sym(_, _, _, _) => "sym "
    }

  /**
   * @param id rewritting procedure
   * @return ASTL obtained by applying the rewriting recursively
   *         No  override, because name is distinct from AST's propagate */
  def propagateASTL(id: rewriteASTLt[L, R]): ASTL[L, R] = {
    def id2[L3 <: Locus, R3 <: Ring]: rewriteASTLt[L3, R3] = d => id(d.asInstanceOf[ASTLt[L, R]]).asInstanceOf[ASTLt[L3, R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTLg] match {
      case e: EmptyBag[_] => e
      case e@Broadcast(a, _, _) => e.copy(arg = id2(a))
      case e@Send(a) => e.copy(args = a.map(id2))(lpart(e.mym), rpart(e.mym))
      case e@Transfer(a, _, _) => e.copy(arg = id2(a))
      case e@Unop(_, a, _, _) => e.copy(arg = id2(a))
      case e@Binop(_, a, a2, _, _) => e.copy(arg = id2(a), arg2 = id2(a2))
      case e@Redop(_, a, _, _) => e.copy(arg = id2(a))
      case e@BinopEdge(_, a, _, _, _) => e.copy(arg = id2(a))
      case e@RedopConcat(a, _, _) => e.copy(arg = id2(a))
      case e@Clock(a, _, _, _, _) => e.copy(arg = id2(a)) //(lpart(e.mym), rpart(e.mym))
      case e@Sym(a, _, _, _) => e.copy(arg = id2(a))
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTL[L, R]]
  }

  /**
   * @param cur        The current programm
   * @param ASTbitSize Stores number of bits of sub expression.
   * @param newtSymb   The symbol table with number of bits of parameters and progressively upadated with variables
   * @return Expression rewritten so as to include Extend, when binop operators are used,
   *         and one of the two operands has not enough bits.
   *
   */
  override def bitIfyAndExtend(cur: DataProg[InfoType[_]], ASTbitSize: AstMap[Int], newtSymb: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val emptyAstMapInt = immutable.HashMap.empty[AST[_], Int] //stores the bit number of an ASTB expression
    /** collect the bit size that  the spatial param and then non spatial operators should have. */
    val paramBitIncrease = mutable.HashMap.empty[String, Int]

    val result = this match {
      case Binop(op, a, a2, l2, r2) => //BINOP needs more work, because it triggers possible insertion of  "extend";
        var anew = a.bitIfyAndExtend(cur, ASTbitSize, newtSymb); //process recursively subtree
        var a2new = a2.bitIfyAndExtend(cur, ASTbitSize, newtSymb) //process recursively subtree
        val nbitASTBParam = emptyAstMapInt + (op.p1 -> ASTbitSize(anew)) + (op.p2 -> ASTbitSize(a2new)) // bit size  of the parameters of the boolean function
        val nbitResult: Int = ASTB.nbitExpAndParam(nbitASTBParam, op.arg, paramBitIncrease) //retrieves the number of bit computed from the call to the ASTB fonction
        if (paramBitIncrease.contains(op.p1.nameP)) //check if first ASTL param is desired to be "extended"
        anew = anew.extendMe(paramBitIncrease(op.p1.nameP)) //extends parameters used in the expression
        // of the first effective parameter if the first ASTB param is desired to be extended
        if (paramBitIncrease.contains(op.p2.nameP)) //check if second ASTL param shoudl be "extended"
        a2new = a2new.extendMe(paramBitIncrease(op.p2.nameP)) //same thing for second effective parameter
        val newthis = Binop(op, anew, a2new, l2, r2)
        ASTbitSize += newthis -> nbitResult //Store the bitsize of the Binop
        newthis
      case _ => //in all the other cases, no change is done on the AST, only  expASTLbitSize is updated.
        val newthis = this.propagateASTL((d: ASTLt[L, R]) => d.bitIfyAndExtend(cur, ASTbitSize, newtSymb))

        def argBitSize() = ASTbitSize(newthis.asInstanceOf[Singleton[AST[_]]].arg) //bit size of the arg if singleton

        ASTbitSize += newthis -> (newthis.asInstanceOf[ASTL[_, _]] match {
          // case l:Layer[_,_] =>  l.nbit
          case Coonst(cte, _, _) => ASTB.nbitExpAndParam(emptyAstMapInt, cte, paramBitIncrease)
          case Unop(op, _, _, _) => ASTB.nbitExpAndParam(emptyAstMapInt + (op.p1 -> argBitSize()), op.arg, paramBitIncrease)
          case Clock(_, _, _, _, _) | Transfer(_, _, _) | Broadcast(_, _, _) | Sym(_, _, _, _) => argBitSize() //bit size equals bit size of arg
          case Redop(op, _, _, _) =>
            if (op._1 == concatB)
              this.locus.fanout
            else if (op._1 == concatUI) {
              this.locus.fanout*argBitSize()
            } //else if (op._1.body.mym.name==B())    1//we can reduce int an produce boolean, on Edges.
            else
              argBitSize()
          case BinopEdge(op,arg,  _, _, _) =>
            var anew = arg.bitIfyAndExtend(cur, ASTbitSize, newtSymb);
            if (op.body.mym.name==B()) 1 else
             {
               val name=if(arg.name==null) arg.asInstanceOf[Read[_]].which else arg.name
               newtSymb(name).nb //abracadabra2
             }  //on pari que c'est la taille de l'operande.//throw new Exception("faut chercher le bitsize de l'op")
          case Send(_) => ASTbitSize(newthis.asInstanceOf[Neton[AST[_]]].args.head)
          case RedopConcat(exp, _, _) =>
            this.locus.fanout   //for the concat redop, the number of bit must take into account the arity (2,3, or 6)

        })
        newthis
    };
    result.setName(this.name);
    result
  }

  /**
   * @return true if the expression contains  only 1-concatenation -2-elt or 3-Broadcast
   *         indeed, those operators can be handled at the level of main instead of macro
   **/
  override def justConcatsorBroadcast: Boolean = this.asInstanceOf[ASTLg] match {
    case Unop(Fundef1(namef, _, _), arg, _, _) =>
      if (namef.startsWith("elt"))
        arg.justConcatsorBroadcast
      else false
    case Binop(Fundef2("concat", _, _, _), arg, arg2, _, _) =>
      arg.justConcatsorBroadcast && arg2.justConcatsorBroadcast
    case RedopConcat(arg, _, _) => arg.justConcatsorBroadcast
    case Broadcast(arg, _, _) => arg.justConcatsorBroadcast
    case _ => super.justConcatsorBroadcast
  }

  def redOpSeq(m: Machine, zones: Dag[Zone], tZone: Map[String, Zone]) = this.asInstanceOf[ASTLg] match {
    case Redop(op, a, _, _) =>
      val expUnfolded = a.unfoldTransfer(m)
      val u = 0
  }

  override def childSameBitSize: Set[ASTLg] = {
    this.asInstanceOf[ASTLg] match {
      case Unop(op, a, _, n) =>
        val par = ASTBt.paramSameBitSize(op)
        if (par.size == 1)
          new HashSet() + inputNeighbors(0).asInstanceOf[ASTLg]
        else
          new HashSet()
      case Binop(op, a, a2, _, n) =>
        val par = ASTBt.paramSameBitSize(op).toList
        val pos: Seq[Int] = par.map(op.p.indexOf(_)) //retrieve the indexes
        HashSet[ASTLg]() ++ pos.map(inputNeighbors(_).asInstanceOf[ASTLg])
      case _ => HashSet()
    }
  }

  override def extendMe(nbit: Int): ASTLt[L, R] = {
    this.asInstanceOf[ASTLg] match {
      case u@Unop(op, arg, _, n) =>
        val par = ASTBt.paramSameBitSize(op)
        if (par.size == 1) {
          val newArg = arg.extendMe(nbit)
          u.copy(arg = newArg).asInstanceOf[ASTLt[L, R]]
        }
        else
          extendMeDirect(nbit)
      case b@Binop(op, a, a2, _, n) =>
        val par: Set[String] = ASTBt.paramSameBitSize(op)
        if (par.size == 1) {
          val pos = op.p.indexOf(par.head) //retrieve the indexes
          if (pos == 0)
            b.copy(arg = a.extendMe(nbit)).asInstanceOf[ASTLt[L, R]]
          else
            b.copy(arg2 = a2.extendMe(nbit)).asInstanceOf[ASTLt[L, R]]
        }
        else extendMeDirect(nbit)
      case _ => extendMeDirect(nbit)
    }
  }
  override def unfoldSimplic(m: Machine): ArrAst = {
    val r = rpart(mym.asInstanceOf[repr[(L, R)]])
    val s = this.locus.asInstanceOf[S]
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s.sufx.length)(cte)
      case Broadcast(_, _, _) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Send(_) => throw new RuntimeException("Broadcast creates   a transfer type")
      case Transfer(_, _, _) => throw new RuntimeException("Transfer creates   a transfer type")
      case Unop(op, a, _, _) =>
        if (op.name.equals("increaseRadius2")) //we add the tm1s early so as to be able to remove them early
        // a.unfoldTransfer(m).map(_.map(x => tm1[R](x.asInstanceOf[ASTBt[R]])(n.asInstanceOf[repr[R]]).asInstanceOf[ASTBg]))
          a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(
            (x => tm1[R](x.asInstanceOf[ASTBt[R]])(r).asInstanceOf[ASTBg]))
        else
          a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(
        new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(r) with ASTBt[R].asInstanceOf[ASTBg])
      case Binop(op, a, a2, _, _) => a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).zip(a2.unfoldSimplic(m)).map({
        case (c, c2) => new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(r) with ASTBt[R].asInstanceOf[ASTBg]
      })
      case Redop(op, a, _, _) =>
        /** creates a binary tree of several call to opred       */
        def reduceEncapsulated(as: Array[ASTBt[R]], opred: redop[R]) =
          as.toList.tail.foldLeft(as(0))(new Call2(opred._1, _, _)(r) with ASTBt[R])
        val result=a.unfoldTransfer(m).map((x: ArrAst) =>
          reduceEncapsulated(x.asInstanceOf[Array[ASTBt[R]]], op.asInstanceOf[redop[R]])).asInstanceOf[ArrAst]
        result
      case BinopEdge(op, a, _, _, _) =>
        /** creates three binary tree of op     */
       val t=a.unfoldTransfer(m)
         assert(t.size==3)
        //op peut ne pas etre symmetrique, faut donc vérifier l'ordre.
        t.map((x: ArrAst) =>new Call2(op, x(0), x(1))(r) with ASTBt[R])
      case RedopConcat(a, _, _) =>
        def reduceConcatEncapsulated(as: Array[ASTBt[B]]): ASTBt[UI] =
          as.toList.tail.foldLeft(as(0).asInstanceOf[ASTBt[UI]])(new Concat2[UI, B, UI](_, _))

        a.unfoldTransfer(m).map((x: ArrAst) =>
          reduceConcatEncapsulated(x.asInstanceOf[Array[ASTBt[B]]])).asInstanceOf[ArrAst]
      case Clock(_, _, _, _, _) => throw new RuntimeException("Clock creates    a transfer type")

      case Sym(_, _, _, _) => throw new RuntimeException("Sym creates  a transfer type")
    }
    //read and Call treated in ASTLt.

  }

  override def unfoldTransfer(m: Machine): ArrArrAstBg = {
    val T(s1, des) = this.locus;
    val rr = this.ring
    val suf = this.locus.sufx
    val l2 = suf.length
    this.asInstanceOf[ASTLg] match {
      case Coonst(cte, _, _) => Array.fill(s1.sufx.length, l2)(cte)
      case Broadcast(a, _, _) =>
        a.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m).map(Array.fill(l2)(_))
      case Send(a) =>
        if (a.length != l2) throw new RuntimeException("incorrect number of arguments for send")
        val res=a.toArray.map(_.asInstanceOf[ASTLt[_, _]].unfoldSimplic(m)).transpose
        res
      case Transfer(a, _, _) =>
        val u = 0
        val res = m(des, s1, a.unfoldTransfer(m))
        res
      case Unop(op, a, _, n) =>
        val k = 0
        if (op.name.equals("increaseRadius2")) //we add the tm1s early so as to be able to remove them early
          a.unfoldTransfer(m).map(_.map(x => tm1[R](x.asInstanceOf[ASTBt[R]])(n.asInstanceOf[repr[R]]).asInstanceOf[ASTBg]))
        else
          a.unfoldTransfer(m).map(_.map(new Call1(op.asInstanceOf[Fundef1[Any, R]], _)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]))
      case Binop(op, a, a2, _, n) =>
        val arg1 = a.unfoldTransfer(m)
        val arg2 = a2.unfoldTransfer(m)
        arg1.zip(arg2).map({
        case (b, b2) => b.zip(b2).map({
          case (c, c2) =>
            new Call2(op.asInstanceOf[Fundef2[Any, Any, R]], c, c2)(n.asInstanceOf[repr[R]]) with ASTBt[R].asInstanceOf[ASTBg]
        })
      })
      case Redop(_, _, _, _) => throw new RuntimeException("Reduces create a simplicial type, not a transfer type")
      case BinopEdge(_, _, _, _, _) => throw new RuntimeException("BinopEdge creates a simplicial type, not a transfer type")
      case Clock(a, dir, _, _, _) =>
        val T(_, src) = a.locus
        val trigo = !dir
        val atr = a.unfoldTransfer(m)
        if ((src < des) ^ dir) atr else atr.map(rot(_, trigo)) //in the clock relation, the indexing remins the same, we just have to change the locus
      case Sym(a, _, _, _) =>
        val T(s1, src) = a.locus; //a.locus is T [E,V]
        val atr0: Array[Array[ASTBg]] = a.unfoldTransfer(m)
        val res = s1 match {
          case V() => atr0.map(rotR(_)).map(rotR(_)).map(rotR(_)) //throw new RuntimeException("sym not defined on V in the general case")
          case E() => atr0.map(rotR(_)); // la composée de deux rotation est une rotation simple qui est aussi une permutation pour E.
          case F() => src match {
            case E() => val Array(Array(db, ds1, ds2), Array(ub, us1, us2)) = atr0;
             // Array(Array(db, ds2, ds1), Array(ub, us2, us1))
              Array(Array(db, ds2, ds1), Array(ub, us2, us1)) //on inverse 1 et 2
            case  V() => val Array(Array(db, ds1, ds2), Array(ub, us1, us2)) = atr0;
              Array(Array(db, ds2, ds1), Array(ub, us2, us1)) //on inverse 1 et 2, c'est symetrique
            //case V() identical to case E
          }
          //if (src < des) atr else atr.map(rotR(_)) //we follow trigonometric, the composition of tree anticlock  must add one rotation, if not(src<des).
        }
        res
      //read and Call treated in ASTLt.
    }
  }

  def shouldAffect: Boolean = this match {
    case Redop(_, _, _, _) => true
    case Binop(_, a1, a2, _, _) => a1.isInstanceOf[ASTL.Clock[_, _, _, _]] || a2.isInstanceOf[ASTL.Clock[_, _, _, _]] || a1.isInstanceOf[ASTL.Sym[_, _, _, _]] || a2.isInstanceOf[ASTL.Sym[_, _, _, _]] //that's an overkill, unnecessary introduced variables will have to be removed
    case _ => false
  }

  /**
   * @param r stores results consisting of alignement, shifted instructions, and generated constraints
   * @return tree with some id being replaced by shifted version,
   *         cycle constraint, instruction setting the shifted version, alignement with respect to used variables.
   */
  override def align(r: Result, tt: TabSymb[InfoNbit[_]]): ASTLt[L, R] = {
    val newExp = this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => this
      case e@Broadcast(arg, _, _) => val newArg = arg.align(r, tt);
        r.algn = r.algn.map { case (k, v) => k -> arg.locus.proj };
        e.copy(arg = newArg)



      case e@Transfer(arg, _, _) =>
        val T(s1, s2) = arg.locus;
        val t = hexPermut((s1, s2));
        val newArg = arg.align(r, tt);
        r.c = permute(r.c, t, e.locus);
        r.algn = composeAll2(t, r.algn)
        e.copy(arg = newArg)
      case e@Unop(_, arg, _, _) =>
        e.copy(arg = arg.align(r, tt))

      case e@Send(args: List[ASTLt[S, Ring]]) => //pour binopEdge, se traite comme binop en fait.
        //val newArgs = args.map(_.align(r, tt)) //collects results in $r
        //r.algn = r.algn.map { case (k, v) => k -> args.head.locus.proj } //does not depend on v, because v is constant
        //e.copy(args = newArgs)(lpart(e.mym), rpart(e.mym))
        var newArgs:List[ASTLt[S, Ring]]=List()
      for(arg<-args){
        val r2=Result()
        var newArg = arg.align(r2, tt) //r2 contient un align de edge, avec trois composante, (ou de face avec deux!)
        val alignedTwice: Predef.Set[String] = r.algn.keys.toSet.intersect(r2.algn.keys.toSet);
        val alignedTwiceDistinctly = alignedTwice.filter(s => !r.algn(s).sameElements(  dupliqueOrTriplique(r2.algn(s)))) //variables with two distinct alignement due to clock/sym operation
        if (alignedTwiceDistinctly.size > 0) // we process only the case with a single such variable
          throw new Exception(" send implies some more alignement, like binop,  we should look more closeley !")
        else {
          for ((k, v) <- r2.algn)
            r.algn += k -> dupliqueOrTriplique(v)  //pour passer d'un align de edge a un align de Ev, on duplique
          newArgs=newArg::newArgs //aprés faut faire reverse, tudieu
        }
      }

        e.copy(args = newArgs.reverse)(lpart(e.mym), rpart(e.mym))

      case e@Binop(_, arg1, arg2, _, _) => //c'est la qu'on bosse!
        val r2=Result()
        var newArg = arg1.align(r2, tt)
       // val algn: Map[String, Array[Int]] = r.algn //on memorize le align de la premiere expression.

        var newArg2 = arg2.align(r, tt)
        val alignedTwice: Predef.Set[String] = r.algn.keys.toSet.intersect(r2.algn.keys.toSet);
        val alignedTwiceDistinctly = alignedTwice.filter(s => r.algn(s) != r2.algn(s)) //variables with two distinct alignement due to clock/sym operation
        if (alignedTwiceDistinctly.size > 1) // we process only the case with a single such variable
          throw new Exception(" more than one to aligne !")
        if (alignedTwiceDistinctly.size== 1)
          System.out.println("aligned twice")
        if (alignedTwiceDistinctly.nonEmpty && !(r2.algn(alignedTwiceDistinctly.head) sameElements r.algn(alignedTwice.head))) {
          //k is the aux defined by an instr which will have to use two registers.
          val nome: String = alignedTwiceDistinctly.head //here we assume that there is a single input variable
          val perm = compose(invert(r2.algn(nome)), r.algn(nome))
          val shiftedE = "shift" + nome
          r.c = intersect(r.c, Some(Cycle(perm, locus.asInstanceOf[TT]))) //ici on ajoute une contrainte de cycle sur la zone, via r
          val repr = new repr(tt(nome).t) // asInstanceOf[repr[(L, R)]]
          val read = new Read(nome)(repr) with ASTLt[L, R] //not used at the end!
          val shiftInstr = Affect(shiftedE, read) //we shift the clock in order to obtain the right correspondance
          // between shif and shifted
          //TODO le alignperm de shiftInstr on le fait ensuite!
          //    shiftInstr.alignPerm=perm
          r.si += nome -> shiftInstr
          r.algn += shiftedE -> r2.algn(nome)
          //newArg = newArg.replaceBy(nome, shiftedE) //the first sub expression is left as is
          newArg2 = newArg2.replaceBy(nome, shiftedE) //in the second espression, we will use the shifted variable.
        }
        else //we combine the alignement from each operand of the binop
          for ((k, v) <- r2.algn)
            r.algn += k -> v
        e.copy(arg = newArg, arg2 = newArg2)
      case e@Redop(_, arg, _, _) => e.copy(arg = arg.align(r, tt))
      case e@BinopEdge(_, arg, _, _, _) => e.copy(arg = arg.align(r, tt))
      case e@Clock(arg, dir, _, _, _) =>
        val newArg = arg.align(r, tt)
        val T(_, des) = this.locus;
        val T(_, src) = arg.locus;
        val trigo = !dir;
        val atr = rotPerm(if (trigo) 1 else 5) //faudrait vérifier is c'est pas le contraire
        if ((src < des) ^ dir) {
          r.c = permute(r.c, atr, e.locus);
          r.algn = composeAll2(atr, r.algn)
        }
        e.copy(arg = newArg) //(lpart(e.mym), rpart(e.mym))
      case e@Sym(arg, _, _, _) => val newArg = arg.align(r, tt)
        val T(_, des) = this.locus;
        val T(s1, src) = arg.locus;
        val atr: Array[Int] = s1 match {
          case E() => rotPerm(1)
          case V() => rotPerm(3)
          case F() => Array(0, 2, 1, 3, 5, 4)
        } //we permute 1 and 2, as well as 4 and 5

        r.c = permute(r.c, atr, e.locus);
        r.algn = composeAll2(atr, r.algn)
        e.copy(arg = newArg)

    }
    newExp.asInstanceOf[ASTL[L, R]]
  }


  /**
   *
   * @param r for computation of all the radius, collect the radius of identifier , plus a modifier making it precise for Edge and Face wether
   *          they are perimeter or radial
   * @param t symbol table to be updated for paramR() to paramRR(Int) where int indicate the radius of result param
   * @return radius and modifier of expression
   */

  override def radiusify3(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): (Int, ASTLt[L, R]) = {


    this.asInstanceOf[ASTLg] match {
      case trans@Transfer(arg, m, n) => {
        def increaseRadius(rad: Int, src: Locus, target: Locus): Int = {
          val newRadius = (src, target) match {
            case (V(), _) | (E(), F()) => rad + 1
            case _ => rad
          }
          if (newRadius >= 2) // we have to do  another communication between radius=1 and radius=-2
            assert(false)
          newRadius
        }

        val (rad, newArg) = arg.radiusify3(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        (increaseRadius(rad, src, target), trans.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      }
      case binop@Binop(_, arg, arg2, _, _) =>
        var (r1, newArg) = arg.radiusify3(r, t)
        var (r2, newArg2) = arg2.radiusify3(r, t)
        assert(r1 == r2 || r1 < 0 || r2 < 0 || Math.abs(r1 - r2) == 1, "binop should processe variables of near identical index i") //todo introduce delays)
        if (r1 < r2 && r1 >= 0) //negative radius means constant
          newArg = increaseRadiuus(newArg)(new repr(newArg.locus), new repr(newArg.ring)) //we augment radius of arg by delaying it
        else if (r2 < r1 && r2 >= 0) //negative radius means constant
          newArg2 = increaseRadiuus(newArg2)(new repr(newArg2.locus), new repr(newArg2.ring)) //we augment radius of arg2 by delaying it
        // if (r1 < r2) for (i <- 0 until r2 - r1) //arg=tm1(arg)
        (math.max(r1, r2), binop.copy(arg = newArg, arg2 = newArg2).asInstanceOf[ASTL[L, R]])
      case Coonst(_, _, _) => (-1000, this) //negative radius means arbitrary radius,
      case u@Unop(op, arg, _, _) =>
        var (rad, newArg) = arg.radiusify3(r, t)
        rad = rad + (if (op.name == "increaseRadius2") 1 else 0)
        (rad, u.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      //for other cases we do nothing
      case b@Broadcast(arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@Redop(_, arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@BinopEdge(_, arg, _, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      case b@RedopConcat(arg, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])
      // case b@Clock(arg, _) =>  val (rad,newArg) = arg.radiusify3(r, t);(rad,b.copy(arg=newArg).asInstanceOf[ASTL[L,R]])
      case b@Sym(arg, _, _, _) => val (rad, newArg) = arg.radiusify3(r, t); (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]])

      case b@Clock(arg, _, _, _, _) => val (rad, newArg) = arg.radiusify3(r, t); //the radius needs to be augmented
        (rad, b.copy(arg = newArg).asInstanceOf[ASTL[L, R]]) //the radius remains the same, just like sym.
      case b@Send(args) => val radNewArgs = args.map(_.radiusify3(r, t));
        val newRad = radNewArgs.map(_._1).reduce(Math.max(_, _))
        val newb = b.copy(args = radNewArgs.map(_._2))(lpart(b.mym), rpart(b.mym))
        (newRad, newb.asInstanceOf[ASTL[L, R]])

    }

  }
  /*
  override def radiusify2(r: TabSymb[Int], t: TabSymb[InfoNbit[_]]): Int = {
    def increaseRadius(rad: Int, src: Locus, target: Locus): Int = {
      val newRadius = (src, target) match {
        case (V(), _) | (E(), F()) => rad + 1
        case _ => rad
      }
      assert(newRadius < 2) // we have to do  another communication between radius=1 and radius=-2
      newRadius
    }

    this.asInstanceOf[ASTLg] match {
      case Coonst(_, _, _) => -1000 //radius is arbitrary
      case Transfer(arg, _, _) => {
        val rad = arg.radiusify2(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        increaseRadius(rad, src, target)
      }
      case Binop(_, arg, arg2, _, _) =>
        val r1 = arg.radiusify2(r, t)
        val r2 = arg2.radiusify2(r, t)
        assert(r1 == r2 || r1 < 0 || r2 < 0, "binop should processe variables of identical index i") //todo introduce delays
        math.max(r1, r2)

      case Unop(op, arg, _, _) =>
        arg.radiusify2(r, t) +
          (if (op.name == "increaseRadius2")
            1
          else 0) //ca ne change pas
      case Broadcast(arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case Redop(_, arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case RedopConcat(arg, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case Clock(arg, _, _, _, _) => arg.radiusify2(r, t) //ca ne change pas
      case Send(args) => args(0).radiusify2(r, t) //ca ne change pas
      case Sym(arg, _, _, _) => arg.radiusify2(r, t) //ca ne change pas
    }

  }



  override def radiusify(r: TabSymb[(Int, Option[Modifier])], t: TabSymb[InfoNbit[_]]): (Int, Option[Modifier]) = {

    /**
     * t
     *
     * @param rad    radius
     * @param m      modifier: Perimeter or Radial
     * @param src    locus of  origin
     * @param target locus of  destination
     * @return transcribes the automata presented in the article,
     *         so as to possibly increase the radius, and update the locus modifier
     *         it seems that now it is obsolete, we replaced radius by radius2
     */
    def increaseRadiusObsolete(rad: Int, m: Option[Modifier], src: Locus, target: Locus): (Int, Option[Modifier]) = {
      val newRadius = (src, m, target) match {
        case (E(), Some(Perimeter()), F()) | // case where the radius does not increase
             (F(), Some(Radial()), E()) | // case where the radius does not increase
             (E(), Some(Radial()), V()) // case where the radius does not increase
        => rad
        case _ => rad + 1
      }
      val newModifier: Option[Modifier] = (src, target) match {
        case (E(), F()) => m
        case (F(), E()) => Modifier.invertModifier(m)
        case (V(), _) => Some(Perimeter())
        case (_, V()) => None
      }
      (newRadius, newModifier)
    }

    this.asInstanceOf[ASTLg] match {
      case Coonst(_, _, _) => startRadius(locus)
      case Transfer(arg, _, _) => {
        val (rad, m) = arg.radiusify(r, t)
        val T(src, target) = arg.locus //we get the source and target locus knowing that arg is a transfer locus
        increaseRadiusObsolete(rad, m, src, target)
      }
      case Binop(_, arg, arg2, _, _) => val (r1, t1) = arg.radiusify(r, t)
        val (r2, t2) = arg2.radiusify(r, t)
        assert(r1 == r2 && t1 == t2, "binop should processe variables of identical radius")
        (r1, t1)
      case Unop(_, arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Broadcast(arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Redop(_, arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case RedopConcat(arg, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Clock(arg, _, _, _, _) => arg.radiusify(r, t) //ca ne change pas
      case Send(args) => args(0).radiusify(r, t) //ca ne change pas
      case Sym(arg, _, _, _) => arg.radiusify(r, t) //ca ne change pas
    }
  }
*/

  override def cost(): Cost = {
    this.asInstanceOf[ASTLg] match { //read and Call treated in ASTLt.
      case Coonst(_, _, _) => Cost(0, true, true)

    }
  }

}