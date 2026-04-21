package compiler

import java.lang.ArrayIndexOutOfBoundsException
import dataStruc.DagNode._
import ASTB.{ParOp, affBoolConst, _}
import ASTBfun.{p, _}
import ASTL.rewriteASTLt
import Circuit.{TabSymb, iTabSymb, iTabSymb2}

import scala.collection._
import scala.collection.immutable.{HashMap, HashSet}
import scala.language.implicitConversions
import AST._
import compiler.ASTBt.checkUISI
import compiler.Packet.{BitLoop, BitNoLoop}

/**
 * node of Abstract Syntax Tree corresponding to an arithmetic field  boolean, integer (signed or unsigned)
 * We wish to be able to preserve covariance of R we couldnot because of progpageASTB.
 */
sealed abstract class ASTB[R <: Ring]()(implicit m: repr[R]) extends ASTBt[R] {

  /** Binary code, LSB at head */
  def toBinary2(n: Int, size: Int): List[ASTB[B]] =
    if (size == 0) List() else (if (n % 2 == 1) True() else False()) :: toBinary2(n / 2, size - 1)

  def extend(n: Int, l: List[ASTBt[B]], v: ASTBt[B]) = l ::: List.fill(n - l.length)(v).asInstanceOf[List[ASTBt[B]]]


  /** return the affbool that label subtrees neares to the root */
  override def affBoolify(): List[ASTBt[B]] = {
    this.asInstanceOf[ASTBg] match {
      case AffBool(n, exp) => List(this.asInstanceOf[ASTBt[B]])
      case _ => inputNeighbors.flatMap(_.asInstanceOf[ASTBt[_]].affBoolify()) //super.affBoolify??
    }
  }

  /**
   *
   * @return number of boolean operators Or, And, Xor, Neg, contained in the expression
   */
  override def totalOp: Int = {
    this.asInstanceOf[ASTBg] match {
      case Neg(_) | Xor(_, _) | Or(_, _) | And(_, _) => 1 + inputNeighbors.asInstanceOf[List[ASTBt[B]]].map(_.totalOp).reduce(_ + _)
      case AffBool(n, exp) => exp.totalOp
      case Shift(exp, b) => exp.totalOp
      case False() => 0
      case True() => 0
      case _ =>
        throw (new Exception("totalOp should be aplied to pure boolean expression"))
    }
  }

  /**
   *
   * @param nl   code generation state variables
   * @param name name of variable being affected
   * @param env  map or scan parameter's expression for index i
   * @return The boolean affectation compiled fro "this"
   */
  override def boolExprNoIndex(nl: BitNoLoop, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    var name2 = name
    val exp = this.asInstanceOf[AST[_]] match {
      case Neg(x) => addNeg(x.boolExprNoIndex(nl, null, env))
      case Xor(x, y) => addXor(x.boolExprNoIndex(nl, null, env), y.boolExprNoIndex(nl, null, env))
      case Or(x, y) => addOr(x.boolExprNoIndex(nl, null, env), y.boolExprNoIndex(nl, null, env))
      case And(x, y) => addAnd(x.boolExprNoIndex(nl, null, env), y.boolExprNoIndex(nl, null, env))
      case Shift(e, b) => Shift(e.boolExprNoIndex(nl, null, env), b)
      case Tminus1(e) => Tminus1(e.boolExprNoIndex(nl, null, env))
      case False() => False()
      case True() => True()
      case _ =>
        throw new Exception("there should be only pure boolean operators here")
    }
    affBoolConst(name2, exp, nl)
  }

  /**
   * this must be of type integer
   *
   * @return names of parameters in exp having same bit size as exp of type ASTB
   */
  override def sameIntBitSize(): Set[String] = {
    if (!(this.ring.isInstanceOf[I])) return HashSet[String]() //we do not consider boolean
    this.asInstanceOf[ASTBg] match {
      case Mapp1(_, x) =>
        x.head.sameIntBitSize()
      case Mapp2(x, y, _) => x.sameIntBitSize().union(y.sameIntBitSize())
      case sc@Scan1(x, _, _, _, _) => x.sameIntBitSize()
      case sc@Scan2(x, y, _, _, _, _) => x.sameIntBitSize().union(y.sameIntBitSize())
      case concat2@ Concat2(_,_) => HashSet()
      case toto@Extend(_,_) =>HashSet()
      case _ =>
        throw new Exception("lets look closer, may be a case is missing but I do not think so")
    }
  }


  /**
   *
   * @param i    current loop index considered
   * @param l    code generation state variables
   * @param name name of variable being affected
   * @param env  map or scan parameter's expression for index i
   * @return The boolean affectation or boolean expression corresponding to the loop index
   *         c'est cuila qui fait le travail de pondre du java a partir d'un ASTB
   */
  override def boolifyForIndexI(i: Int, l: BitLoop, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    var name2 = name
    val exp = this.asInstanceOf[ASTBg] match {
      case Neg(x) => addNeg(x.boolifyForIndexI(i, l, null, env))
      case Xor(x, y) => addXor(x.boolifyForIndexI(i, l, null, env), y.boolifyForIndexI(i, l, null, env))
      case Or(x, y) => addOr(x.boolifyForIndexI(i, l, null, env), y.boolifyForIndexI(i, l, null, env))
      case And(x, y) => addAnd(x.boolifyForIndexI(i, l, null, env), y.boolifyForIndexI(i, l, null, env))
      case Mapp1(op, x) =>
        var newEnv = env + (op.p1.nameP -> x(0).asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env))
        if (x.size > 1) //we must add the second argument if it is present, as xb.
        newEnv = newEnv + (op.name -> x(1).asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env))
        op.arg.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, newEnv)
      case Mapp2(x, y, op) => //il se peut quon rajute un affect et augmente la tsymb
        val newEnv = env + (op.p1.nameP -> x.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env))
        op.arg.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, newEnv)
      case sc@Scan1(x, op: Fundef2R[B], v, _, initUsed) =>
        if (l.firstIter(i) && initUsed) {
          affBoolConst(sc.scanVar, v, l)
/*          v match {
            case Elt(-1,_) => l.readWithConst(sc.scanVar) //grosse entourloupe pour dédoubler le dernier bit dans halfSIsurUI
              //print(l.readWithConst(sc.scanVar))
              //throw new Exception("here")
            case _ => affBoolConst(sc.scanVar, v, l)
          }*/
        } else {
          val firstArg =
            if (l.firstIter(i)) v
            else l.readWithConst(sc.scanVar)
          val iShifted =
            if (initUsed) i - l.step
            else i //takes into account the fact that scan's values are shifted
          val newEnv = env +
            (op.p1.nameP -> firstArg) +
            (op.p2.nameP -> x.asInstanceOf[ASTBt[B]].boolifyForIndexI(iShifted, l, null, env))
          val e = op.arg.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, newEnv)
          if (l.lastIter(i)) e
          else affBoolConst(sc.scanVar, e, l)
        }
      case sc@Scan2(x, y, op: Fundef3R[B], v, _, initUsed) =>
        if (l.firstIter(i) && initUsed)
          affBoolConst(sc.scanVar, v, l)
        else {
          val firstArg =
            if (l.firstIter(i)) v
            else l.readWithConst(sc.scanVar) //sc10 first value vaut zero
          val iShifted =
            if (initUsed) i - l.step
            else i //takes into account the fact that scan's values are shifted
          val newEnv = env +
            (op.p1.nameP -> firstArg) +
            (op.p2.nameP -> x.asInstanceOf[ASTBt[B]].boolifyForIndexI(iShifted, l, null, env)) +
            (op.p3.nameP -> y.asInstanceOf[ASTBt[B]].boolifyForIndexI(iShifted, l, null, env))
          val optimizedOpBody = //when z is true, carry(x,y,z) = x | y which is bychance also   op.arg.inputNeighbors(1).inputNeighbors(1) in the body of carry
            if (op.name.equals("carry") && newEnv(op.p3.nameP).equals(True()))
              op.arg.inputNeighbors(1).inputNeighbors(1)
            else op.arg
          val e = optimizedOpBody.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, newEnv)
          if (l.lastIter(i)) e
          else affBoolConst(sc.scanVar, e, l)
        }
      case Shift(e, b) => Shift(e.boolifyForIndexI(i, l, null, env), b)
      case Tminus1(e) => Tminus1(e.boolifyForIndexI(i, l, null, env))
      case Elt(n, exp) =>
        val newExp = exp.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env)
        val indexElt = if (n == -1) l.loopSize - 1 else n
        if (i == indexElt) AffBool(name, newExp) else if (i != indexElt)
          name2 = null
        newExp
      case Reduce(exp, op, init) =>
        val newExp = exp.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env)
        name2 = name //we allways make an affectation
        val newRedExp =
          if (l.firstIter(i)) newExp
          else {
            val newEnv = env +
              (op.p1.nameP -> new Read(name)(repr(B)) with ASTBt[B]) +
              (op.p2.nameP -> newExp)
            op.arg.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, newEnv)
          }
        newRedExp
      case ex@Extend(n: Int, exp: ASTBg) =>
        val nbitExp = exp.nBit(l.tSymbVar, l.coalesc, env)
        var newExp: ASTBt[B] = null
        if (i < nbitExp) newExp =
          exp.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env)
        if (exp.mym.name == SI() && i == nbitExp - 1)
          affBoolConst(ex.scanVar, newExp, l) //we store the sign bit
        else if (i < nbitExp)
          newExp
        else if (exp.mym.name == UI()) ASTB.False()
        else if (exp.mym.name == SI()) l.readWithConst(ex.scanVar) // sign bit replicates for signed int.
        else
          throw new Exception("extend bordel probably is UISI and we 'd need to know wether it is SI or UI")
      case exp@Intof(value: Int) =>
        val t = exp.mym.name.asInstanceOf[I];
        val nbit = nbitCte(value, t) //depends on wether t is signed or unsigned
        val p = scala.math.pow(2, nbit).toInt;
        try {
          fromBoolB(toBinary(value + (if (value >= 0) 0 else p), nbit)(i))
        }
        catch {
          case e: IndexOutOfBoundsException => throw new Exception("we must have a bug in extends")
        }
      case False() => False()
      case True() => True()
      case co@Concat2(exp1, exp2) =>
        val nbitExp1 = exp1.nBit(l.tSymbVar, l.coalesc, env)
        //val nbitExp2=exp2.nBit(gen,env)
        if (i < nbitExp1)
          exp1.asInstanceOf[ASTBt[B]].boolifyForIndexI(i, l, null, env)
        else
          exp2.asInstanceOf[ASTBt[B]].boolifyForIndexI(i - nbitExp1, l, null, env)
    }
    affBoolConst(name2, exp.asInstanceOf[ASTBt[B]], l)
  }


  override def deCallify(env: HashMap[String, ASTBg]): ASTBg = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.deCallify(env).asInstanceOf[ASTBt[R]]
    propagateASTB(rewrite)
  }


  override def toString: String =
    this.asInstanceOf[ASTB[_]] match {
      case AffBool(nameb, e) =>
        nameb + "=" //+"["
      case Intof(v) => "" + v
      case True() => "truue"
      case False() => "faalse"
      case Concat2(x, y) => "::"
      case Elt(i, x) => "Elt" + i
      case Extend(i, _) => "Extend" + i //+ mym.name
      case Xor(x, y) => "^"
      case Or(x, y) => "|"
      case And(x, y) => "&"
      case Neg(x) => "~"
      case Mapp1(op, x) => "Mapp1" + op.name //+ mym.name
      case Mapp2(x, y, op) => "Mapp2" + op.name //+ mym.name
      case Scan1(x, op, init, dir, _) => "Scan1" + op.name + init + dir //+ mym.name
      case Scan2(x, y, op, _, dir, _) => "Scan2" + op.name + dir //+ mym.name
      case Reduce(x, op, _) => "Red" + op.name
      case Shift(x, right) => (if (right) ">>>" else "<<")
      case Tminus1(x) => "tm1"
    }

  /**
   * @param id rewriting procedure
   * @return ASTB obtained by applying the rewriting recursively
   *         No  override, because name is distinct from AST's propagate */
  def propagateASTB(id: rewriteASTBt[R]): ASTBt[R] = {
    def id2[R3 <: Ring]: rewriteASTBt[R3] = d => id(d.asInstanceOf[ASTBt[R]]).asInstanceOf[ASTBt[R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTBg] match {
      case e: EmptyBag[_] => e
      case e@Xor(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Or(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@And(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Neg(a) => e.copy(arg = id2(a))(e.mym)
      case e@Concat2(a, b) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Elt(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Extend(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Mapp1(_, a) => val newe = e.copy(args = a.map(id2(_)))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        newe
      case e@Mapp2(a, b, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        ;
        newe
      case e@Scan1(a, _, _, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Scan2(a, b, _, _, _, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Reduce(a, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Tminus1(a) => e.copy(arg = id2(a))(e.mym)
      case e@Shift(a, _) => e.copy(arg = id2(a))(e.mym)
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTB[R]]
  }

  /** recursive remove of all tm1, seem to be very odd to do that! */
  override def detm1iseR: ASTBt[R] = {
    def id2[R3 <: Ring]: rewriteASTBt[R3] = d => d.asInstanceOf[ASTBt[R]].detm1iseR.asInstanceOf[ASTBt[R3]] //introduit des variables libres
    val newD = this.asInstanceOf[ASTBg] match {
      case e: EmptyBag[_] => e
      case e@Xor(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Or(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@And(a, b) => e.copy(arg = id2(a), arg2 = id2(b))(e.mym)
      case e@Neg(a) => e.copy(arg = id2(a))(e.mym)
      case e@Concat2(a, b) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Elt(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Extend(_, a) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Mapp1(_, a) => val newe = e.copy(args = a.map(id2(_)))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        newe
      case e@Mapp2(a, b, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym);
        newe.dirNarrowed = e.dirNarrowed;
        ;
        newe
      case e@Scan1(a, _, _, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Scan2(a, b, _, _, _, _) => val newe = e.copy(arg = id2(a), arg2 = id2(b))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Reduce(a, _, _) => val newe = e.copy(arg = id2(a))(e.mym); newe.dirNarrowed = e.dirNarrowed; newe
      case e@Tminus1(a) =>
        id2(a)
      case e@Shift(a, _) => e.copy(arg = id2(a))(e.mym)
    };
    newD.setName(this.name);
    newD.asInstanceOf[ASTBt[R]]
  }

  /** remove the head tm1 */
  override def detm1ise: ASTBt[R] = this match {
    case ASTB.Tminus1(e) =>
      e.name = name; //propagates the name's change should we allways do that
      e
    case _ => this
  }

  override def isTm1 =
    this match {
      case Tminus1(_) => true
      case _ => false
    }

  override def isNotTm1Read =
    this match {
      case Tminus1(x) => AST.isNotRead(x)
      case _ => true
    }

  /** we will not generate an affect for such expression, it cost only the negation operator, we prefer to recompute it */

  override def unfoldInt(t: TabSymb[InfoNbit[_]]): List[ASTBt[B]] =
    this.asInstanceOf[ASTB[_]] match {
    case Elt(nb, arg) =>

      val l = arg.unfoldInt(t)
      if(nb >= l.size)
        throw new Exception("bordelConcatChoose3bitdeprioRand")
      List(l(nb)) //we read the nbth element of the boolean list
    case Concat2(arg1, arg2) => arg1.unfoldInt(t) ::: arg2.unfoldInt(t)
    case True()=>List(True())
    case False()=>List( False())
  }

}

/** static object using arithmetic parse trees, operators gets a name, using another method, with the letter 'n' appended
 * Important CODE CONVENTION: LSB first means that Least significant bit is head of list.
 **/
object ASTB {
  var totalScan = 0
  type rewriteASTBt[R <: Ring] = ASTBt[R] => ASTBt[R]

  /** Direction the pipelining process of integers's bit
   * left means from the least significant bits towards the msb, and   right is the other way round. */
  abstract sealed class Dir {
    def narrowed: Dir;

    def opposite: Dir
  }

  final case class Left() extends Dir {
    val narrowed = this;

    def opposite = Right()
  }

  final case class Right() extends Dir {
    val narrowed = this;

    def opposite = Left()
  }

  final case class Both() extends Dir {
    val narrowed = Left();

    def opposite = throw new Exception("Both has no opposite")
  }


  //______Elementary type
  type Uint = ASTBt[UI];
  type Sint = ASTBt[SI];
  type Bool = ASTBt[B];


  /** Communication Constructors, work for both Booleans and integers  */
  case class Shift[R <: Ring](arg: ASTBt[R], right: Boolean)(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]

  /** All the constructors should be declared private for clean separtion. TMInus1 illustrates how to proceeds in this direction */
  //private[ASTB]
  case class Tminus1[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]


  case class IncreaseRadius[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]


  /** Bolean Constructor */
  //class Bool extends ASTB[B] with EmptyBag[AST[_]]

  final case class True()(implicit n: repr[B]) extends ASTB[B] with EmptyBag[AST[_]] {
    override def isConst = true

  }

  final case class False()(implicit n: repr[B]) extends ASTB[B] with EmptyBag[AST[_]] {
    override def isConst = true

  }

  implicit def toBoolB(d: ASTBt[B]): Boolean = if (d == True()) true else if (d == False()) false else
    throw new Exception("pas boolean")

  /**
   *
   * @param b boolean to be read
   * @return boolean as an ASTB instance
   */
  def fromBoolB(b: Boolean): ASTBt[B] = if (b == true) True() else False()

  // abstract class Op2 extends ASTB[B] with Doubleton[AST[_]]
  final case class Xor(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class And(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Or(arg: ASTBt[B], arg2: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Doubleton[AST[_]] //{assert(y.nbit==x.nbit)}
  final case class Neg(arg: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Singleton[AST[_]]

  /** ¯Boolean Affectation are also considered as  expression ,because an affectation in java does have a value, which is the expresion
   * itself being affected */
  final case class AffBool(nameb: String, arg: ASTBt[B])(implicit n: repr[B]) extends ASTB[B] with Singleton[AST[_]]

  def affBool(nameb: String, arg: ASTBt[B]) = if (nameb == null) arg else AffBool(nameb, arg)


  def affBoolConst(nameb: String, arg: ASTBt[B], g: Packet): ASTBt[B] =
    if (arg.isConst) {
      if (nameb != null) {
        g.constantTable.addOne(nameb -> fromBoolB(arg));
        fromBoolB(arg)    //pas besoin d'affecter pisque la valeur de la variable se trouve dans le tableau de constante le quel sera consulté, en bonne logique! AffBool(nameb, arg)}
      }
      else arg
    } //we need to return the constant because it could be afected to other variable
    else {
      if ((nameb != null) && (g.constantTable.contains(nameb))) g.constantTable.remove(nameb) //variable are reused they can loose their status of bieng constant
      if (nameb == null) arg else AffBool(nameb, arg)
    }

  /** @param dir is a direction. that can be narrowed from both to left or right
   *             ParOp allows to easily computes direction and direction's narrowing if any. */
  abstract class ParOp[R <: Ring](val dir: Dir)(implicit n: repr[R]) extends ASTB[R] {
    /** if dir equals both but a child is rightWard, then we must be obliged to iterate rightward, we register this change in dirNarrowed */
    var dirNarrowed: Dir = dir
  }

  abstract class ParOpScan[R <: Ring](override val dir: Dir)(implicit n: repr[R]) extends ParOp[R](dir) {
    val nb = totalScan;
    totalScan += 1

    def scanVar = "_sc" + nb //fixme j'ai peur que si on apelle deux fois une fonction avec un scan on instancie deux fois le meme scanVar alors que il en faudrait deux distinctes
  }

  /**
   * An oprerator with outputStored must store its result. Reduce and Elt are such.
   **/
  trait OutputStored

  /**
   * An oprerator with inputStored must have its input stored, in order to be able to traverse it several time (binary encode)
   **/
  trait InputStored

  /** returns bit at position i, modulo nbit. Obs: -1 is the index of the last bit. */
  case class Elt[R <: I](i: Int, arg: ASTBt[R])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton[AST[_]] with OutputStored

  case class Reduce[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B])(implicit n: repr[B]) extends ParOp[B](Both()) with Singleton[AST[_]] with OutputStored


  val outputStored: AST[_] => Boolean = (x: AST[_]) => x.isInstanceOf[OutputStored]


  /** Integer Constructor */
  case class Intof[R <: I](value: Int)(implicit n: repr[R]) extends ParOp[R](Both()) with EmptyBag[AST[_]]

  /** used for doing concat reduction */
  case class Concat2[R1 <: Ring, R2 <: Ring, O1 <: I](arg: ASTBt[R1], arg2: ASTBt[R2])(implicit n: repr[O1])
    extends ParOp[O1](Left()) with Doubleton[AST[_]] //on pourrait mettre both, mais faudrait bien ruser, alors

  /** planned to br used, in order to use a single concat to regroup arbitrary many components */
  case class ConcatN[R1 <: Ring, O1 <: I](args: List[ASTBt[R1]])(implicit n: repr[O1])
    extends ParOp[O1](Both()) with Neton[AST[_]]

  /** will copy the msb until nbits are obtained, we inherit parOpScan in order to enjoy a register to store that last bit */
  case class Extend[R <: Ring](i: Int, arg: ASTBt[R])(implicit n: repr[R]) extends ParOpScan[R](Left()) with Singleton[AST[_]]

  /** Iterates on one int */
  case class Mapp1Old[R <: I](arg: ASTBt[R], op: Fundef1[B, B])(implicit n: repr[R]) extends ParOp[R](Both()) with Singleton[AST[_]]

  /**
   * Iterates on one int
   *
   * @param op   operators that iterates
   * @param args arguments the first argument is the integer,there can be also a second argument which is a  boolean used by op
   * @param n    implicit for the scalar type
   * @tparam R scalar type
   */
  case class Mapp1[R <: I](op: Fundef1[B, B], args: List[ASTBt[R]])(implicit n: repr[R]) extends ParOp[R](Both()) with Neton[AST[_]]


  /** iterates on two ints with identical number of bits */
  case class Mapp2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef2[B, B, B])(implicit n: repr[R])
    extends ParOp[R](Both()) with Doubleton[AST[_]] {
    checkUISI(arg, arg2)
    // totoa assert(arg.mym.name == arg2.mym.name, "map2's operand must be both ui or both si in fact not, we can map si to ui");
    // when we define boolean fucntion such as add or eq which works for both.")
  }

  /** iterate on one int, uses a carry */
  case class Scan1[R <: I](arg: ASTBt[R], op: Fundef2R[B], init: ASTBt[B], override val dir: Dir, initUsed: Boolean)(implicit n: repr[R])
    extends ParOpScan[R](dir) with Singleton[AST[_]]

  /** iterate on two ints with identical  number of bits, uses a carry */
  case class Scan2[R <: I](arg: ASTBt[R], arg2: ASTBt[R], op: Fundef3R[B], init: ASTBt[B], override val dir: Dir, initUsed: Boolean)
                          (implicit n: repr[R]) extends ParOpScan[R](dir) with Doubleton[AST[_]]

  /** *****Wrapping *********/
  def tm1[R <: Ring](e: ASTBt[R])(implicit m: repr[R]) = new Tminus1(e)(m) with ASTBt[R]

  def shiftL[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]): Shift[R] = Shift(arg, right = false)

  def shiftR[R <: Ring](arg: ASTBt[R])(implicit n: repr[R]): Shift[R] = Shift(arg, right = true)


  val lnOf2: Double = scala.math.log(2) // natural log of 2
  val Epsilon = 0.00001 //we add epsilon so that an exact power of two needs one bit more.
  def log2(x: Double): Int = scala.math.ceil(scala.math.log(x) / lnOf2).toInt

  /**
   *
   * @param n
   * @param t
   * @return return the minmimum number of bits needed to encode the signed integer n
   */
  def nbitCte(n: Int, t: I): Int = if (n < 0) {
    if (t != SI()) throw new RuntimeException("should be signed integer");
    1 + log2(-n - Epsilon)
  }
  else if (n == 0) 1 //the integer O takes one bit to store
  else log2(n + Epsilon) + (if (t == SI()) 1 else 0)

  /**
   * //TODO memoiser pour ne pas avoir a rappeler 40,000 fois add
   *
   * @param nbitASTBParam    stores the number of bits of parameters which have been passed up to now
   *                         used to evaluate the bit size of expression
   * @param exp              the ASTB we want to know how many bits it has
   * @param paramBitIncrease memorizes the increase of  parameter's bit size, backtrack from parameter to parameter
   *                         all the way to the initial ASTL parameter, so as to find out if one should insert
   *                         an unop Extend operators
   * @return bit size of $exp
   */
  def nbitExpAndParam(nbitASTBParam: immutable.HashMap[AST[_], Int], exp: AST[_],
                      paramBitIncrease: mutable.HashMap[String, Int]): Int = {
    /**
     * records in  paramBitIncrease, parameters that needs to be extended, because they are combined with Ints having more bits.
     *
     * @param x  should be a parameter of the boolean function??
     * @param a1 actual bit size of parameter
     * @param a2 target bit size it should have
     */
    def increaseParamBitSize(x: AST[_], a1: Int, a2: Int): Unit = {
      if (a1 < a2) {
        x match {
          case p: Param[_] => paramBitIncrease += (p.nameP -> a2);
          case _ => throw new RuntimeException("we would like to increase the bit sizeof x but x is not a parameter")
        }
      }
    }

    /**
     *
     * @param x first expression of scan2 or map2
     * @param y second  expression of scan2 or map2
     * @return compute the max bit size of both arguments while  applying  recursively recording of paramBitIncrease deeper down
     */
    def maxArgSize(x: AST[_], y: AST[_]): Int = {
      val (nx, ny) = (nbitExpAndParam(nbitASTBParam, x, paramBitIncrease), nbitExpAndParam(nbitASTBParam, y, paramBitIncrease))
      increaseParamBitSize(x, nx, ny);
      increaseParamBitSize(y, ny, nx);
      math.max(nx, ny)
    }

    /**
     *
     * @param fParamName name of parameter of called function affected with exp
     * @param exp        expression to analyse
     * @return name of parameter of calling function, having the same number of bits as exp.
     *         allows to go one step nearer towards the parameter of the ASTL binop operator
     *         whose one operand need to be extended
     */
    def upwardCorr(fParamName: String, exp: ASTBg) = {
      val upParams = exp.sameIntBitSize()
      val extendedBitSize = paramBitIncrease(fParamName)
      for (p <- upParams)
        paramBitIncrease.addOne(p -> extendedBitSize)
    }

    exp match {
      case Intof(n) => nbitCte(n, exp.mym.name.asInstanceOf[I])
      case True() | False() => 1
      case Call1(f, e) => nbitExpAndParam(nbitASTBParam +
        (f.p1 -> nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)), f.arg, paramBitIncrease)
      case Call2(f, e, e2) =>
        val fp1 = nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)
        val fp2 = nbitExpAndParam(nbitASTBParam, e2, paramBitIncrease)
        val nbitRes = nbitExpAndParam(nbitASTBParam + (f.p1 -> fp1) + (f.p2 -> fp2), f.arg, paramBitIncrease)
        //we must propagate from f.p1 and  f.p2, back to ASTL's binop parameter
        //we look if paramBitInccrease contains parameter's name of f, and if so, tries to convert them to former parameter prsent in nbitASTBParam
        for (fParamName <- paramBitIncrease.keys)
          if (f.p1.nameP == fParamName) //paramBitIncrease will contain all the parameters which should be extended,
          //in fact only the "oldest ancestor" is usefull, it will cause an Extend to be included in the ASTL node
          upwardCorr(fParamName, e.asInstanceOf[ASTBg])
          else if (f.p2.nameP == fParamName)
            upwardCorr(fParamName, e2.asInstanceOf[ASTBg])
        nbitRes
      case Call3(f, e, e2, e3) => //call2 is mainly used for cond, the first arg is a bool
        val fp1 = nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)
        val fp2 = nbitExpAndParam(nbitASTBParam, e2, paramBitIncrease)
        val fp3 = nbitExpAndParam(nbitASTBParam, e3, paramBitIncrease)
        val nbitRes = nbitExpAndParam(nbitASTBParam + (f.p1 -> fp1) + (f.p2 -> fp2) + (f.p3 -> fp3), f.arg, paramBitIncrease)
        //we must propagate from f.p1 and  f.p2, back to ASTL's binop parameter
        //we look if paramBitInccrease contains parameter's name of f, and if so, tries to convert them to former parameter prsent in nbitASTBParam
        for (fParamName <- paramBitIncrease.keys)
          if (f.p1.nameP == fParamName) //paramBitIncrease will contain all the parameters which should be extended,
          //in fact only the "oldest ancestor" is usefull, it will cause an Extend to be included in the ASTL node
            upwardCorr(fParamName, e.asInstanceOf[ASTBg])
          else if (f.p2.nameP == fParamName)
            upwardCorr(fParamName, e2.asInstanceOf[ASTBg])
          else if (f.p3.nameP == fParamName)
            upwardCorr(fParamName, e3.asInstanceOf[ASTBg])
        nbitRes

      case e@Param(_) =>
        nbitASTBParam(e)
      case Neg(x) => nbitExpAndParam(nbitASTBParam, x, paramBitIncrease)
      case Xor(_, _) => 1
      case Or(_, _) => 1
      case And(_, _) => 1
      case Scan1(exp, _, _, _, initused) =>
        nbitExpAndParam(nbitASTBParam, exp, paramBitIncrease) //+ (if (initused) 0 else 0)
      case Scan2(exp, exp2, _, _, _, _) =>
        maxArgSize(exp, exp2)
      case Reduce(_, _, _) => 1 //FIXME doesnot work for the reduction with concat
      case Mapp2(exp, exp2, _) => maxArgSize(exp, exp2)
      case Shift(e, _) => nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)
      case Tminus1(e) => nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)
      case IncreaseRadius(e) => nbitExpAndParam(nbitASTBParam, e, paramBitIncrease)
      case Mapp1(_, expList) => nbitExpAndParam(nbitASTBParam, expList.head, paramBitIncrease)
      //case MappBI(exp, exp2, opp)               => nBitR(nbit, exp2, pm)
      case Elt(_, _) => 1;
      case Concat2(exp, exp2) => nbitExpAndParam(nbitASTBParam, exp2, paramBitIncrease) + nbitExpAndParam(nbitASTBParam, exp, paramBitIncrease) //
      case Extend(n, _) => n
      case Read(x) => throw new Exception("when a boolean expression is evaluated only Param are used, not read")

    }
  }


  /**
   * same as nBitExpandParam, except it does not  memorizes the increase of ASTB parameter's bit size
   *
   * @param nbitASTBParam stores the number of bits of parameters which have been passed up to now
   * @param d             the ASTB we want to know how many bits it has
   * @param t             is set to null if not needed
   * @return bit size of $d
   */
  def nbitExp2(nbitASTBParam: immutable.HashMap[AST[_], Int], d: AST[_], t: TabSymb[InfoNbit[_]], c: iTabSymb[String]): Int = {
    /**
     *
     * @param x first expression of scan2 or map2
     * @param y second  expression of scan2 or map2
     * @return compute the max bit size of both arguments while  applying  recursively recording of paramBitIncrease deeper down
     */
    def maxArgSize(x: AST[_], y: AST[_]): Int = {
      val (nx, ny) = (nbitExp2(nbitASTBParam, x, t, c), nbitExp2(nbitASTBParam, y, t, c))
      math.max(nx, ny)
    }

    d match {
      case Intof(n) => nbitCte(n, d.mym.name.asInstanceOf[I])
      case True() | False() => 1
      case Call1(f, e) => nbitExp2(nbitASTBParam + (f.p1 -> nbitExp2(nbitASTBParam, e, t, c)), f.arg, t, c)
      case Call2(f, e, e2) => nbitExp2(nbitASTBParam + (f.p1 -> nbitExp2(nbitASTBParam, e, t, c)) + (f.p2 -> nbitExp2(nbitASTBParam, e2, t, c)), f.arg, t, c)
      case e@Param(_) => nbitASTBParam(e)
      case Neg(x) => nbitExp2(nbitASTBParam, x, t, c)
      case Xor(_, _) => 1
      case Or(_, _) => 1
      case And(_, _) => 1
      case Scan1(exp, _, _, _, initused) => nbitExp2(nbitASTBParam, exp, t, c) + (if (initused) 0 else 0)
      case Scan2(exp, exp2, _, _, _, _) => maxArgSize(exp, exp2)
      case Reduce(_, _, _) => 1 //FIXME doesnot work for the reduction with concat
      case Mapp2(exp, exp2, _) => maxArgSize(exp, exp2)
      case Shift(e, _) => nbitExp2(nbitASTBParam, e, t, c)
      case Tminus1(e) => nbitExp2(nbitASTBParam, e, t, c)
      case Mapp1(_, expList) => nbitExp2(nbitASTBParam, expList.head, t, c)
      //case MappBI(exp, exp2, opp)               => nBitR(nbit, exp2, pm)
      case Elt(_, _) => 1;
      case Concat2(exp, exp2) => nbitExp2(nbitASTBParam, exp2, t, c) + nbitExp2(nbitASTBParam, exp, t, c) //
      case Extend(n, _) => n
      case Read(x) =>
        if (t.contains(x)) t(x).nb
        else if (c.contains(x) && t.contains(c(x))) t(c(x)).nb
        else
          throw new Exception("where is " + x + "?, it is not found in the symbolTable.  Bug is probably instruction in a dag are not in topological order")
    }
  }


  /**
   *
   * @param t instruction
   * @return direction of instruction
   */
  def instrDirection(t: Any): Option[Dir] = t.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTBg].dir1

  /** Binary code, LSB at head */
  def toBinary(n: Int, size: Int): List[Boolean] =
    if (size == 0) List() else (if (n % 2 == 1) true else false) :: toBinary(n / 2, size - 1)

  /**
   *
   * @param s name of a variable
   * @return true if that variable is a temporary variable introduced in the last stage of compilation.
   */
  def isTmp(s: String): Boolean = s != null && s.startsWith("_") && !s.startsWith("_aux")


  /**
   *
   * @param code1loop binary code of a loop
   * @return names defined in the expression
   */
  def names(code1loop: List[ASTBt[B]]): HashSet[String] = {
    var resDef = HashSet[String]()

    def names(exp: ASTBt[B]): Unit = {
      exp match {
        case AffBool(n, arg) => resDef += n
        case _ =>
      }
      exp.inputNeighbors.map((t: AST[_]) => names(t.asInstanceOf[ASTBt[B]]))
    }

    for (bInst <- code1loop)
      names(bInst)
    resDef
  }


  /**
   *
   * @param code1loop binary code of a loop
   * @return names used in the expression
   */
  def used(code1loop: List[ASTBt[B]]): HashSet[String] = {
    var resUsed = HashSet[String]()

    def used(exp: ASTBt[B]): Unit = {
      exp match {
        case r: Read[ASTBt[B]] =>
          resUsed += r.which
        case _ =>
      }
      exp.inputNeighbors.map((t: AST[_]) => used(t.asInstanceOf[ASTBt[B]]))
    }

    for (bInst <- code1loop) used(bInst)
    resUsed
  }

  /**
   *
   * @param code1loop binary code of a loop
   * @return names defined in the expression , name used in the expression
   */
  def tmpNames(code1loop: List[ASTBt[B]]): (HashSet[String], HashSet[String]) = {
    var resRead = HashSet[String]()
    var resDef = HashSet[String]()

    def tmpNames(exp: ASTBt[B]): Unit = {
      exp match {
        case AffBool(n, arg) =>
          if (isTmp(n)) resDef += n
        case r: Read[ASTBt[B]] =>
          if (isTmp(r.which)) resRead += r.which


        case _ =>
      }
      exp.inputNeighbors.map((t: AST[_]) => tmpNames(t.asInstanceOf[ASTBt[B]]))
    }

    for (bInst <- code1loop)
      tmpNames(bInst)
    (resDef, resRead)
  }

  def isNotMap1Read(iT: collection.Set[AST[_]]): AstPred = {
    case Mapp1(_, x :: _) =>
      AST.isNotRead(x) && (!iT.contains(x))
    case _ =>
      true
  }


  def addNeg(x: ASTBt[B]) = x match {
    case ASTB.False() => ASTB.True()
    case ASTB.True() => ASTB.False()
    case Neg(exp2) => exp2
    case newx@_ => Neg(newx)
  }

  def addXor(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) => y
    case (True(), _) => addNeg(y) // Neg may be further simplified
    case (_, False()) => x
    case (_, True()) => addNeg(x) // Neg may be further simplified
    case _ => Xor(x, y)
  }

  def addAnd(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) | (_, False()) => False()
    case (True(), _) => y
    case (_, True()) => x
    case _ => And(x, y)
  }

  def addOr(x: ASTBt[B], y: ASTBt[B]) = (x, y) match {
    case (False(), _) => y
    case (_, False()) => x
    case (True(), _) | (_, True()) => True() //we  could further simplify the Neg
    case _ => Or(x, y)
  }

}

