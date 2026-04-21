package compiler

import dataStruc.DagNode._
import AST.{Layer, _}
import compiler.ASTBfun.ASTBg
import compiler.ASTL.{ASTLg, delayedL}
import compiler.Circuit.{TabSymb, iTabSymb}
import compiler.VarKind.MacroField
import dataStruc.{DagNode, Named}

import scala.Console.out
import scala.collection._
import scala.collection.immutable.HashSet

/**
 * Represent a field using an Abstract Syntax Tree using
 * Function definition, and calls, reading of variables, delaying of evaluation.
 * Reused to implement
 * 1- the AST of spatial  field (ASTL)
 * 2- the AST of arithmetic field(ASTB)
 *
 * @tparam T type of the expression
 * @param m implicit parameter used to compute this type.
 */
abstract class AST[+T]()(implicit m: repr[T]) extends DagNode[AST[_]] with Named {
  /** @return all the AST's leaves */
  def leaves(): List[AST[_]] =
    if (inputNeighbors.isEmpty) List(this)
    else inputNeighbors.flatMap(_.leaves())

  /**
   *
   */
  val mym: repr[T] = m

  /** @return tabulation for printing instructions returning type T */
  def tabulations = 2

  /** Builds the set of symbols which are read do not consider layer, those represent memory cells to be loaded */
  def symbolsExcepLayers: immutable.HashSet[String] = {
   // println(this +" toto")
    this match {
      case Read(s) => if (Named.isLayer(s)) HashSet() else HashSet(s)
      case Param(s) => HashSet(s)
      case l: Layer[_] => HashSet() //HashSet(l.name)
      case _ => inputNeighbors.map(e => e.symbolsExcepLayers).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
    }
  }

  def symbolsIncludingLayers: immutable.HashSet[String] =
    this match {
      case Read(s) =>  HashSet(s)
      case Param(s) => HashSet(s)
      case l: Layer[_] => HashSet(l.name)
      case _ => inputNeighbors.map(e => e.symbolsIncludingLayers).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
    }

  def symbolsofLayers: immutable.HashSet[String] =
    this match {
      case Read(s) => if (Named.isLayer(s)) HashSet(s) else HashSet()
      case Param(s) => HashSet()
      case l: Layer[_] => HashSet(l.name) //HashSet(l.name)
      case _ => inputNeighbors.map(e => e.symbolsofLayers).foldLeft(HashSet.empty[String])((x, y) => x.union(y))
    }
  /*
    /**
     * OBSOLETE  I keep it here because of the  interesting implementation
     *
     * @param t stores how many times a parameter is used.
     * @return
     */

    def paramUsed(t: TabSymb[Int]): Unit =
      this match {
        case Param(s) => if (t.contains(s)) t.addOne(s -> (t(s) + 1)) else t.addOne(s -> 1)
        case _ => inputNeighbors.map(_.paramUsed(t))
      }
  */
  /**
   * @return textual representation of tree
   */
  override def toString: String =
    this.asInstanceOf[AST[_]] match {
      case Read(s) => s //+ mym.name
      case Param(s) => "Param " + s
      // case f: Fundef[_]      => "Fundef " + f.namef + " of param " + f.p.map(p => p.nameP).foldLeft("")(_ + ", " + _)
      case c: Call[_] =>
        "Call " + c.f.name + " " //  + mym.name
      case Heead(_) => "head"
      case Taail(_) => "tail"
      case Cons(_, _) => "cons"
      case Delayed(arg) => "Delayed"
      case l: Layer[_] =>
        "Layer2 " + this.name + ":" + mym.name
      case _ => throw new RuntimeException("merdouille")
    }


  /**
   *
   * @param i instruction where expression this was found. depending if it callProc or Affect, the processing will nt
   *          be the same
   * @param t the symbol table, it needs to be modified by transforming MacroFields, into StoredField
   * @return effective arguments of call which needs to be affectize
   *         we will not affectize combination of broadcast, elt and read ,
   *         carefull: for args of call which are not such a combination, but are variables,
   *         their kind  must still be changed from macroField to Stored field
   */
  def nonConcatOrBroadcastCallArg(i: Instr, t: mutable.HashMap[String, InfoType[_]]): List[AST[_]] = this.asInstanceOf[AST[_]] match {
    case e: EmptyBag[AST[_]] =>
      if (i.isInstanceOf[CallProc]) //this should be storedFieldified, because it is the expr of a callProc
         if (e.name != null)
        if (t(e.name).k == MacroField())
          t.addOne(e.name -> t(e.name).storedFieldise)
      List() //+ mym.name
    case c: Call[_] =>
      val (simple, complex) = c.args.partition(_.asInstanceOf[ASTL.ASTLg].justConcatsorBroadcast)
      val formerMacroFields = simple.flatMap(_.leaves()).filter((a: AST[_]) =>
        t.contains(a.name) && t(a.name).k == MacroField()).toSet
      for (f <- formerMacroFields)
        t.addOne(f.name -> t(f.name).storedFieldise)
      complex.toList ++ inputNeighbors.flatMap(_.nonConcatOrBroadcastCallArg(null, t))
    case Heead(_) => List()
    case Taail(_) => List()
    case Cons(_, _) => List()
    case _ => inputNeighbors.flatMap(_.nonConcatOrBroadcastCallArg(null, t))
  }

  /**
   * Treefy must be written also for AST because  Coons are AST but not ASTLt[L,R]
   *
   * @param usedTwice dags which are used twice, or which need to be affected for some other reason.
   * @param idRepr    :id of representant of the equivalence class with respect to equal on case class hierarchy
   * @return transformed tree  with preserved T type, for type checking consistency
   *         where delayed are removed, and expression usedTwice are replaced by read.
   *         transformation is applied on the whole tree, so subtree verifying usedTwice will form an independant family  */

  def setReadNodeRemoveDelayed(usedTwice: AstPred, idRepr: Map[AST[_], String]): AST[T] = {
    val rewrite: AST[T] => AST[T] = (d: AST[T]) => d.setReadNodeRemoveDelayed(usedTwice, idRepr)
    if (usedTwice(this)) new Read[T](idRepr(this))(mym.asInstanceOf[repr[T]])
    else this.propagate(rewrite)
  }


  /**
   * @param id1 a bijection betwee AST
   * @return recreates the whole structure   to avoid   side-effect. because we build List, using Coons, Heead, Taail,
   *         the  Call can be of type AST and not ASTLt, as heead, and taail.  therefore we need propagate on AST
   */
  def propagate(id1: rewriteAST[_]): AST[T] = {
    val id = id1.asInstanceOf[rewriteAST[T]] //if I put this type  bij2[T] directly for the parameter id1, it breaks covariance.
    def id2[T3]: rewriteAST[T3] = d => id(d.asInstanceOf[AST[T]]).asInstanceOf[AST[T3]] //introduit des variables libres
    val newD = this.asInstanceOf[AST[_]] match {
      case Read(_) => this //throw  new RuntimeException("Deja dedagifié!" )
      case e: EmptyBag[_] => e
      //case Delayed(arg) => id2(arg()) //the useless delayed node is supressed Delayed are now ASTLt

      case e@Heead(a) => e.copy(arg = id2(a))(e.mym) //{ e.substitute(a,id2(a));e }//{e.arg = id2(a);e} //
      case e@Taail(a) => e.copy(arg = id2(a))(e.mym)
      case e@Cons(a, a2) => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e@Call1(_, a) => e.copy(arg = id2(a))(e.mym)
      case e@Call2(_, a, a2) => e.copy(arg = id2(a), arg2 = id2(a2))(e.mym)
      case e@Call3(_, a, a2, a3) => e.copy(arg = id2(a), arg2 = id2(a2), arg3 = id2(a3))(e.mym)
    }
    newD.setName(this.name)
    newD.asInstanceOf[AST[T]]
  }


  def isNotTm1Read: Boolean = if (isInstanceOf[ASTBt[_]]) asInstanceOf[ASTBt[_]].isNotTm1Read else true

  def isRead: Boolean = if (isInstanceOf[ASTBt[_]]) asInstanceOf[ASTBt[_]].isNotTm1Read else true
}

object AST {
  /*
    /** static function, analyse exps of callProc instructions, for affectizing, as well as exp of Call expression, the same processing holds */
    def nonConcatOrBroadcastCallorCallProc(argsOrExps: List[AST[_]], t:TabSymb[InfoType[_]] )={
      val (simple, complex)= argsOrExps.partition(_.asInstanceOf[ASTL.ASTLg].justConcatsorBroadcast)
      val formerMacroFields =simple.flatMap(_.leaves()).filter((a:AST[_])=>t(a.name).k==MacroField()).toSet
      for(f<-formerMacroFields)
        t.addOne(f.name->t(f.name).storedFieldise)
      complex.toList ++ argsOrExps.map(_.inputNeighbors.flatMap(_.nonConcatOrBroadcastCallArg(t)))
    }*/


  /** Predicate on ASTs */
  type AstPred = AST[_] => Boolean
  /** Predicate on ASTs true when not read */
  val isNotRead: AstPred = {
    case AST.Read(_) => false;
    case _ => true
  }



  val isRead: AstPred = {
    case AST.Read(_) => true
    case _ => false
  }
  /** Predicate on ASTs true for Cons related constructor */
  val isCons: AstPred = {
    case Taail(_) | Heead(_) | Call1(_, _) | Call2(_, _, _) | Call3(_, _, _, _) => true;
    case _ => false
  }

  def or(a1: AstPred, a2: AstPred) = (a: AST[_]) => a1(a) | a2(a)

  def and(a1: AstPred, a2: AstPred) = (a: AST[_]) => a1(a) & a2(a)

  type rewriteAST[U] = AST[U] => AST[U]
  type rewriteAST2 = AST[_] => AST[_]

  /** There is not ASTLt type for Coons.  */
  case class Cons[Thead, Ttail](arg: AST[Thead], arg2: AST[Ttail])(implicit n: repr[(Thead, Ttail)]) extends AST[(Thead, Ttail)] with Doubleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Thead]]; def setArg2(a: AST[_]) = arg2 = a.asInstanceOf[AST[Ttail]] }
  case class Heead[Thead](arg: AST[(Thead, _)])(implicit n: repr[Thead]) extends AST[Thead] with Singleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Tuple2[Thead, _]]]; }
  case class Taail[Ttail](arg: AST[(_, Ttail)])(implicit n: repr[Ttail]) extends AST[Ttail] with Singleton[AST[_]] //{ def setArg(a: AST[_]) = arg = a.asInstanceOf[AST[Tuple2[_, Ttail]]]; }

  abstract class Fundef[+T](namef: String, var body: AST[_], val p: Param[_]*) extends Named {
    name = namef
  } //no need to store the type of f's body at the level of fundef
  case class Fundef0[+To1](s: String, arg: AST[To1]) extends Fundef[To1](s, arg)

  case class Fundef1[+Ti1, +To1](s: String, arg: AST[To1], p1: Param[Ti1]) extends Fundef[To1](s, arg, p1)

  case class Fundef2[+Ti1, +Ti2, +To1](s: String, arg: AST[To1], p1: Param[Ti1], p2: Param[Ti2]) extends Fundef[To1](s, arg, p1, p2)

  case class Fundef3[+Ti1, +Ti2, +Ti3, +To1](s: String, arg: AST[To1], p1: Param[Ti1],
                                             p2: Param[Ti2], p3: Param[Ti3]) extends Fundef[To1](s, arg, p1, p2, p3)
  case class Fundef4[+Ti1, +Ti2, +Ti3,+Ti4, +To1](s: String, arg: AST[To1], p1: Param[Ti1],
                                             p2: Param[Ti2], p3: Param[Ti3], p4: Param[Ti4]) extends Fundef[To1](s, arg, p1, p2, p3, p4)

  //on peut pas utiliser fundefn, car faudrait savoir a l'avance le nombre de paramétres, pour maj l'environnement.
  //case class Fundefn[Ti1, To1](override val namef: String, arg: AST[To1], pn: Param[Ti1]*)(implicit n: repr[To1])  extends Fundef[To1](namef, arg, pn: _*)
  case class Param[+T](nameP: String)(implicit n: repr[T]) extends AST[T] with EmptyBag[AST[_]] {
    name = nameP;
  }

  // @TODO we should not import compiler._, and find a way to use parameter with IntV rather than [V,SI]
  /** Creates a parameter for macro */
  def pL[L <: Locus, R <: Ring](name: String)(implicit n: repr[L], m: repr[R]) = new Param[(L, R)](name) with ASTLt[L, R]

  /** Replace call1, call2, call3, after the nbit stage */
  abstract class Call[T](val f: Fundef[T], val args: AST[_]*)(implicit n: repr[T]) extends AST[T]

  //final case class Multop[L <: Locus, R1 <: Ring, R2 <: Ring](op: Seq[ASTB[R1]] => ASTB[R2], var args: Seq[ASTLtrait[L, R1]], m: repr[L], n: repr[R2])
  //   extends ASTL[L, R2]()(repr.nomLR(m,n)) with Neton[AST[_]] { def setArgs(a: Seq[AST[_]]) = args = a.asInstanceOf[Seq[ASTLtrait[L, R1]]] }
  case class Call1[Ti1, To1](override val f: Fundef1[Ti1, To1], arg: AST[_ <: Ti1])(implicit n: repr[To1])
    extends Call[To1](f, arg) with Singleton[AST[_]]

  case class Call2[Ti1, Ti2, To1](override val f: Fundef2[Ti1, Ti2, To1], arg: AST[_ <: Ti1], arg2: AST[_ <: Ti2])(implicit n: repr[To1])
    extends Call[To1](f, arg, arg2) with Doubleton[AST[_]]

  case class Call3[Ti1, Ti2, Ti3, To1](override val f: Fundef3[Ti1, Ti2, Ti3, To1], arg: AST[_ <: Ti1], arg2: AST[_ <: Ti2], arg3: AST[_ <: Ti3])(implicit n: repr[To1])
    extends Call[To1](f, arg, arg2, arg3) with Tripleton[AST[_]]

  case class Call4[Ti1, Ti2, Ti3, Ti4, To1](override val f: Fundef4[Ti1, Ti2, Ti3, Ti4, To1], arg: AST[_ <: Ti1], arg2: AST[_ <: Ti2], arg3: AST[_ <: Ti3], arg4: AST[_ <: Ti4])(implicit n: repr[To1])
    extends Call[To1](f, arg, arg2, arg3, arg4) with Tripleton[AST[_]]

  case class Read[T](which: String)(implicit m: repr[T]) extends AST[T]() with EmptyBag[AST[_]]

  /**
   * The Depth First Search  algo gathering DagNodes visits recursively all Delayed node of an  AST  as soon as they are created, because
   * the delayed expression is an inputNeighbor of the Delayed node.
   * Thereafter, treeIfy will remove them.
   * Delayed uses a trick found on the net, to have a call by name, together with a case class necessary to make the match
   *
   * @param _arg delayed expression   */
  case class Delayed[T](_arg: () => AST[T])(implicit m: repr[T]) extends AST[T]() with Singleton[AST[_]] {
    lazy val arg: AST[_] = _arg()
  }

  /**
   *
   * @param _arg call by name
   * @param m
   * @tparam T
   * @return Delayed AST noe"
   */
  def delayed[T](_arg: => AST[T])(implicit m: repr[T]): AST[T] = {
    lazy val delayed = _arg;
    new Delayed[T](() => delayed)
  }

  /** Strate are field defined at t and t+1 */
  trait OldStrate[T] {
    self: AST[T] => //a strate is an AST
    /** the value at t, is the strate itself, it represent the value at time t , not sure about that! I think this hold only for layers*/
    val pred: AST[T]
    val next: AST[T] //next remains to be defined.
  }


  /**
   * @param nbit the number of bits
   * @param init the method used to initialize the layer, set to global if left open
   * @tparam T
   * Unlike other constructors,  Layer is not defined as a case class,
   * otherwise equality would allways hold between any two layer of identical bit size
   * Layer is an AST constructor, because it is used both in ASTL and ASTB
   * it stores system instructions. it is a strate, the pred value is itelsf.
   **/
  abstract class Layer[T](val nbit: Int, val init: String)(implicit m: repr[T]) extends AST[T]()
    with EmptyBag[AST[_]] //with Strate[T]
    {
    /** avoid a scala bug */
    val predd/*: AST[T] */= this;
      val next:AST[T]
    val v2 = 1
    assert(nbit == 1 || !this.asInstanceOf[ASTLg].ring.isInstanceOf[B], "a boolean is on one bit") //we check that if it is boolean, nbit=1

    /** system instruction for rendering,debuging,memorizing  can be associated to layers, so as to be latter retrieved during compilation */
    private var sysInstr: List[CallProc] = List.empty;

    /** needed to visite the next fields */
   // override def other: List[AST[_]] = next :: super.other

    /** @param v field to be displayed   */
    protected def show(v: AST[_]*) = {
      for (f <- v)
        sysInstr ::= CallProc("show", List(), List(f))
    }
      def showText(v: AST[_],ls:List[String])={
       sysInstr ::= CallProc("show", List(), List(v))
        Circuit.labelsOfFieldsBeforeName=Circuit.labelsOfFieldsBeforeName + ((v , ls))
      }
      def showt(vs: AST[_]*)= {
        for (v <- vs) showText(v, List())
      }

    /** @param v field that should be false everywere unless a bug appears */
    def bugif(v: AST[_]) = sysInstr ::= CallProc("bug", List(), List(v))

    /** @return all the user system call, plus the memorized call which is automatically added
     *          must be launched after seting names */
    def oldDystInstr: List[CallProc] = CallProc("memo", List(Named.lify(name)), List(next)) :: sysInstr

      /** returns all the sysInstr plus the memo instruction */
    def systInstr: List[CallProc] = {
      val normal = CallProc("memo", List(Named.lify(name)), List(next)) :: sysInstr
      assert(sysInstr.toSet.size == sysInstr.size, "probably we show several time the same field")
      next match {
        case u@Delayed(x) =>
          if (u.arg == this) return sysInstr //next is ourself, so this is a constant layer, so we do not need memo instructions
        case _ =>
      }
      normal
    }
  }
}

