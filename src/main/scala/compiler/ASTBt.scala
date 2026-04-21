package compiler

import AST.{AstPred, Call1, Call2, Call3, Delayed, Fundef, Fundef1, Fundef2, Fundef3, Layer, Param, Read}
import ASTB.{And, Dir, Extend, False, Intof, Mapp2, Or, ParOp, Scan1, Scan2, Tminus1, True, Xor, nbitCte, rewriteASTBt, _}
import ASTBfun.{ASTBg, Fundef2R}
import ASTL.rewriteASTLt
import Circuit.{TabSymb, iTabSymb, iTabSymb2}

import scala.collection.{Map, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import Array._
import compiler.ASTBt.checkUISI
import compiler.Packet.{BitLoop, BitNoLoop}
import dataStruc.Named


object ASTBt {
  type BB = ASTBt[B]
  /** stores for each function, the parameter having the same number of bits as the result */
  private var paramSameBitSizeMem: mutable.HashMap[String, Set[String]] = mutable.HashMap()

  /**
   *
   * @param f next function to consider
   * @return int parameter of f, whose number of bits is equal to the number of bit of f's result
   *         we use a table  paramSameBitSize in order to avoid recomputing the value all the time
   */
  // private[ASTBt]
  def paramSameBitSize(f: Fundef[_]): Set[String] = {
    if (!paramSameBitSizeMem.contains(f.name))
      paramSameBitSizeMem.addOne(f.name -> (f.body.asInstanceOf[ASTBt[_]].sameIntBitSize()))
    paramSameBitSizeMem(f.name)
  }

  def checkUISI(effectivPar: AST[_], opPar: AST[_]) =
    if (effectivPar.mym.name != opPar.mym.name && effectivPar.mym.name != B() /*&& opPar.mym.name!=B()*/)
      throw new Exception("Faut preserver SI ou UI")
}

/** Identifies AST corresponding to int or bool, excludes those obtained with cons */
trait ASTBt[+R <: Ring] extends AST[R] with MyOpB[R] with MyOpIntB[R] {
  self: AST[R] =>


  def isConst = false



  /** return the affbool that label subtrees nearest to the root */
  def affBoolify(): List[ASTBt[B]] = {
    inputNeighbors.flatMap(_.asInstanceOf[ASTBt[_]].affBoolify())
  }

  /**
   * this must be of type integer
   *
   * @return names of parameters in exp having same bit size as exp, of type AST
   */
  def sameIntBitSize(): Set[String] = {
    var res: Set[String] = HashSet()
    this.asInstanceOf[AST[_]] match {
      case Param(namep) =>
        res = HashSet(namep)
      case Call1(f, arg) =>
        val fparams = ASTBt.paramSameBitSize(f)
        if (fparams.contains(f.p1.nameP))
          res = (arg.asInstanceOf[ASTBt[_]].sameIntBitSize())
      case Call2(f, arg, arg2) =>

        val fparams = ASTBt.paramSameBitSize(f)
        if (fparams.contains(f.p1.nameP))
          res = res.union(arg.asInstanceOf[ASTBt[_]].sameIntBitSize())
        if (fparams.contains(f.p2.nameP))
          res = res.union(arg2.asInstanceOf[ASTBt[_]].sameIntBitSize())
    }
    res
  }

  /**
   *
   * @param i    current loop index considered
   * @param l    code generation state variables
   * @param name name of variable being affected
   * @param env  map or scan parameter's expression for index i
   * @return The boolean affectation or boolean expression corresponding to the loop index
   */
  def boolifyForIndexI(i: Int, l: BitLoop, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    val exp = this.asInstanceOf[AST[_]] match {
      case u@Param(_) => env(u.nameP)
      case Read(x) => l.readAtIndex(x, i, env)
    }
    affBoolConst(name, exp, l)
  }

  /**
   *
   * @return number of boolean operators Or, And, Xor, Neg, contained in the expression
   */
  def totalOp: Int =
    this.asInstanceOf[AST[_]] match {
      case u@Param(_) => 0
      case Read(x) => 0
      case _ => 0
    }

  def boolExprNoIndex(nl: BitNoLoop, name: String, env: HashMap[String, ASTBt[B]]): ASTBt[B] = {
    val exp = this.asInstanceOf[AST[_]] match {
      case u@Param(_) => env(u.nameP)
      case Read(x) => nl.read(x)
    }
    affBoolConst(name, exp, nl)
  }

  def ring: R = mym.name

  /** Remove the first tm1 */
  def detm1iseR: ASTBg = {
    this.asInstanceOf[AST[_]] match {
      case Read(_) => this
      case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBt[_]].detm1iseR)(mym) with ASTBt[R]
      case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
        a.asInstanceOf[ASTBt[R]].detm1iseR,
        a2.asInstanceOf[ASTBt[R]].detm1iseR)(mym) with ASTBt[R]
      case _ =>
        throw new Exception("on devrait traiter ca la ")

    }
  }

  /** remove the head tm1 */
  def detm1ise: ASTBt[R] = this

  /** sinon y a une erreur du compilo scala empty modifier. */
  val u = 3;
  val v = 3

  /** return the direction if there is one */
  def dir1: Option[Dir] = if (isInstanceOf[ParOp[_]]) Some(asInstanceOf[ParOp[_]].dirNarrowed)
  else if (isInstanceOf[Read[_]]) Some(Both())
  else None

  /**
   *
   * @param env used to store parameter's value
   * @return we evaluate all the calls and only the calls,
   *         this will produce a big pure ASTB DAG, which will need an affectify, after that, it will give an idea of what is there.
   **/
  def deCallify(env: HashMap[String, ASTBg]): ASTBg =
    this.asInstanceOf[AST[_]] match {
      case Read(x) =>
        this.asInstanceOf[ASTBt[B]]
      case u@Param(_) => env(u.nameP) //soit un read soit un readscalar soit un affectscalar suivant la nature du parametre
      case Call1(op, x) => //il se peut quon rajoute un affect et augmente la tsymb au lieu d' augmenter l'environnement
        //we check that x 's type is a subtype of the paramater
        // we dlike to write something like that op.p1.mym=x.mym if op is element we do not check because concat produces boolean instead of uint
        if (x.mym.name != op.p1.mym.name && !op.name.startsWith("elt") && !op.name.startsWith("notNull")   ) /*|op.name.startsWith("orScanRight")*/
          throw new Exception("Faut preserver SI ou UI")
        val newEnv = env + (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv)
      case Call2(op, x, y) => //il se peut quon rajute un affect et augmente la tsymb
        if (!op.name.equals("concat2")&& !op.name.equals("concaat2")) {
          checkUISI(x, op.p1); checkUISI(y, op.p2)
        } //for concat2 param can be V or UI or UISI;

        // if ((x.mym.name != op.p1.mym.name && op.p1.mym.name != UISIB()) || (y.mym.name != op.p2.mym.name && op.p2.mym.name != UISIB()))
        //null//totoa throw new Exception("Faut preserver SI ou UI")
        val newEnv = env +
          (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBg].deCallify(env))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv)
      case Call3(op, x, y, z) => //il se peut quon rajoute un affect et augmente la tsymb
        val newEnv = env +
          (op.p1.nameP -> x.asInstanceOf[ASTBg].deCallify(env)) +
          (op.p2.nameP -> y.asInstanceOf[ASTBg].deCallify(env)) +
          (op.p3.nameP -> z.asInstanceOf[ASTBg].deCallify(env))
        op.arg.asInstanceOf[ASTBg].deCallify(newEnv)
    }

  /**
   *
   * @param newName correspondance towards scalar names
   * @return same tree except target is replaced by src   */

  def coalesc(newName: iTabSymb[String]): ASTBt[R] = {
    val u = 0
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.coalesc(newName)
    val newD: ASTBt[R] = this match {
      case a: ASTB[R] => a.asInstanceOf[ASTB[_]] match {
        case AffBool(x, exp) => AffBool(newName.getOrElse(x, x), exp.coalesc(newName)).asInstanceOf[ASTBt[R]]
        case _ => a.propagateASTB(rewrite)
      }
      case _ => this.asInstanceOf[AST[_]] match {
        case Read(x) =>
          if (!newName.contains(x)) this
          else new Read[R](newName(x))(mym) with ASTBt[R]
        //the copy calls done by AST'propagate will preserve the trait ASTBt[R]===>NOT
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBt[_]].coalesc(newName))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBt[R]].coalesc(newName),
          a2.asInstanceOf[ASTBt[R]].coalesc(newName))(mym) with ASTBt[R]
        case _ =>
          throw new Exception("merdouille")
        // case _ => (this.propagate((d: AST[R]) => d.asInstanceOf[ASTBt[R]].coalesc(newName).asInstanceOf[AST[R]])).asInstanceOf[ASTBt[R]]
      }
    }
    newD.asInstanceOf[ASTBt[R]]
  }

  /**
   * Important to specify that the L,R type of AST nodes is preserved, for type checking consistency
   * Surprisingly, when building ASTL explicitely, we need to drop the fact that the type is preserved,
   * and go from ASTL[L,R] to ASTLg
   * Transform a Dag of AST into a forest of trees, removes the delayed.
   *
   * @return the Dag where expression used more than once are replaced by read.
   *         generates ASTs such as READ that preserve the implementation of  ASTLscal by using "with"
   */
  override def setReadNodeRemoveDelayed(usedTwice: AstPred, repr: Map[AST[_], String]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.setReadNodeRemoveDelayed(usedTwice, repr)
    val newD: ASTBt[R] = if (usedTwice(this)) new Read[R](repr(this))(mym) with ASTBt[R]
    else this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case Param(_) => new Read[R]("p" + repr(this))(mym) with ASTBt[R]
        case l: Layer[_] => (new Read[R](Named.lify(repr(this)))(mym) with ASTBt[R])
        case Read(_) => this //throw new RuntimeException("Deja dedagifié!")
        case Delayed(arg) => //arg.asInstanceOf[ASTLt[L, R]].propagate(rewrite)
          arg().asInstanceOf[ASTBt[R]].setReadNodeRemoveDelayed(usedTwice, repr) //the useless delayed node is supressed
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBg].setReadNodeRemoveDelayed(usedTwice, repr))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBg].setReadNodeRemoveDelayed(usedTwice, repr),
          a2.asInstanceOf[ASTBg].setReadNodeRemoveDelayed(usedTwice, repr))(mym) with ASTBt[R]
      }
    }
    newD.setName(if (repr.contains(this)) repr(this) else this.name);
    newD.asInstanceOf[ASTBt[R]]
  }

  /** */
  def simplify(usedOnce: Set[String], defs: Map[String, Instr]): ASTBt[R] = {
    val rewrite: rewriteASTBt[R] = (d: ASTBt[R]) => d.simplify(usedOnce, defs)
    this match {
      case a: ASTB[R] => a.propagateASTB(rewrite)
      case _ => this.asInstanceOf[AST[_]] match {
        case r@Read(x) =>
          if (usedOnce.contains(x)) {
            val newr = defs(x).exps(0).asInstanceOf[ASTBt[R]]
            newr.name = r.name
            newr
          }
          else this
        case Call1(f, a) => new Call1(f.asInstanceOf[Fundef1[Any, R]], a.asInstanceOf[ASTBg].simplify(usedOnce, defs))(mym) with ASTBt[R]
        case Call2(f, a, a2) => new Call2(f.asInstanceOf[Fundef2[Any, Any, R]],
          a.asInstanceOf[ASTBg].simplify(usedOnce, defs),
          a2.asInstanceOf[ASTBg].simplify(usedOnce, defs))(mym) with ASTBt[R]
      }
    }
  }

  def isTm1: Boolean = false

  def isMap1Read: Boolean = false

  override def isNotTm1Read: Boolean = true

  /** returns the set of tree whose father  iterates the list of bits forming the integer,
   * in the inverse direction i.e. dirNarrowed goes
   * from leftward to rightward or from rightward to leftward
   * also narrows the direction if needed otherwise leave direction as Both
   * it is possible that the expression starts with non parop.
   * we should then return the set of trees whose father is nonparop */
  def SetDirAndReturnChangedDir(): Set[ASTBg] = {
    var r: HashSet[ASTBg] = HashSet.empty
    var dirs: HashSet[Dir] = HashSet.empty
    if (isInstanceOf[ParOp[_]]) {
      val me = asInstanceOf[ParOp[_]]
      val myDir = me.dirNarrowed
      dirs = HashSet(myDir)
    }

    for (s <- inputNeighbors) {
      r = r.union(s.asInstanceOf[ASTBg].SetDirAndReturnChangedDir()) //retrieves already found inverted directions
      if (s.isInstanceOf[ParOp[_]])
        dirs = dirs + s.asInstanceOf[ParOp[_]].dirNarrowed //dirs contains the narrowed dir of the children
    }
    if (isInstanceOf[ParOp[_]]) {
      val me = asInstanceOf[ParOp[_]]
      val myDir = me.dirNarrowed //c'est lourds, je répéte
      if (dirs.contains(ASTB.Left()) && dirs.contains(ASTB.Right())) { // I added the filtering very recently
        r = r ++ inputNeighbors.filter(_.isInstanceOf[ParOp[_]]).filter(_.asInstanceOf[ParOp[_]].dirNarrowed == myDir.narrowed.opposite).asInstanceOf[List[ASTBg]]
        me.dirNarrowed = myDir.narrowed
      }
      else if (dirs.contains(ASTB.Left()))
        me.dirNarrowed = ASTB.Left()
      else if (dirs.contains(ASTB.Right()))
        me.dirNarrowed = ASTB.Right()
    }
    r
  }



  /**
   * THIs is an Integer expression, as opposed to a boolean expression.
   *
   * @param t   symbolTable with bitsize
   * @param env ""Contains expression of parameters ""
   * @param c   coalesced registers
   * @return the number of bits used by the expression
   */
  def nBit(t: TabSymb[InfoNbit[_]], c: iTabSymb[String], env: HashMap[String, ASTBt[B]]): Int = {
    val paramBitSize = immutable.HashMap[AST[_], Int]() ++ //comutes the bit size of the parameters
      env.map((f: (String, ASTBt[B])) => (Param(f._1)(repr(f._2.ring)) -> (f._2.nBit(t, c, env))))
    nbitExp2(paramBitSize, this, t, c)
  }


  /**
   *
   * @param t symbol table used to check the bit size of int
   * @return transform an int expression in a list of bool expression, the size of the list is the bit size
   */
  def unfoldInt(t: TabSymb[InfoNbit[_]]): immutable.List[ASTBt[B]] = this.asInstanceOf[AST[_]]
  match {
    case Read(which) =>
      if(!t.contains(which))
        throw new Exception("t(which)")
      if (t(which).t == B()) List(this.asInstanceOf[ASTBt[B]]) else //nothing to do, it's already OK
        Instr.deployInt2(which, t(which)).map((s: String) => new Read(s)(repr.nomB) with ASTBt[B])
  }

}


