package dataStruc

import compiler.AST.Read
import compiler.ASTB.{AffBool, False, True}
import compiler.{AST, ASTB, Affect, DataProg, InfoType}
import compiler.Circuit.TabSymb
import dataStruc.Util.{radicalOfVar, radicalOfVar2}
import dataStruc.DagNode.Neton

import scala.collection.{Iterable, immutable, mutable}

/**
 * Node of a Directed Acyclic Graph (DAG)
 * getCycle is used to test the absence of cycles
 * getGreater is used to collect all the nodes of a Dag,
 * whose set of minimum is passed or completed on the fly
 * neighbor is   an edge used with depth first search,
 * other is not an edge. It points to other nodes to explore the whole DAG
 * to complete on the fly an initial set of minimals
 */
trait DagNode[+T <: DagNode[T]] {
  //self: T =>
  def inputNeighbors: List[T]

  /** others are node that should be visited, but are not input neighbors.
   * by default there is none */
  //def other: List[T] = List.empty

  /** we print without parenthesis when there is a single input */
  def toStringTree: String ={
    //   println("toatoa")
    toString + " " +
      (if (inputNeighbors.size > 1 || this.isInstanceOf[Neton[_]])
        "(" + inputNeighbors.map(_.toStringTree).foldLeft("")(_ + ", " + _).substring(2) + ")" //le substring vire la premiere virgule
      else if (inputNeighbors.size == 1) inputNeighbors.head.toStringTree else " ")
  }
  def toStringTreePrintOnlyOne: String ={
    toString + " " +
      (if (inputNeighbors.size >= 1 )inputNeighbors.head.toStringTree else " ")
  }


  /** ([
   *
   * @param t
   * @param PARL left partenthesis or space, to be inserted at next recursive call for binop or shift (shift is implemented like a binop)
   * @param PARR left partenthesis or space, to be inserted at next recursive call for binop or shift (shift is implemented like a binop)
   * @return java code ready to be compiled by javac
   *         in case of a boolean affect, we need to wrap it with parenthesis to produce such code as r1=(r2=exp)&&(r3=exp2)
   *         the expression where unary operator like - or ~ precede the expression on which they apply, so that we can combine
   *         them without parenthesis, and therefore much less parenthesis, and much more readable expression
   */

  // def toStringTreeInfix(t: TabSymb[InfoType[_]], PARL: String = "", PARR: String = ""): String = { //default value for PARL and PARE is no parenthesis
  def toStringTreeInfix(t: DataProg[InfoType[_]], PARL: String = "", PARR: String = ""): String = { //default value for PARL and PARE is no parenthesis
    def isShift(s: String) = s.equals("<<") || s.equals(">>>")

    def toStringInputOperand(t: DataProg[InfoType[_]]): String = {
      assert(t != null && isInstanceOf[AST[_]])
      this.asInstanceOf[AST[_]] match {
        case Read(name) => val rad = radicalOfVar2(name)
          val s = t.tSymbVarSafe(rad)
          if (s.k.isParamD || s.k.isLayerField || s.k.isParamR) {
            if(s.k.isRadius1)
              name + "[i-1]"
            else
              name + "[i]"
          } //no delays for the moment being, when we read
          else name //operand is a loop register.
        case False() =>
          "0 /*False*/"
        case True() =>
          "-1 /*True*/"

        // I have  put O instead of "/*False*/", it seems to work
          //"/*False*/" //by simplification a whole expression may reduce to false after simplification.
      }
    }

    /** * @param t symbol Table needed to check if variable is a parameter
     *
     * @return code of boolean affectation, adds a [i] if isParam is true, or [i-1]/[i-1] if result parameter of radius 1 or -1
     *         radius is set to -1 when we wand to atificially add a delay,
     *         as a quick and dirty way to remove the tm1 in an affectation paramR<-tm1(exp)
     */
    def toStringOutputOperand(t: DataProg[InfoType[_]]): String = {
      assert(isInstanceOf[AST[_]])
      this.asInstanceOf[AST[_]] match {
        case ASTB.AffBool(name, _) =>
          val nameRad = radicalOfVar2(name);
          try{
            val k = t.tSymbVarSafe(nameRad).k
            if (!k.isParam) toString //affectation is done to a register local in the loop.
            else if (k.isRadius1)
              name + "[i-1] = " //Radius can be either 0 or 1 here we should also take into account the store.
            else if (k.isRadiusm1)
              name + "[i+1] = " //Radius can be either 0 or 1 here we should also take into account the store.
            else
              name + "[i] = "
          }
          catch{
            case e:java.lang.Exception=>toString //je fait l'hypothése que on n'a pas trouvé l'id car il s'agit de nom de variable temporaraire, non stockés
          }
      }
    }

    assert {
      inputNeighbors.size <= 2
    }
    val codop = toString
    inputNeighbors.size match {
      case 0 => " " + toStringInputOperand(t) + " "
      case 1 => if (isShift(codop))
        "" + PARL + inputNeighbors.head.toStringTreeInfixPar(t) + " " + codop + " " + " 1 " + PARR //parenthesis
      else if (isInstanceOf[AffBool]) //here we need to take into account delays
        PARL + toStringOutputOperand(t) + inputNeighbors.head.toStringTreeInfixPar(t) + PARR //toString comes before the parameter
      else //here we consider unary operators
        codop + inputNeighbors.head.toStringTreeInfixPar(t)
      case 2 => "" + PARL + inputNeighbors(0).toStringTreeInfixPar(t) + " " + codop + " " +
        inputNeighbors(1).toStringTreeInfixPar(t) + PARR
    }
  }

  def toStringTreeInfixPar(t: DataProg[InfoType[_]]): String = toStringTreeInfix(t, "(", ")")
  /**
   * Tries to find a cycle
   *
   * @return the cycle if a cycle is found, else none
   */
  def getCycle: Option[Vector[T]] = new Dag[T]().dfs(this.asInstanceOf[T], Vector[T]())
}

/**
 * Contains trait that facilitates definitions of DagNodes, when the number of inputs is given to be 0,1,2,3 or arbirary
 */
object DagNode {

  trait EmptyBag[+T <: DagNode[T]] extends DagNode[T] {
    def inputNeighbors: List[T] = List.empty;
  }

  trait Singleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def inputNeighbors: List[T] = List(arg)
  }

  trait Doubleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def inputNeighbors: List[T] = List(arg, arg2)
  }


  trait Tripleton[+T <: DagNode[T]] extends DagNode[T] {
    def arg: T;

    def arg2: T;

    def arg3: T;

    def inputNeighbors: List[T] = List(arg, arg2, arg3)
  }

  trait Neton[T <: DagNode[T]] extends DagNode[T] {
    def args: List[T];

    def inputNeighbors: List[T] = args
  }

}