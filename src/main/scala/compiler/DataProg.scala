package compiler

import java.util.stream.Collectors
import ASTB._
import AST.{AstPred, Call, Call2, Fundef, Fundef2, Layer, Read, and, isCons, isNotRead}
import Circuit.{AstMap, Machine, TabSymb, iTabSymb, iTabSymb2, takeNbOfBitIntoAccount}
import VarKind.{LayerField, MacroField, ParamD, ParamR, ParamRR, StoredField}
import dataStruc.{Align2, Dag, DagInstr, Naame, Named, Schedule, Util, WiredInOut, toSet}
import dataStruc.WiredInOut.{defby, setInputNeighbor}
import Instr.{a, affectizeReturn, readR}
import ASTB.Tminus1
import ASTBfun.{ASTBg, Fundef2R, Fundef2RB, concatRedop, redop}
import ASTL.ASTLg
import Named.{delify, newAuxTmp, noDollarNorHashtag}
import compiler.ASTLt.ConstLayer
import compiler.Constraint.{Aligned, H1beforeH2}
import compiler.SpatialType.ASTLtG
import dataStruc.Util.{existInJava, findDuplicates, hasBeenReprogrammed, prefixDash, prefixDot, suffixDot}
import org.w3c.dom.events.MutationEvent
import sdn.carrySysInstr

import java.io.File
import java.lang.reflect.Method
import java.util
import scala.List
import scala.Predef.ArrowAssoc
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.{Iterable, IterableOnce, Map, MapView, Set, immutable, mutable}
import scala.collection.immutable.{HashMap, HashSet, ListMap}
import scala.language.postfixOps
import scala.Predef._
import scala.util.Try

object DataProg {
  //val nameDirCompilCA = "src/main/java/compiledCA/" //where the compiled loops will be stored
  //val nameDirProgCA = "src/main/scala/progOfCA/" //where the compiled loops will be stored
  //var nameCA3:String=null
  val nameDirCompilLoops = "src/main/java/compiledMacro/" //where the compiled loops will be stored
  val nameDirProgLoops = "src/main/scala/progOfmacros/" //where the source of macro will be stored
  var isRootMainVar = true //set to false after first construct, identifies the mainRoot

  /** all the constant layers to be used in macros */
  val constLayers:HashMap[String,ConstLayer[_,_]]=new HashMap()+
    ("defVe" -> new ConstLayer[T[V, E], B](1, "def")) +
    ("defVf"-> new ConstLayer[T[V, F], B](1, "def"))
  /** print a map on several small lines, instead of one big line */
  private def string[T](t: TabSymb[T], s: String): String = t.toList.grouped(4).map(_.mkString(s)).mkString("\n") + "\n"

  /**
   * @param f function to be compiled
   * @tparam T type of result returned by f.
   * @return A dataProg in highly compact form with four type of instructions which  are callProc to:
   *         -1 return (for the main)   2-show 3 -bug-4 memo (affectation to the next field for layers)
   *         Expression includes the following constructors:
   *         -1  AST Constructor: Delayed  Param | Call1 Call2 Call3 Coons Heead Taail | Read
   *         -2  ASTL Constructor: Binop  Coonst  Uno Redop  Clock Broadcast Send Transfer Sym
   *         The DFS algo of DAG visits all Delayed node recursively as soon as they are created
   *         Variables with varKind paramD and Layer are created
   ***/
  def apply[T](f: Fundef[T], racineNommage: Named, nameCA2: String): DataProg[InfoType[_]] = {
    /**
     *
     * @param l list of newly visited  AST Nodes
     * @return elements of $l which are layers.
     */
    def getLayers(l: List[AST[_]]) =
      l.collect { case la: Layer[_] => la }

    /** y a deux source de system instruction: layer et carrySysInstr */

    def getSysInstr(l: List[AST[_]]): List[CallProc] = {
      val l1= getLayers(l).flatMap(_.systInstr)
      val l2: List[CallProc] =l.collect{case  instrs:carrySysInstr=>instrs.syysInstr}.flatten
      val res=l1++l2
      val setsize=res.toSet.size
      if(setsize!=res.size)   throw new Exception("probably the same field is printed two times " + findDuplicates(res) )
      res
    }
    //def getHierarchyDisplay:HashMap[Layer[_],ASTL[_ <: Locus,_ <: Ring]]=new HashMap()++
    //TODO build the layer structure here, exploit that we have it!
    val dag: Dag[AST[_]] = Dag()
    /** f.body  is the expression containing the value returned by the functions.
     * It  is the  access point to all the AST nodes needed to compute the function.
     * We use a fake call to a macro called "return" to represent the function's code */
    val main = CallProc("return", List(), List(f.body))
    /** contains the current instructions to be explored for retrieving new DagNodes */
    var instrsCur = List(main)
    /** contains the current instructions to be explored for retrieving new DagNodes */
    var layers: List[Layer[_]] = List()
    //if(isRootMainVar) nameCA3=nameCA2
    do try {
      val newElts=dag.addGreaterOf(instrsCur.flatMap(_.exps))
      val l: List[Layer[_]] = getLayers(newElts)
      layers :::= l;
      val syysInstrs= newElts.collect{case  instrs:carrySysInstr=>instrs.syysInstr}.flatten //les syysInstr aussi y peuvent ajouter du matos recursif
      instrsCur = (l.flatMap(_.systInstr)++syysInstrs) //as we add generators, we possibly get new call to Display debug or memorize
    }
    catch {
      case e@(_: dag.CycleException) =>
        //Name.setAllName(f, "") //permet d'afficher les noms de variables du cycle et donc de
        Naame.setAllName(racineNommage, "tata") //permet d'afficher les noms de variables du cycle et donc de
        //  Plus facilement identifier ou se trouve le cycle dans le programme
        for (a <- e.cycle)
          print(a + (if (a.name != null) (a.name + "-") else "-"))
        throw new dag.CycleException(Vector.empty)
    }
    while (!instrsCur.isEmpty)
    // we now descend starting from the main circuit, to explore all the field, and then fields of fields.....
    val stillNullNamed3=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name==null case _ => false})
    dataStruc.Naame.setAllName(racineNommage, nameCA2); //for ''grad'' to appear as a name, it should be a field of an object extending the fundef.
    // dataStruct.Name.setAllName(f, "")
    val fliesNisv=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name=="fliesNisv" case _ => false})
    val stillNullNamed2=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name==null case _ => false})
    val notNullNamed2=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name!=null case _ => false})
    //we check that each layers is reached by the naming algo
    for(l<-layers) {
      if(l.name==null) {
        if(l.isInstanceOf[ConstLayer[_,_]])
          l.setName(l.init + l.asInstanceOf[ConstLayer[_,_]].locName)
        else throw new Exception("one of the layers has not been reached by the naming algorithm")
      }
    }
    val stillNullNamed=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name==null case _ => false})
    val notNullNamed=dag.visitedL.filter((s:AST[_])=>s match{case t:Named=> t.name!=null case _ => false})
    val funs: iTabSymb[Fundef[_]] = immutable.HashMap.empty ++ dag.visitedL.collect {
      case l: Call[_] =>
        (l.f.name, l.f)
    }

   //compute the name of the java classes containing the code of macros
    var javaClassOfMacros: Set[String] =funs.keys.map(prefixDot(_)).toSet
    //removes  previously compiled class of loops, which needs to be compiled again, because source has been updated.
    for(namejava<-javaClassOfMacros)
      //if (hasBeenReprogrammed(namejava,nameDirProgLoops,nameDirCompilLoops)) //there has been a reprogramming
        if (hasBeenReprogrammed(nameDirProgLoops+namejava.capitalize+".scala",nameDirCompilLoops+namejava+".java")) //there has been a reprogramming
        {
          val f=new File(nameDirCompilLoops + namejava+".java")
          f.delete()
          javaClassOfMacros=javaClassOfMacros-namejava
      }
      //we remove the classOfMacro if their source has been manually deleted, so as to trigger their recompilation
    for(namejava<-javaClassOfMacros)
      if(!existInJava(nameDirCompilLoops+namejava+".java"))
        javaClassOfMacros=javaClassOfMacros-namejava
    /**
     * builds the map of already compiled macro, for each java file of macro
     */
    val allAlreadayCompiled:HashMap[String,Array[String]]= {
      /** returns name of already defined macro of type macrosType.
       *  for example, methods of rand (randV, randE, if macroTypeFile=compiledMacro/rand
       *  removes the bit size*/
      def alreadyCompiledForOneBitSize(macrosTypeFile: String): Array[String] =
        Util.myGetDeclaredMethod(macrosTypeFile).map(prefixDash(_)) //we get the declared metho, but then supress the int size
      HashMap()++javaClassOfMacros.map((s:String)=>(s->alreadyCompiledForOneBitSize("compiledMacro." +s)))
    }

    /**
     *
     * @param macroNobitSize name of loopmacro not including bit size
     * @return true if one loop $macroNobitSize$ has been compiled for at least one bit size
     */
    def isCompiled(macroNobitSize:String):Boolean=
      (allAlreadayCompiled.contains(prefixDot( macroNobitSize)))&&
      (allAlreadayCompiled(prefixDot( macroNobitSize)).contains(suffixDot(macroNobitSize)))

    /**
     *
     * @param macroNobitSize Name of a macro without bit size
     * @return true if that name has bee stored in takeNbOfBitIntoAccount so as to be considered for the second pass.
     */
    def needCompiled(macroNobitSize:String):Boolean=
      takeNbOfBitIntoAccount.contains(macroNobitSize)

    /**
     * map of the funs's name which do need to be compiled
     */
    val toBeCompiled: Map[String, Fundef[_]] =funs.filter((x)=> !isCompiled(x._1) || needCompiled(x._1))
    /** second  gathering of SysInstr, wecan now access  the layer's name, because  setName has been called   */
    val notToBeCompiled=funs.filter((x)=> ! toBeCompiled.contains(x._1))
    def getConstLayer(namesProc:List[String])={
      val names=namesProc.flatMap( allLayerFromCompiledMacro(_)).toSet.map(delify(_))
       names.map(constLayers(_))
    }

    val constlayer=getConstLayer(notToBeCompiled.map(x=>x._1).toList)
    val instrs: List[CallProc] = main :: getSysInstr(dag.visitedL)
    /** adding bug layers */
    if (isRootMainVar) {
      isRootMainVar = false //the next dataProg will therefore not execute the comming code
      layers = bugLayers(instrs) ++ layers.asInstanceOf[List[Layer[_]]] //we add the bug layers, we must find out firt on what kind of locus we do have possible bugs.
      layers=constlayer.toList++layers
    }
    /** Symbol table  */
    val tsb: TabSymb[InfoType[_]] = mutable.HashMap.empty
    tsb ++= f.p.toList.map(a => ("p" + a.name, InfoType(a, ParamD()))) // stores parameters  in the symbol table.
    tsb ++= layers.map(a => (Named.lify(a.name), InfoType(a, LayerField(a.nbit, a.init)))) // stores layers with bit size, in the symbol table.
    val newProg=new DataProg[InfoType[_]](new DagInstr(instrs, dag), //alreadycompiled fun will not be in subFun,
      toBeCompiled.map { case (k, v) ⇒ k -> DataProg(v,v.body,k) }, tsb, f.p.toList.map("p" + _.name), List())//compiles carefully selected subset of macros.
    //newProg.checkInvariant;
    newProg
  }

  def bugLayers(lesInstr: List[CallProc]): List[Layer[_]] = {
    val bugInstr = lesInstr.filter(_.procName == "bug")
    //we add the bug layers, we must find out firt on what kind of locus we do have possible bugs.
    var locusBug: Set[Locus] = bugInstr.map(_.exps.head.mym.name.asInstanceOf[(Locus, Ring)]._1).toSet
    //we artificially add V, so as to be able to identify the main entry point by testing it has a llbugV
    locusBug = locusBug + V()
    locusBug.map((l: Locus) => {
      val la = (ASTLt.constLayerBool("false")(new repr(l))).asInstanceOf[Layer[_]]
      la.setName("bug" + l.shortName);
      la
    }).toList
  }

  def allLayerFromCompiledMacro(procName:String): List[String] ={
    //calcul des layers de la macro appellée
    val className="compiledMacro."+prefixDot(procName)
    // Load the Java class
    val clazz: Class[_] = Class.forName( className)

    // Get all methods of the class
    val methods: Array[Method] = clazz.getDeclaredMethods
    // Get the first method (or whichever you're interested in)
    val methodVersion  = methods.filter(_.getName.contains(suffixDot(procName)))
    val method:Method=methodVersion.head
    // Get the parameters of the method
    val parameters = method.getParameters.map(_.getName)
    val paramLayers=parameters.reverse.takeWhile(Named.isLayer(_)).reverse
    // val layers: Array[AST.Layer[_]] =paramLayers.map(Layers.layers(_))
    paramLayers.toList
  }
}


/**
 * Contains the compiled data, and all the functions used to implement the stage of compilation:
 * treify, procedurify, bitify, macroify, foldRegister, unfoldSpace
 *
 * @param dagis the dag of instructions stored in reversed order.
 * @param funs  the macros
 * @tparam U type of the info stored
 * @param tSymbVar symbol table
 * @param paramD   names of data parameters, provides  an order on them
 * @param paramR   names of result parameters , provides  an order on them
 * @param coalesc when unfolding from spatial type to scalar type , or scalar int to bool,
 *                each variable is rewritten into several, however, those several duplicata can sometimes be coalesced
 *                for exemple grad$d2, grad$ad1, grad$h1, grad$ad2, grad$d1, grad$h2 can be coalesced
 *                because we succeeded to schedule instructions so that they in fact correspond to a single variable
 *                naturally, we coalesc them to a register called "grad"
 *                when such coalescing  happens grad$d2, grad$ad1, grad$h1, grad$ad2, grad$d1, grad$h2
 *                will not appear in the symbol table,
 *                instead they will figure in the coalesc table.
 *                The locus is forgotten in the type of stored variables in main loop,
 *                but is kept in the type of macroFields, DataParameters, ... for CA loops.
 *                For main loop----------
 *                The former variable, "grad", remains in the symbol table, and this holds even if no coalescing happens
 *                the reason is that this will allow to retrieve the locus, which will be usefull for displaying
 *                For boolean vertice variable, we choose to not insert several entries, for the spatial, the non spatial a
 *                and finally the boolean variable, we use a single spatial variable, with type V(),B()
 *                For CA loop ----------------
 *                we keep the locus in the type, it helps to distinguish scalar variables from variables which
 *                come from unfolding. Macrofields are not printed anyway
 */
class DataProg[U <: InfoType[_]](val dagis: DagInstr, val funs: iTabSymb[DataProg[U]], val tSymbVar: TabSymb[U],
                                 val paramD: List[String], val paramR: List[String],
                                 val coalesc: iTabSymb[String] = null) {

  /** all the coalesced register must be defined in the symbol table */
  def allLayers: List[String] = {
    def isLayer(name: String) = tSymbVar(name).k.isLayerField
    tSymbVar.keys.filter(isLayer).toList
  }
  def checkInvariant={
    def invariantLayers={ //only the main can have layers, oups, not true because we pass the defVe layers
      assert(allLayers.isEmpty||isRootMain, "we have a macro" +"with layers, let us look at produce java, what happens in the suppressed segment")
    }
    def invariantCoalesc =
      if (coalesc != null)
        for (c <- coalesc.values)
          if (!tSymbVar.contains(c) && !c.startsWith("mem[")) //!(Try(c.toInt).isSuccess))
            throw new Exception("colesced register:" + c + " not present in symbol table")
    /** verifies that a main loop does not call other main loop, we would need a stack and that has no been implemented */
    def invariantSingleMain =
      if (!isLeafCaLoop && !isRootMain)
        throw new Exception("there is only the mainRoot which is not a leaf Ca loop ")
    /** all registers used by insrtructions must be either contained in tSymb or in tSymb(coalesc) */
    def invariantVariable = {
      val used = dagis.usedVars
      for (v <- used)
        if (!tSymbVarExists(v) && !tSymbVarExists("p" + v) && !v.startsWith("mem["))
          throw new Exception("variable:" + v + " not present in symbol table")
    }
  invariantCoalesc
    invariantSingleMain
    invariantVariable//}//;invariantLayers
  }
  /** the main root is characterized by the fact that it has a bug layer. */
  def isRootMain: Boolean = tSymbVar.contains("llbugV")

  /** used to tranform leafCAloops which have no subfun. */
  val noSubFun = immutable.HashMap[String, DataProg[InfoNbit[_]]]()

  private def dagisScheduleMatters = coalesc != null

  /** look up the symbol table if not found, take the coalesced form */
  def tSymbVarSafe(str: String): U = {
    if (coalesc == null) tSymbVar(str)
    else if (!tSymbVar.contains(str) && (!coalesc.contains(str) || !tSymbVar.contains(coalesc(str))))
      throw new Exception("on trouve pas " + str)
    else
      tSymbVar.getOrElse(str, tSymbVar(coalesc(str))) //renvoie la version  coalesced seulement si pas dans la table.
  }

  /** look up the symbol table if not found, take the coalesced form */
  protected def tSymbVarExists(str: String) = {
    if (coalesc == null) tSymbVar.contains(str)
    else tSymbVar.contains(str) || (coalesc.contains(str) && tSymbVar.contains(coalesc(str)))
  }



  /** @return instructions in textual form */

  def toStringHeader =
    (if (isLeafCaLoop) "************************************************\nleaf CA loop " else "non-leaf main ") +
      " of signature: " + paramD.mkString(" ") + "=>" + paramR.mkString(" ") /*+ " name of CA " + paramR(0) */ + "\n"

  lazy val keys: List[String] = tSymbVar.keys.toList
  /** regroup  identifier having a common varkind */
  lazy val idIndexedByKind: Predef.Map[VarKind, List[String]] = keys.groupBy(tSymbVar(_).k)

  lazy val intKeys: List[String] = try {
    keys.filter(tSymbVar(_).asInstanceOf[InfoNbit[_]].nb > 1)
  }
  catch {
    case _: ClassCastException => List()
  } // tabSymb may not contains InfoNbit if bit size was not yet computed

  def isScalar(s: String): Boolean = !isSpatial(s)

  def isSpatial(s: String): Boolean = !tSymbVar(s).t.isInstanceOf[Ring] //j'en ai fait une autre qui regarde si le nom contient des diese ou des dollars

  /** in order to also avoid repeating the spatial type, we also regroup identifiers by  spatial or scalar type */
  def indexingByType(s: List[String], p: String => Boolean) = s.filter(p).groupBy(tSymbVar(_).t)

  /** The following illustrates a simple and standard way of recomputing all the values of a map,
   * using a match of the (keys,value) pair .map{case (k, v) and
   * re-building association using the arrow k-> indexingBySpatialType(v) */
  def indexedByKindThenByType(p: String => Boolean): Map[VarKind, Map[Any, List[String]]] = idIndexedByKind.map {
    case (k, v) => k -> indexingByType(v, p)
  }

  /** We defined ParamD < ParamR < MacroFields, so as to be able to sort and
   * show first  dataPamater and resutParameters */
  def sortedindexedByKindThenByType(p: String => Boolean) = ListMap(indexedByKindThenByType(p).toSeq.sortBy(_._1): _*)


  /** keys of coalescInverted are register list towards which variables are coalesced, we must add standalone variables */
  lazy val coalesced: Map[String, Iterable[String]] =
    if (coalesc == null || coalesc.isEmpty) HashMap()
    else coalesc.keys groupBy (coalesc(_))
  /** names of variables which are used before being affected */
  lazy val delayed = {
    var res: Set[String] = HashSet()
    var defined: Set[String] = HashSet()
    for (instr: Instr <- dagis.visitedL.reverse) {
      res ++= (instr.usedVars() -- defined)
      defined ++= instr.names
    }
    if (idIndexedByKind.contains(ParamD()))
      res --= idIndexedByKind(ParamD()).toSet // dis   <-  pdis makes pdis appear as a delayed variable,
    // pdis appears in tabSymb sorted by kind,
    // (res -- paramD.toSet).toList.sorted  pdis does not appears directly in paramD, which countains pdis#0, pdis#1 ...
    res
  }
  /** register which are not coalesced, and shoud be defined. */
  lazy val standaloneRegister: Iterable[String] =
    tSymbVar.keys.filter((s: String) => (!coalesc.contains(s) && !tSymbVar(s).k.isParam && !tSymbVar(s).k.isLayerField && !coalesced.contains(s) && !(s(0) == '_')))

  /**
   * we distinguish between the various segment to print.
   * @return
   */

  /** @return instructions in textual form will be redefiened in DataProgLoop in order to include code of loops*/
  def toStringInstr = "there is " + dagis.visitedL.length + " instructions\n" +
    dagis.visitedL.reverse.map((i: Instr) => i.toString() + "\n").mkString("")

  override def toString: String = {

    def toStringFuns: String = {
      var branch: Int = 0; var leave: Int = 0
      def countCAloops(f: DataProg[U]): Unit =
        if (f.isLeafCaLoop) leave += 1
        else {
          branch += 1
          f.funs.values.map(countCAloops(_))
        }
      def totalComplexity: String = {
        if (!isInstanceOf[DataProgLoop[_]]) return ""
        var res = 0
        for (f <- funs.values)
          res += f.asInstanceOf[DataProgLoop[_]].totalOp
        " total complexity is: " + res + "gates "
      }
      if (!isLeafCaLoop )//verifie que c'est la racine
      {  countCAloops(this);
        "************************************************\n there is " + branch + " main branch fun and " + leave + " leaf ca loop\n" + totalComplexity
      }
      else ""
    }

    /** @return the whole symbol table  in textual form */
    def toStringTabSymb: String = {
      tSymbVar.size + " variables sorted by kind and then by spatial or scalar type:\nSpatial types: \n " +
        sortedindexedByKindThenByType(isSpatial).mkString("\n") +
        "\nScalar type: \n" +
        // sortedIdScalar.values.map(_.mkString("\n")) +
        sortedindexedByKindThenByType(isScalar).filter((x: (VarKind, Map[_, List[String]])) => x._2.nonEmpty).mkString("\n") +
        "\nnon boolean varaiable are : " + intKeys.map((id: String) => id + ":" + tSymbVar(id).asInstanceOf[InfoNbit[_]].nb + " bit") + "\n"
    }

    /** @return coalesced registers in textual form with alphabetic ordering on the keys
     *          so that the register r1,r2... stand out together */
    def toStringCoalesc: String = if (coalesc == null) "" else {
      val sortCoalesced = ListMap(coalesced.toSeq.sortBy(_._1): _*)
      "standalone (also need registers): " + standaloneRegister.mkString(",") + "\n" +
        "delayed: (need initialize) " + delayed.mkString(",") + "\n" +
        coalesced.size + " classes of coalesced Ids\n" +
        coalesced.keys.toList.sorted.mkString(", ") + "\n" +
        sortCoalesced.grouped(2).map(_.mkString("---")).mkString("\n") + "\n"
    }

    /**
     * @param t declared function, and macro
     * @tparam T
     * @return automatically defined macro are moved to last position for clarity.
     */
    def listOf[T](t: Map[String, T]): List[(String, T)] = {
      val (automatic, definedMacros) = t.partition((x: (String, T)) => x._1.startsWith("_fun"));
      automatic.toList ::: definedMacros.toList
    }
    val l=listOf(funs)
    val codefuns=l.mkString("\n\n")
    toStringFuns + toStringHeader + toStringInstr + toStringTabSymb + toStringCoalesc + "\n" + codefuns
  }


  /** add new symbol created through affectize */
  private def updateTsymb[U](l: List[AST[_]], v: VarKind): mutable.Map[String, InfoType[_]] =
    tSymbVar.asInstanceOf[TabSymb[InfoType[_]]] ++= l.map((e: AST[_]) => (e.name, new InfoType(e.mym.name, v)))
  def storeFieldise2(v:String)={
    val tSymbVarbit=tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
    tSymbVarbit(v)=tSymbVarbit(v).storedFieldise2
  }

  /** add new symbol created through affectize with number of bits , using only the symbol table */
  private def updateTsymbNbit[U](l: List[AST[_]], v: VarKind): mutable.Map[String, InfoNbit[_]] = {
    val emptyEnv: HashMap[String, ASTBt[B]] = HashMap.empty[String, ASTBt[B]]
    for (e <- l)
      tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]].addOne(
        e.name -> new InfoNbit(e.mym.name, v,
          e.asInstanceOf[ASTBt[_]].nBit(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc, emptyEnv)))
    tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
  }

  /**
   * @return the DAG of AST becomes a forest of tree, and we we build a Dag of Instructions instead which include.
   *         1- as before callProc to  -1 return    2-show 3 -bug- 4 memo (affectation )
   *         2- pure affectation of AST used two times or more.
   *         variable for those affectation are created with VarKind "Field"
   *         Delayed Constructors are removed from Expressions
   *         Param are replaced by Read with the letter 'p' added to the name
   *         Layers are replaced by Read with the letter 'll' added to the name
   *         Some of the node do not have name, i.e. their name is null
   *         they are not used two times, they did not received a name
   *
   *         * works  for ASTBt instead of ASTLt when setting dagdag to false
   *         which result in directy working on visitedL feature of DAG instead of reconstructing it
   *         it include then with the following difference:
   *         * we compute a new name only for expression used twice, and we certainly
   *         * do not try to optimize the name, we also have to forget about shift when computing inputNeighbors,
   *         * so as to be able to used it in order to insert the new affect at the right place.
   *
   */

  def treeIfy(): DataProg[U] = {
    /** we will consider read if it is a parameter is read */
    val isNotReadReg: AstPred = {
      case AST.Read(x) =>
        tSymbVarSafe(x).k == ParamD()
      case _ => true
    }
    val isNotConst: AstPred = {
      case  a:ASTLt[_,_] => ! a.isCoonst
      case _ =>true
    }
    val iT: Set[AST[_]] = dagis.inputTwice.filter(and(isNotReadReg,isNotConst)) //should filter out more stuff because it consumes register which are a precious ressource

    val dagis2: DagInstr = dagis.affectIfy(iT, "auxL", dagisScheduleMatters) //also replaces access to data parameters+layers by read

    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerField(_)) // dagis.newAffect, stores precisely affected expression which are also nonGenerators.
    //todo newAffect has been ordered so that nbit of a variable v1 that uses a variable v2, is upbdated after v2. It may be the case that
    //dividing into layerfields and macrofields, perturbate this order.
    if (!dagisScheduleMatters) {
      updateTsymb(macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro => its type = MacroField,
      if (!isLeafCaLoop)
        updateTsymb(layerFields, StoredField()) // for the main , excepted for affectation of the form dist<-lldist, the type of dist is set to storedLayer,
      // the varKind Layer is replaced by stored field, and no longer used at all,Except for constant layers
      else updateTsymb(layerFields, MacroField()) // for the loop macro, the only layers passed are constant layers,
    } //  we set the type to macro because we do not need to store them again.
    else {
      //val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
     //proposition pour demain:
      //rajouter un test pour restreindre seulement au constantes
      def isConst2(a:AST[_]):Boolean={
        a match{
          case b:ASTBt[_]=>b.isConst
          case _ => false
        }
      }
      val (const,notConst)=macroFields.partition(isConst2)
      updateTsymbNbit(const,   if (!isLeafCaLoop )StoredField()else MacroField()) // if affectify happens after unfold int, we provide the number of bits

      //updateTsymbNbit(macroFields, MacroField()) // if affectify happens after unfold int, we provide the number of bits
      updateTsymbNbit(notConst, StoredField())
      updateTsymbNbit(layerFields, StoredField())
    }

    //we check that macros do not contain level 2, macros.
    if(!isRootMain)
        if(funs.size>0)
      assert(funs.isEmpty)
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy() }, tSymbVar, paramD, paramR, coalesc)
  }

  /**
   * @return replaces function call by procedure call
   *         "return " callProc together with Cons expression are replaced by  affectations  to result parameters,
   *         Call AST nodes are replaced by   callProc instructions
   *         x<-Heead y<-Taail are replaced by directly passing x to the call Proc , written as an affectation of x,y
   *         instructions  of the form: id<-tail  id<-head, return   becomes useless. They are filtered out
   *         variable for effective parameter(resp. result) parameter are created with VarKind "StoredField" (resp. ParamR)
   */
  def procedurIfy(): DataProg[InfoType[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    /*    val (callProc,affect)=dagis.visitedL.partition((i:Instr)=>i.isInstanceOf[CallProc])
        val exps=dagis.visitedL.flatMap(_.exps)//effective parameter of proc, or affected expression
        val argAff = affect.map(_.exps(0)).map(_.nonConcatOrBroadcastCallArg(p.tSymbVar).toSet)
        val argCallProc=callProc.map(_.exps).map((es:List[AST[_]])=>
          AST.nonConcatOrBroadcastCallorCallProc(es,p.tSymbVar)).toSet*/
    val arg: Predef.Set[AST[_]] = dagis.visitedL.flatMap((i: Instr) => i.exps.flatMap(
      _.nonConcatOrBroadcastCallArg(i, tSymbVar.asInstanceOf[TabSymb[InfoType[_]]]))).toSet
    // val arg=argAff.union(argCallProc)

    val dagis2 = dagis.affectIfy(AST.or(isCons, arg.contains(_)), "auxC")
    p.updateTsymb(dagis.newAffect.map(_.exp), StoredField()) //we store the args to call in memory so that we can pass them
    val hd: TabSymb[String] = mutable.HashMap.empty;
    val tl: TabSymb[String] = mutable.HashMap.empty
    for (i <- dagis2.visitedL) i.buildhdtl(hd, tl)
    //def called=dagis2.visitedL.filter(case c: Call[_] =>)
    assert(hd.keySet.size==tl.keySet.size,"on utilise pas tout les résultat de "+hd.values + tl.values)
    /** "return CallProc instruction" containing the body of the function */
    val main = dagis2.allGenerators.find(_.isReturn).get.asInstanceOf[CallProc]
    /** names of variable storing the result parameters ,
     * LinkedHashSet as opposed to Hashset,   preserves the order of insertion
     * and thus, the order of parameter, which is informational */
    val paramRmut = mutable.LinkedHashSet.empty[String]
    /** transformation if formulated as an instruction rewriting
     * replace the "return" callProc by  affectations  to result parameters, and then
     * replace Call AST nodes by   callProc instructions
     * filters out instructions which becomes useless, of the form: id<-tail  id<-head, return */
    val rewrite2: Instr => List[Instr] = (i: Instr) => {
      if (i.isReturn)
        affectizeReturn(p.tSymbVar, paramRmut, i.exps.head).flatMap(_.procedurIfy(hd, tl, p.tSymbVar))
      else
        i.procedurIfy(hd, tl, p.tSymbVar)
    }
    val dagis3 = dagis2.propagate(rewrite2)
    new DataProg(dagis3, funs.map { case (k, v) => k -> v.procedurIfy() }, p.tSymbVar, paramD, paramRmut.toList)
  }


  /** Auxiliary variable will be StoredField or MacroField, depending if we are in a CAloop or in the main */
  def storeOrMacroField = if (isLeafCaLoop) MacroField() else MacroField()

  /**
   * Computes the number of bits of all variables: parameters (effective and formal)
   * ,  affectation, and also internal nodes of all the ASTs.
   *
   * @param nbitP : list of  each parameter's bit size, assumed to be ASTLs.
   * @return Program data including number of bits  available in the symbol table
   *         a macro signature now includes bit size of parameters.
   *         So if a macro is called two times with different bitsize, two macros are compiled
   *         The affectation for redops should be generated in foldRegister
   *         We generate them now so that we can also compute the number of bits for the corresponding variables.
   *         //¯TODO show of storedLayer must be handled after macroification
   **/
  def bitIfy(nbitP: List[Int]): DataProg[InfoNbit[_]] = {
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    /** We generate also variable which are effective data parameters for called macro
     * their kind is set to StoredField() */
    val effectiveDataParam: HashSet[AST[_]] = HashSet() ++ dagis.allGenerators.flatMap(
      { case cp@CallProc(p, names, exps) => if (Instr.isProcessedInMacro(p)) List() else exps.filter(isNotRead(_)); case _ => List() })
    val dagis1 = dagis.affectIfy(effectiveDataParam(_), "auxB")
    /** effective result parameters which were already variables need to be re-registered as storedFields */
    val newStoredFiedl: List[AST[_]] = effectiveDataParam.toList.filter((a: AST[_]) => AST.isNotRead(a) || p.tSymbVar(a.name).k == MacroField())
    p.updateTsymb(newStoredFiedl, StoredField())

    val l = dagis1.dagAst.visitedL.asInstanceOf[List[ASTLt[_, _]]]
    val redops: HashSet[AST[_]] = HashSet() ++
      l.flatMap { _.redExpr  } ++ l.filter(_.isRedop)
    val affected: Seq[AST[_]] = dagis1.visitedL.filter(_.isInstanceOf[Affect[_]]).map(_.exps.head)
    //  if(redops.intersect(affected.toSet).nonEmpty)  throw new Exception("yes this is usefull")
    val redops2 = redops -- affected //we do not need to affectify, it is already affectified, this looks bugged
    val redops3: Set[AST[_]] = redops2.filter(isNotRead(_))

    //on copie sur redop pour traiter binopEdge
    val binopEdge=  HashSet() ++ l.flatMap { _.binopEdgeExpr  } ++ l.filter(_.isBinopEdge)
    val binopEdge2 = binopEdge -- affected //we do not need to affectify, it is already affectified, this looks bugged
    val binopEdge3= binopEdge2.filter(isNotRead(_))
    val binredop= redops3 ++ binopEdge3

    /** values being reduced must be id of variable
     * so we affectify those, before bitIfying,
     * because that puts new ids in the symbol table
     * for  which we will also need to know the bit size
     * We also affectify the reduced value in order to reuse the register
     * which accumulates the reduction */
   // val dagis2 = dagis1.affectIfy(redops3(_), "auxO");
    val dagis2 = dagis1.affectIfy(binredop(_), "auxO");
    p.updateTsymb(dagis1.newAffect.map(_.exp), storeOrMacroField)


    val nbitExp: AstMap[Int] = mutable.HashMap.empty
    val newFuns: TabSymb[DataProg[InfoNbit[_]]] = mutable.HashMap.empty
    /** stores the number of bits of parameters which are assumed to be ASTLs */
    val newtSymb: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    //adds param's bit
    newtSymb ++= (paramD zip nbitP).map {
      case (nom, nbi) => nom -> new InfoNbit(tSymbVar(nom).t, tSymbVar(nom).k, nbi)
    }
    //adds layers's bit
    val layersName: List[String] = tSymbVar.keys.filter(Named.isLayer(_)).toList

    for (nom <- layersName) {
      val d = tSymbVar(nom)
      newtSymb.addOne(nom, new InfoNbit(d.t, d.k, d.k.asInstanceOf[LayerField].nb))
    }
    val rewrite: Instr => Instr = _.bitIfy(p, nbitExp, newtSymb, newFuns)
    // we bitify all the instructions in reverse order
    // because instructions are stored in reversed order
    // and computing the number of bits needs to follow the natural order
    new DataProg(dagis2.propagateReverse(rewrite), newFuns, newtSymb, paramD, paramR)
  }

  /** @return true if function is a leaf function,
   *          not calling other function, so no stored field
   *          in fact we have to allow stored field for computing constant,
   *          (a better implementation with constant folding would correct that)
   *          and therefore directly executable as a loopMacro on CA
   *          we check that it is also not isRootMain which could surprisingly be a CA loop if it computes identity */
  def isLeafCaLoop: Boolean = funs.isEmpty  && !isRootMain //&& !tSymbVar.valuesIterator.exists(_.k.isStoredField)

  /**
   *
   * @param e expression we want to check
   * @return true if e reads a layer
   */
  private def isLayerField(e: AST[_]): Boolean = e match {
    case AST.Read(s) =>
     s.startsWith("ll")// we change to cope with ll  tSymbVar(s).k.isLayerField
    case _ => false
  }


  /** after macroisation, we need to again run a treeification, on generated macros.
   * a dataParameter called "toto" which is read two times,  will be "affectized".
   * affectation "ptoto=toto" is added, where the new id appends the letter 'p' to the original parameter's name
   * and toto is replaced by ptoto, of varking "MacroField"
   * affectation "ptoto=toto" will ultimately be translated as a loading.
   *
   * todo we need to check this on loop-macro produced by macroified */
  def treeIfyParam(): DataProg[U] = {
    val isNotReadOrParam: AstPred = {
      case r@AST.Read(_) =>
        tSymbVar(r.which).k == ParamD();
      case _ => true
    }
    val isReadAndParam: AstPred = {
      case r@AST.Read(_) =>
        tSymbVar(r.which).k == ParamD();
      case _ => false
    }

    /** data parameter used more than once, which should therefore be loaded  */
    val iT = dagis.inputTwice.filter(isNotReadOrParam)
    /** we need to scan the leaves of expressions in instructions, because scanning dagAst visit only a subset of leaves. */
    val paramToBeRepl: List[AST[_]] = dagis.visitedL.flatMap(_.exps.flatMap(_.leaves())).filter(isReadAndParam);
    paramToBeRepl.map(_.pify()); //adds a 'p' to the name, effect of this supplementary p causes affectification to generate  ptoto=toto
    val dagis2 = dagis.affectIfy(iT, "auxM") //expression of the Affectation generated are stored in dagis.newAffect, they correspond precisely to nonGenerators.
    val (layerFields, macroFields) = dagis.newAffect.map(_.exp).partition(isLayerField(_)) //there is now no layerFields, so this seems useless.
    if (!dagisScheduleMatters) {
      updateTsymb(macroFields, MacroField())
      updateTsymb(layerFields, StoredField()) //This does not consider affectation of the form dist<-lldist,
      for (name <- iT.filter(AST.isRead).map(_.asInstanceOf[Read[_]].which)) {
        val info = tSymbVar(name).asInstanceOf[InfoNbit[_]] //we drop the letter "p" we get the number of bits
        val newInfo = new InfoNbit(info.t, MacroField(), info.nb)
        tSymbVar.addOne(Named.pify(name) -> newInfo.asInstanceOf[U])
      }
    }
    else { //but carefull, we should provide the number of bits if affectify happen after unfold int.
      // val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
      updateTsymbNbit(macroFields, MacroField())
      updateTsymbNbit(layerFields, StoredField())
    }

    // the type of dist is set to storedLayer
    // paramD varkind  could  be replaced by Affect , but this should not happen because of the added letter 'p' for the parameter.
    // if a parameter is used two times, the generated affectation will generate a read without the 'p'
    new DataProg(dagis2, funs.map { case (k, v) ⇒ k -> v.treeIfy() }, tSymbVar, paramD, paramR, coalesc)
  }

  private var nameCompteur = 0

  /**
   *
   * @return separate the program into "pure leaf CA loops" later to be compiled as a big loops,
   *         and non leaf main, later to be compiled in a single sequence of calls to CA loops.
   *         pure main should contains only affectation between variables, concat, and calls to other macros
   */
  def macroify(): DataProg[InfoNbit[_]] = {
    /** @param s field identifier
     * @return True if field  with id s needs to be stored in CA memory  */
    def needStored(s: String): Boolean =
      tSymbVar(s).k.needStored

    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    /**
     * @param finstrs a set of affectation forming a connected component.
     * @return subFunction whose instructions are in topological order
     *         DR parameter are repeated, but will be removed from results, when compiling the call, and the header.
     */
    def builtFun(finstrs: Iterable[Instr]): DataProg[InfoNbit[_]] = {
      /** @param i an instruction
       * @return true if instruction $i produces a result that needs to be stored in a CA layer   */
      def resultNeedStored(i: Instr) = i.names.filter(needStored).nonEmpty || i.tobeProcessedInMacro //(either instruction is a call to a memo, a layer next's value, a paramR, a StoredField,
      /** transforms memo system calls into affectation */
      val pureAffect: Iterable[Instr] = finstrs.map(_.callProcToAffect)
      /** contains instructions with potentially produce variable needing to be stored */
      val fparamR: List[Instr] = pureAffect.filter(resultNeedStored).toList
      /** resultParameters's id are the variables that need to be stored */
      val fparamRname = fparamR.flatMap(_.names).filter(needStored)
      /** DataParameters'id are the variables that need to be stored */
      val locallyComputed = finstrs.flatMap(_.names).toSet
      val fparamDbrut: Set[String] = toSet(pureAffect.flatMap(_.exps)
        .flatMap(_.symbolsExcepLayers).filter(!locallyComputed.contains(_)))
      val fparamDstored: Set[String] = fparamDbrut. filter (needStored(_)) //on accepte que les parametres soient des macro, cela peut arriver maitenant qu'on casse des marco en deux pour éviter les cycles dans le dag quotieht
      /** contains macro fields which becomes stored field due to cycle detection. */
      val fparamDmacro: Set[String] = fparamDbrut. filter (!needStored(_)) //on accepte que les parametres soient des macro, cela peut arriver maitenant qu'on casse des marco en deux pour éviter les cycles dans le dag quotieht
      /** Variables that are both dataParameter, and not computed within new function     */
        val fparamD=fparamDmacro.union(  fparamDstored)
      val fparamDwithoutR = fparamD.filter(!fparamRname.contains(_)).toList
      //if there is paramD which are also parameR then fparamDwithoutR va etre strictement plus petit que fparamD
      if (fparamDwithoutR.size < fparamDstored.size)
        throw new RuntimeException("Macro has parameter which are both data and result") // _we have to consider this case more carefully


      val newtSymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
      val t = tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
      for (p <- fparamDwithoutR) {
        val old = t(p); newtSymbVar += p -> new InfoNbit(old.t, ParamD(), old.nb)
      }
      for (p <- pureAffect) for (n <- p.names) {
        val old = t(n)
        newtSymbVar += n -> new InfoNbit(old.t,
          if (!needStored(n)) MacroField()
          else ParamR(), old.nb)
      }
      setInputNeighbor(pureAffect.toList) // when using a data parameter in paramD,
      // we should not include the instructions which were computing those parameter
      val newDagis = new DagInstr(fparamR) //instructions computing results are the roots.

      val constantLayers = newDagis.visitedL
      /** newly built macro may use layer such as constant layers to model the border, when doing reductions */
      val usedLayers = toSet(newDagis.visitedL.flatMap(_.exps).flatMap(_.symbolsofLayers))
      for (name <- usedLayers)
        newtSymbVar.addOne((name -> p.tSymbVar(name)))


      new DataProg(newDagis, mutable.HashMap.empty, newtSymbVar, fparamDwithoutR, fparamRname).treeIfyParam() //the parameter needs to be treeified

    }
    def NeedBuiltFunOld(finstrs: Iterable[Instr]): Boolean = {
      for (i <- finstrs.filter(_.isInstanceOf[Affect[_]])) if (!i.asInstanceOf[Affect[_]].exp.asInstanceOf[ASTL.ASTLg].justConcatsorBroadcast) return true;
      false
    }
    if (isLeafCaLoop) return p
    /** predicate defining connected component forming macros
     *
     * @param src    instruction creating a field $f
     * @param target instruction using that field
     * @return true if src and target should be in the same macro
     */
    def proximity(target: Instr, src: Instr): Boolean =
      src match {
        case Affect(name, exp) => !needStored(name) && //condition 1= field created by source must not be stored
          (target match {
            case CallProc(namep, _, _) => Instr.isProcessedInMacro(namep) //condition 2 =if target is a system call, it should be memo
            case Affect(nametarget, exptarget)  =>
             // if(tSymbVarSafe(nametarget).)
              true
          })

        case _ => false
      }

    val newFuns: TabSymb[DataProg[InfoNbit[_]]] = mutable.HashMap.empty

    /**
     *
     * @return generates function name of the form _fun1,_fun2...
     */
    def newFunName(): String = "_fun" + Named.getCompteur("_fun")

    /**
     * @param finstrs instructions forming a connected component
     * @return true if the instructions use only  concat or elt
     *         or Broadcast (which can also be treated in non-leaf by copying formal argument,]
     *         in which  case  it is not necessary to create a function,
     */
    def NeedBuiltFun(finstrs: Iterable[Instr]): Boolean = {
      for (i <- finstrs) i match {
        case Affect(_, e) => if (!e.asInstanceOf[ASTL.ASTLg].justConcatsorBroadcast) return true
        // we must test callProc to memo, because memo is authorised to have effective arguments which are not variables
        case CallProc("memo", _, List(e)) => if (!e.asInstanceOf[ASTL.ASTLg].justConcatsorBroadcast) return true
        case _ => {}
      }
      return false
    }

    /**
     * @param g instructions forming a connected component
     * @return a CallProc to a  function that is created as a side effect, from those instructions.
     */
    def transform(g: Iterable[Instr]): List[Instr] = {
      if (!NeedBuiltFun(g))
        return g.toList
      val name = newFunName()
      newFuns.addOne(name -> builtFun(g))
      List(CallProc(name, newFuns(name))) //replaces the list of instruction by a CallProc to the new created function
    }
    def processCyclePairs(vars:Set[String])=
      for(v<-vars)
        storeFieldise2(v)



    //we sort the instructions of dagis, in order to obtain a deterministic labeling of automaticaly defined macro,
    // turn out it is necessary to sort
    // but later: we sort the components when macroifying
    //System.out.println(sortedDagis)
    val newDagis: Dag[Instr] = dagis.quotient2(proximity,processCyclePairs, transform)


    val stillUsed: Set[String] = HashSet() ++ newDagis.visitedL.flatMap(_.names)
    val newTsymbVar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    //we filter out macro Fields
    for ((name, info) <- p.tSymbVar)
      if (info.k != MacroField())
        newTsymbVar.addOne(name -> info)
      else if (stillUsed.contains(name)) //due to the fact that some operator can be processed on the main(broadcast, elem, even clock and anticlock)
      //some of the macroField are not macroified. we check which one, just by lookikng wether they are still in use in the new main instructions
        newTsymbVar.addOne(name -> info.storedFieldise2)
    new DataProg(newDagis, newFuns ++ funs.map { case (k, v) ⇒ k -> v.macroify() }, newTsymbVar, paramD, paramR)
  }


  /**
   * @return for redop wich are also result parameters, we introduce an intermediate macroField,
   *         toto<-reduce remains  toto<-reduce  but toto is now a macrofield
   *         and a suplementary affectation stores toto into totoR which is now the  paramR,
   *         this manipulation will spare read and writes from CA 's memory
   */
  def addParamRtoDagis2(): DataProg[InfoNbit[_]] = {
    /** @param paramR
     * @return finds out if an "R" has been added due to the fact that it was a result used to compute a redop
     *         if so, modifies the result's name fuck it produced
     *         a bug, because I used R also to name a subfield of the main field.
     */
    def addsAnR(paramR: String) = if (tSymbVar.contains(paramR + "R")) paramR + "R" else paramR

    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (!p.isLeafCaLoop || p.isRootMain) //in one extreme case the root main is also a CA loop!
      return new DataProg(p.dagis, funs.map { case (k, v) => k -> v.addParamRtoDagis2() },
        p.tSymbVar, paramD, paramR.map(addsAnR(_)))
    val rewrite1: Instr => List[Instr] = (i: Instr) => a(i).insertMacroFieldbeforeReduceParamR(p.tSymbVar)
    new DataProg(p.dagis.propagate(rewrite1), noSubFun, p.tSymbVar, paramD, paramR.map(addsAnR(_))) //no coalesced registers
  }


  /**
   * @param constraints permutation constraints computed during alignment
   * @param alignPerm   alignment between instruction updating a given variable obs Dag contains shift instructions
   * @return a dag of zones  with constraints, a map that finds the root of an instructions ,the alignement to root
   */
  def zones2(constraints: TabSymb[Constraint], alignPerm: Map[(String, String), Array[Int]]): (Dag[Zone],
    Map[String, Instr], Map[String, Array[Int]]) = {
    val hasToAlign: Instr => Boolean = (i: Instr) => i.isTransfer //only transfer zone must align their instructions on a root
    /**
     * used to build zone defined as connected components of identical locus: transfer or simplicial
     * we start by target which is the fist component and tries to add source which is the second comonent
     * * second component is source, therefore the first can be callProc */
    val proximity2: (Instr, Instr) => Boolean =
      (x: Instr, y: Instr) => x.isTransfer == y.isTransfer &&
        !x.isV && !y.isV && //V nodes are isolated
        !y.shiftandshifted(x) //toto is an inputneighbors of shiftoto, but it is a fake binding used to
    //ensure that shiftoto is scheduled after toto's affectation,
    // this fake binding is identified  using the predicate shiftandshifted and then neutralized
    // because it must no be used to compute alignement to root.

    // we cannot do a quotient easily, because the quotient computes align2root and align2root is used to build zones
    // we first computes connected component,

    val (
      /** connected component forming zones */
      groupNodes: Iterable[List[Instr]],

      /** alignement to root */
      align2root: Schedule,

      /** map from instruction to root instruction */
      myRoot: Map[String, Instr]) = dagis.alignedComponents(proximity2, alignPerm, hasToAlign) //an alignement is computed on  T's.


    def transform(g: Iterable[Instr]): List[Zone] = List(Zone(constraints, g.asInstanceOf[Iterable[Affect[_]]], alignPerm, align2root,
      myRoot.asInstanceOf[Map[String, Affect[_]]]))

    val newDagNodes = groupNodes.flatMap(transform).toList
    WiredInOut.setInputAndOutputNeighbor(newDagNodes)
    val newGenerators = newDagNodes.filter({ case a: WiredInOut[_] => a.outputNeighbors.isEmpty; case _ => true }) // generators are dagNodes with no output
    //this version does not take into account the presence of cycles
    // generators should rather be defined as zone which contains generator of former dag.
    val formerGenerators = dagis.allGenerators.toSet.asInstanceOf[Set[Affect[_]]]
    val newGenerators2 = newDagNodes.filter(z => (formerGenerators.intersect(z.instrs.toSet)).nonEmpty)
    /**
     * Building of zonedag assumes that the zones form a Dag, it could fail,
     * Possible cycles will be detected during dag constructionin
     * in this case, we should look back to the code
     * and split the macro in two, ( by adding an addistional show), so as to remove the cycle
     * a Dag for zones simplifies a lot the following picking phase
     */
    val zoneDag = new Dag(newGenerators2) //reconstruct dag from generators,

    zoneDag.visitedL.map(_.addPartitionOut()) //set partition constraints towards output neighbors
    //now we know if the TCC will fold, before we pick, we could try to further constrain the cycle so as to reuse
    //delayed variables in order to avoid introducing new registers
    zoneDag.visitedL.map(_.setFoldConstrSimplicial())
    (zoneDag, myRoot, align2root)
  }

  /**
   *
   * @return in the varkind of the symbol table, we replace ParamR by ParamRR(r) where r is the radius
   *         computed with respect to index in the bit plane (and not the distance)
   *         we add delays in exoression,  if a binop is applied to two expression of distinct radius.
   */
  def radiusify3: DataProg[InfoNbit[_]] = {
    val radius: TabSymb[Int] = mutable.HashMap.empty //stores all the radius of the id in that symbol tables.
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (isLeafCaLoop) {
      val rewrite: Instr => Instr = (i: Instr) => i.radiusify3(radius, p.tSymbVar)
      dagis.propagateUnitKeepSchedulereverse(rewrite)
    }
    //dagis.visitedL=dagis.visitedL.reverse.map(_)
    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.radiusify3 }, p.tSymbVar, paramD, paramR, coalesc)
  }
  /*

    def radiusify2: DataProg[InfoNbit[_]] = {
      val radius: TabSymb[Int] = mutable.HashMap.empty //stores all the radius of the id in that symbol tables.
      val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
      if (isLeafCaLoop)
        dagis.visitedL = dagis.visitedL.reverse.map(_.radiusify3(radius, p.tSymbVar))
      new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.radiusify2 }, p.tSymbVar, paramD, paramR, coalesc)
    }

    def radiusify: DataProg[InfoNbit[_]] = {
      val radius: TabSymb[(Int, Option[Modifier])] = mutable.HashMap.empty //stores all the radius of the id in that symbol tables.
      val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
      if (isLeafCaLoop)
        dagis.visitedL.reverse.map(_.radiusify(radius, p.tSymbVar))
      new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.radiusify }, p.tSymbVar, paramD, paramR, coalesc)
    }
  */

  /**
   * @param m models the "machine"'s communications
   * @param d
   * @return a first simple version of muInstructions that does not fold reduction and does not consider shift
   */

  private def muInstr(m: Machine, d: DagInstr): Map[String, List[Instr]] = { //: (Map[String, List[Instr]],TabSymb[InfoNbit[_]] )
    require(isLeafCaLoop)
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var muIs: iTabSymb2[List[Instr]] = HashMap.empty
    //val tZone: Map[String, Zone] = DagInstr.defby(zones.visitedL)
    for (i <- d.visitedL) muIs += a(i).name -> i.unfoldSpace(m, p.tSymbVar)
    muIs
  }

  /**
   *
   * @param d
   * @return computes the mu Instructions of a main (non-leaf CA loop), which remains in the same order,
   *         no scheduling needed.
   *         returns also the symbol table with added scalar
   */
  private def muInstrMain(d: DagInstr): (List[Instr], TabSymb[InfoNbit[_]]) = { //: (Map[String, List[Instr]],TabSymb[InfoNbit[_]] )
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    for ((name, info: InfoNbit[_]) <- p.tSymbVar) {
      tSymbScalar.addOne(name -> info)
      val names = info.locus.deploy(name)
      for (n <- names) {
        if (n != name) //we do not want to remove spatial information
          tSymbScalar.addOne(n -> tSymbVar(name).asInstanceOf[InfoNbit[_]].scalarified) //for main function, we unfold systematically all the variables
      }
    }
    (d.visitedL.flatMap(_.unfoldSpace(null, p.tSymbVar)), tSymbScalar)
  }


  private def deploySpace(s: String) = tSymbVar(s).locus.deploy(s)


  /**
   *
   * @param m encodes all the communication which in fact happens between transfer loci
   * @return a data prog where now instruction are scalar instructions, however, the symbol table still contains
   *         spatial type (a scalar type, plus a locus). This avoid an explosion of symbol,
   *         it is the coalesc map which allows to find out the type of a given used variable
   *         the variable used are no longer the one in the symbol table. They are the on in the values of the coalesced map
   */

  def redopConcats = dagis.visitedL.flatMap({ //identifies which are the concat
    case Affect(name, x) =>
      if (x.toString.startsWith("redconcat2")||x.toString.startsWith("redconcaat2")) Some(name) else None //name of a reduction is red+name of operator concat2
    case _ => None
  })
  def unfoldSpace(m: Machine): DataProg[InfoNbit[_]] = {
    if (!isLeafCaLoop) {
      val (muI, tSymbScalar) = muInstrMain(dagis) //computes the muI associated to a callProc and direct affectation, and the modified symbolTable.
      return new DataProg(DagInstr(muI.reverse), funs.map { case (k, v) => k -> v.unfoldSpace(m) },
        tSymbScalar, paramD.flatMap(deploySpace(_)), paramR.flatMap(deploySpace(_)), HashMap.empty) //no coalesced registers we put empty to enforce schedule matters
    }
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    /** tabAlign((i1,i2) stores alignement of i1's result with respect to i2's result, i2's name must be used by i1 */
    val tabAlign: mutable.Map[(String, String), Array[Int]] = mutable.HashMap.empty
    /** used to collect econstraint  generated when aligning */
    val cycleConstraints: TabSymb[Constraint] = mutable.HashMap.empty

    /** adds shift instruction to dataProg
     * as a side effect, it also computes alignement and constraints due to shifts */
    def alignShift() = {
      val rewrite2: Instr => List[Instr] = (i: Instr) =>
        if (i.isTransfer)
          a(i).align2(cycleConstraints, p.tSymbVar, tabAlign) //only transfer instructions needs to compute alignement
        else List(i)
      /** dagis completed with shift instructions */
      val dagisWithShift: DagInstr = dagis.propagate(rewrite2)
      //  print("ererererererererererererererererererererererererererererererererererererererererererererer\n" + dagis2)
      if (!cycleConstraints.isEmpty)
        println("Constraint: " + cycleConstraints) //we check constraints generated
      //for (i <- dagisWithShift.visitedL) i.reset //will become useless soon
      for (i <- dagisWithShift.visitedL) //adds the names of shifted variables introduced If cycles where present)
        if (i.isShift) {
          val n = a(i).name
          val d: InfoNbit[_] = p.tSymbVar(n.drop(5)) //info about not shifted variable
          p.tSymbVar.addOne(n, new InfoNbit(d.t, d.k, d.nb))
        }
      new DataProg(dagisWithShift, noSubFun, p.tSymbVar, paramD, paramR)
    }

    val p2: DataProg[InfoNbit[_]] = alignShift() //produces tabAlign, introduit deux shifts.
   // print(tabAlign.map({ case (k, v) => "" + k + v.toSeq }))
    //println("dag produced by alignShift\n" + p2) //display result of  alignShift.

    //we have computed cycle cosntraint due to shift, in cycleConstraints
    //we now compute sendCosntraint due to send. between the source Ev, and the reconstitute target Ev
    val binopEdgeConstraints: TabSymb[Constraint] = mutable.HashMap.empty //wi
    val binopEdgeInstrs=p2.dagis.visitedL.filter ((i:Instr) => {i match {
      case Affect(n,e:ASTLtG) => e.isBinopEdge
      case _ => false
    }} ).asInstanceOf[List[Affect[_]]]
    if(binopEdgeInstrs.nonEmpty) {
      for(i<-binopEdgeInstrs) if(i.inputNeighbors.size>0) {  //it can be the case that the dev field is used twice and stored, in which case there is no more cosntraints to register        val dev=i.inputNeighbors(0).asInstanceOf[Affect[_]]
        val dev=i.inputNeighbors(0).asInstanceOf[Affect[_]]
        if(dev.locus.get ==T(E(),V()))
          binopEdgeConstraints(dev.name)= H1beforeH2 (dev.locus.get) //send is used in combination with binop, and should be
        else
        {
          print(dev.locus.get)
          //on tente le meme truc
          binopEdgeConstraints(dev.name)= H1beforeH2 (dev.locus.get) //send is used in combination with binop, and should be
        }

        //constrained h1 before h2, d1 before d2, ad1 before ad2, because of      }
      }}

/*    val sendConstraints: TabSymb[Constraint] = mutable.HashMap.empty //will be indexed by name defined by send Instructions
    val sendInstrs=p2.dagis.visitedL.filter ((i:Instr) => {i match {
       case Affect(n,e:ASTLtG) => e.isSend
        case _ => false
    }} ).asInstanceOf[List[Affect[_]]]
   if(sendInstrs.nonEmpty) {
     println("ici")
     for(i<-sendInstrs) {
       val dev=i.inputNeighbors(0).inputNeighbors(0).asInstanceOf[Affect[_]]
       sendConstraints(dev.name)= H1beforeH2 (i.locus.get) //send is used in combination with binop, and should be
         //constrained h1 before h2, d1 before d2, ad1 before ad2, because of      }
   }}*/
   val computedConstraint: TabSymb[Constraint] = mutable.HashMap.empty
    computedConstraint++= cycleConstraints
    computedConstraint++= binopEdgeConstraints//au lieu de sendConstraints qu'on jette
    val (z2: Dag[Zone], myRoot: Map[String, Instr], align2root: Map[String, Array[Int]]) = p2.zones2(computedConstraint, tabAlign) //send Constraint will endup in the right zone.

    //println(z2) //displays zone,
    val tZone2: Map[String, Zone] = defby(z2.visitedL) //associe une root a une zone.
    val defI2: Map[String, Instr] = p2.dagis.defby

    /*//Now, we need to update the src field of each sendConstraint.
    for(sendConstraint<- sendConstraints.values){
      val aligned=sendConstraint.asInstanceOf[Aligned]
      val instr: Affect[_] =aligned.srcInstr
      val root=myRoot(instr.name)  //root Instruction
      val zone=tZone2(root.names.head)
      aligned.src=zone
    }*/


    val muI10: Map[String, List[Instr]] = muInstr(m, p2.dagis)

    z2.visitedL.reverse.map(_.pick()) //pick one schedule for each zone, starting from the first instruction
    //println(z2)

    var (muI12: Map[String, List[Instr]], tSymbScalar2, coalesc2) = permuteAndFixScheduledMu(muI10, p2.dagis, tZone2, defI2, myRoot, align2root) // revisit muI 's'reduce when reduced exression is folded
    //we separate the reduction in two parts: one that can do at tm1 and the rest that is done now.
    //concat needs to preserve the order, but it will, since whhats concatenated is already in sync whith the result of concatenation

    // simplifConcat will replace toto_4 <- concat(toto_3,exp) par toto#4 <-exp


    val redconc=redopConcats
    for (name <- redconc) {
      val i = defI2(name)
      assert(tSymbVar(name).locus == V(), "for the moment we concatenate only on vertice") //
      if (i.inputNeighbors.nonEmpty) {
        muI12 = muI12 + (name -> (muI12(name).map(_.simplifConcat()))) //triger in a shift in the indexes #0 is the last to be affected

        for (i <- 0 to 5) //we also need to add the toto#i in tsymbVar
          tSymbScalar2.addOne(name + "#" + i -> new InfoNbit[B](B(), tSymbVar(name).k, 1))
        val youpi = 0
      }
    }


    val muI13: List[Affect[_]] = scheduleMuCode(muI12, p2.dagis, defI2, tZone2, myRoot).toList.asInstanceOf[List[Affect[_]]]
    val iT2 = DagInstr(muI13).inputTwice.filter(isNotRead) //we exploit the DAG form to find out about usedTwice exp, we did not used it yet!!!
    //if the factorized expression is just a << or >> as it is now ?? we better just recompute it
    //print("____|____|____|____|____|____|____|____|____|____|____|____|\n"+muI3)  //printing this for debug is usefull because we see which component is processed
    val muI14 = muI13.map(_.coalesc(coalesc2))
    //adds paramD to symbol Table WITH the suffx for specifying direction, since paramD will be deployed.
    //paramR are also deployed but their case is already  handled correctly in the symboltable
    for ((name, info: InfoNbit[_]) <- p.tSymbVar) {
      if (info.k == ParamD() || info.k.isInstanceOf[ParamRR] || info.k.isInstanceOf[LayerField]) {
        //we unfold paramD and paramR and also layerField, which can be there for constant layers
        for (nameWithSufx <- deploySpace(name))
          tSymbScalar2.addOne(nameWithSufx -> info)
        //if (info.locus != V()) tSymbScalar2.remove(name)
        // the prior infoTab must be removed from the symbol Table, for V there is no suffixes, this is why it is special
        if (info.locus != V()) tSymbScalar2.addOne(name -> info) //TODO just changed, ca risque de creer du bordel

      }

    }
     new DataProg(DagInstr(muI13), noSubFun, tSymbScalar2, paramD.flatMap(deploySpace(_)), paramR.flatMap(deploySpace(_)), coalesc2)

  }

  /**
   *
   * @param muI        list of  muInstructions grouped per instruction's defined name, the order in the list is the canonical order, given by the locus
   * @param dagis      instructions needed to compute
   * @param tZ         map of zones
   * @param defI       maping a name to the instruction defining it
   * @param myRoot     mapping a name to the root instruction
   * @param align2root alignement on root
   * @return hashmap of muInst associated to inst, the order in the list encodes the schedule
   *         scalar symbol table, when instruction has been folded
   *         coalesced map of registers
   */
  def permuteAndFixScheduledMu(muI: Map[String, List[Instr]], dagis: DagInstr, tZ: Map[String, Zone],
                               defI: Map[String, Instr],
                               myRoot: Map[String, Instr], align2root: Map[String, Array[Int]]):
  (HashMap[String, List[Instr]], TabSymb[InfoNbit[_]], iTabSymb[String]) = {
    var oldmuI = muI //it will be modified to remove the tm when doing reduction
    var newMuI: HashMap[String, List[Instr]] = HashMap.empty
    /** stores the name and type of variables produced by spatial unfolding, after register are coalesced */
    val tSymbScalar: TabSymb[InfoNbit[_]] = mutable.HashMap.empty
    /** stores a mapping to coalesced registers    */
    var coalesc: iTabSymb[String] = HashMap.empty

    /** ****************
     *
     * @param name variable affected by an instruction
     * @return muInstVector  associated to instr, now scheduled
     *
     */
    def permuteAndFixScheduledMu2(name: String): List[Instr] = {
      def isJustReadingLayer(i: Instr): Boolean = {
        i match {
          case Affect(name, exp) => exp match {
            case Read(which) => tSymbVarSafe(which).k.isLayerField
            case _ => false
          }
          case _ => false
        }
      }

      if (!defI.contains(name))
        throw new Exception("pas trouvé" + name)
      val i = defI(name) //instruction
      if (newMuI.contains(name)) return newMuI(name) //muInstruction's new schedule has already been computed
      val permuted: List[Instr] =
        if (a(i).isRedop)
          foldRedop(a(i))
        else if (a(i).isBinopEdge) {
         // val s: Array[Int] = i.mySchedule2(tZ, myRoot, align2root)
          foldBinopEdge(a(i))
        } else if (i.isV)
          oldmuI(name) //simplest case
        else if (i.isFolded2(tZ, myRoot)) {
          if (i.isShift)
            foldShift(a(i))
          else {
            val s: Array[Int] = i.mySchedule2(tZ, myRoot, align2root) //get the schedule computed when slicing in zones.
            if (s != null)
              dataStruc.Align2.compose2(s, oldmuI(name).toArray).toList
            else
              throw (new Exception("problem in aligning on root"))
          }
        }
        else if (!i.isTransfer)
          oldmuI(name) //canonical order, no need to permute
        else throw (new Exception("look more closely why transfer zone is not folded in order to guess what to do"))
      newMuI += name -> permuted;
      // computes coalesc mapping and tSymbScalar
      if (!a(i).isRedop) { //for redop the coalesc mapping and tSymbScalar are already done
        val l = a(i).locus.get
        val names = l.deploy(i.names.head)
       // on update coalesc si c'est folded
        if (i.isFolded2(tZ, myRoot) && !tSymbVar(i.names.head).k.isInstanceOf[ParamRR] &&  !isJustReadingLayer(i)) {
          for (n <- names)
            coalesc += (n -> i.names.head) //we register the fact that  several symbol are coalesced
          //and we add the single coalesced symbol
          tSymbScalar.addOne(i.names.head -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]])
        }
        else {
          tSymbScalar.addOne(name -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]]) //adds spatial type
          for (n <- names) //no coalesced needed, instead we add several symbols
            tSymbScalar.addOne(n -> tSymbVar(i.names.head).asInstanceOf[InfoNbit[_]].scalarified) //adds scalar type
        }
      }
      permuted
    }
    /**
     *
     * @param i instruction doing the affect
     * @return scheduled  muinstruction for foldBinopEdge.
     *         it depends wether the reduced field is folded or not
     *         Reduction can happen in successive step to optimize register use
     *         a suffix #1 #2 #3 is appended to indicate which stage we are
     **/
    def  foldBinopEdge(i: Affect[_]): List[Instr]={

      val isFolded = i.isFolded2(tZ, myRoot)
      if (!isFolded | i.inputNeighbors.size==0) //abracadabra
        return oldmuI(i.name)
         //todo faut vérifier l'ordre en regardant le schedule des zones.
         val input: Instr =i.inputNeighbors(0)
      val schedulei=i.mySchedule2(tZ, myRoot, align2root) //1,0,2,3,4,5
      val scheduleInput=input.mySchedule2(tZ, myRoot, align2root) //1,0,2,3,4,5
      val locusInput: Locus =input.locus.get
      val locusRing=input.ring.get //UI
      val tbit = tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]]
      val nbit=
        if(tSymbScalar.contains(input.names.head))
          tSymbScalar(input.names.head).nb
        else
          tbit(input.names.head).nb
      val newVar=newAuxTmp() //we need a tmp variable
      tSymbScalar.addOne(newVar -> new InfoNbit(locusRing, MacroField() , nbit) )//(name + "#" + i -> new InfoNbit[B](B(), tSymbVar(name).k, 1)
      var result:List[Instr]=List()
      val treeInstr: List[Instr] =oldmuI(i.name)
      val call2=treeInstr(0).asInstanceOf[Affect[_]].exp.asInstanceOf[Call2[_,_,_]]
      val f=call2.f.asInstanceOf[Fundef2[UI,UI,_<:Ring]]//.asInstanceOf[Fundef2RB[Ring]]
        for(k<-0 until 3){
          val resSufx=E().the6sufx(schedulei(k))
         // In case of binop, we force the order, because the op in the binop may not be symmetric; example is lt
         val arg1Sufx=locusInput.the6sufx(scheduleInput(2*k))
         val arg2Sufx=locusInput.the6sufx(scheduleInput(2*k+1))
          result=result:::dedouble2(i.name+"$"+resSufx, newVar, f, input.names.head + "$"+arg1Sufx, input.names.head + "$"+arg2Sufx)(f.body.mym.asInstanceOf[repr[Ring]])
      }

     // val binop=call2.f.asInstanceOf[Fundef2RB[Ring]]
    //  val res=dedouble2( ,newVar,binop,Instr.readR(,r) )

     // def reduceR(a1: ASTBg, a2: ASTBg, opred: redop[Ring], m: repr[Ring]) =  new Call2(opred._1, a1, a2)(m) with ASTBt[Ring]

      def dedouble2[To1 <: Ring](nameEdge: String, newTmp: String, f: Fundef2[UI, UI, To1], arg1: String, arg2: String)(implicit reprTo1: repr[To1]): List[Instr] = {
        val ui = new repr[UI](UI())
        val instr1 = Affect(newTmp, readR(arg1, ui))
        val instr2 = Affect(nameEdge,
          new Call2[UI, UI, To1](f, Instr.readR(newTmp, ui).asInstanceOf[AST[UI]], Instr.readR(arg2, ui).asInstanceOf[AST[UI]]  ) with  ASTBt[To1] )
        List(instr1, instr2)
      }

/*      def dedouble2(nameEdge:String, newTmp:String, f:Fundef2[UI,UI,_<:Ring],arg1:String,arg2:String):List[Instr]={
         val r=new repr[Ring](new Ring())
        val ui=new repr[UI](UI())
        val instr1=Affect(newTmp,readR(arg1,ui))
        val instr2=Affect(nameEdge, new Call2(f,Instr.readR(newTmp,ui) , Instr.readR(arg2,ui)) with ASTBt[UI])
      List(instr1, instr2)
      }*/

      result
      //List(i)
    }
    /**
     *
     * @param i instruction doing the affect
     * @return scheduled  muinstruction for redop.
     *         it depends wether the reduced field is folded or not
     *         Reduction can happen in successive step to optimize register use
     *         a suffix #1 #2 #3 is appended to indicate which stage we are
     **/
    def foldRedop(i: Affect[_]): List[Instr] = {
      /**
       *
       * @param name   instruction's name
       * @param muName muInstruction that should be removed tm1
       */
      def detm1ise(name: String, muName: String) = {
        oldmuI = oldmuI + (name -> oldmuI(name).map(
          _.detm1ise(muName)))
      }

      val op = a(i).exp.asInstanceOf[ASTL[_, _]].opRedop
      //it is possible that we directly reduce a data parameter, then there is no input neighbors,
      val isFolded = i.isFolded2(tZ, myRoot)

      if (i.inputNeighbors.isEmpty) {
        //sinon je sais pas faire encore faut réfléchir
        if (isFolded || tSymbVar(i.name).locus == V()) {
          val l = a(i).locus.get.asInstanceOf[S]
          //  if(tSymbVar(i.name).locus != V()){

          for (scalarName <- l.deploy(i.name))
            coalesc = coalesc + (scalarName -> i.name) //sert a rien si scalarName=i.name, si locus =V
          tSymbScalar.addOne(i.name -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))
        }

        else {
          assert(false, "je sais pas faire")
        }
        return oldmuI(i.name)
      }
      val inputInst = i.inputNeighbors.head

      if (!inputInst.isFolded2(tZ, myRoot)) oldmuI(i.name) // if reduced field is not folded we leave as it was:a single expression
      else {
        val l = a(i).locus.get.asInstanceOf[S]
        val r1 = a(i).ring.get
        val r = repr(r1).asInstanceOf[repr[Ring]]
        val d = l.density
        val cpt = Array.fill[Int](d)(0) //used to suffix name
        val cptTm1 = Array.fill[Int](d)(0) //used to suffix name of delayed sum
        val tm1Sum: Array[Int] = Array.fill[Int](d)(0) //number of delayed for each component
        val result = new Array[Instr](6)
        val names = l.deploy(i.name)
        val iInputMuInsts: Array[Instr] = oldmuI(inputInst.names.head).toArray //inputNeighbor which is reduced
        val inputShedule: Array[Int] = inputInst.mySchedule2(tZ, myRoot, align2root) //schedule of inputNeighbor
        val iInputMuInstOrdered = Align2.compose2(inputShedule, iInputMuInsts)
        for (j <- 0 to 5)
          tm1Sum(l.proj(inputShedule(j))) +=
            (if (iInputMuInstOrdered(j).exps(0).asInstanceOf[ASTBt[_]].isTm1) 1 else 0)
        val isTm1 = iInputMuInstOrdered.map(_.exps.head.asInstanceOf[ASTBt[_]].isTm1)
        val scheduleOfLastAffectedTm1 = isTm1.lastIndexOf(true)
        val nbDelayed = isTm1.filter(_ == true).size
        // val optionalPrefix = if (tSymbVar(i.name).k == ParamR()) "#Reg" else ""
        for (j <- 0 to 5) { //for folding of input  to work, the reduction must accumulate
          val iInputMuInst: Affect[_] = a(iInputMuInstOrdered(j)) //muInst read
          val numI = l.proj(inputShedule(j)) //numI select the target component of the simplicial vector produced by redop
          if (tm1Sum(numI) < 2 || op._1.name.equals("concat2")|| op._1.name.equals("concaat2")) //it is not worth/not possible to be doing a delayed sum,or it is risky because concat cannot be reordered
          {
            val nameOfAffectedPrevious = names(numI) + "_" + cpt(numI)
            cpt(numI) += 1;

            val nameOfAffectedNow = names(numI) +
              (if (cpt(numI) * d >= 6) "" else "_" + cpt(numI)) //last affected component does no get an integer prefix
            val coalescedName = (if (i.isFolded2(tZ, myRoot) || i.isV) i.name else names(numI)) //+ (if (cpt(numI) * d >= 6) "" else optionalPrefix)
            coalesc += (nameOfAffectedNow -> coalescedName)
            tSymbScalar.addOne(coalescedName -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))
            val iInputMuInstName: String = iInputMuInst.names.head
            val readNextMuVar = Instr.readR(iInputMuInstName, r)
            val readCurrentRedVar = Instr.readR(nameOfAffectedPrevious, r)
            val newMuInstrExp =
              if (cpt(numI) == 1) readNextMuVar //the first myInstruction is a simple affectation
              else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
                op.asInstanceOf[redop[Ring]], r)
            result(j) = Affect(nameOfAffectedNow, newMuInstrExp)
          }
          else //we do a delayed sum with at least two term in it
          {
            val cptt = if (isTm1(j)) cptTm1(numI) else cpt(numI)
            val iInputMuInstName = iInputMuInst.names.head
            detm1ise(inputInst.names.head, iInputMuInstName) //correct oldMui, remove the tm1
            newMuI = newMuI - inputInst.names.head
            permuteAndFixScheduledMu2(inputInst.names.head) //recompute newMui from oldMui
            val tm1Opt = if (isTm1(j)) "tm1" else "" //suffixe optionnel a rajouter
            val nameOfAffectedPrevious = names(numI) + tm1Opt + "_" + cptt
            if (isTm1(j)) cptTm1(numI) += 1 else cpt(numI) += 1;
            val onlyTm1 = tm1Sum(numI) * d == 6
            val onlyTm1Last = onlyTm1 && cptTm1(numI) == tm1Sum(numI) //true for final reduction when only tm1
            val firstNonTm1 = (cpt(numI) == 1) && !(isTm1(j))
            val lastNonTm1 = ((cpt(numI) + tm1Sum(numI)) * d == 6) && (!isTm1(j)) // representing the reduction for each component
            val lastTm1 = (cptTm1(numI) == tm1Sum(numI)) && (isTm1(j)) // representing the reduction for each component
            val nameOfAffectedNow = names(numI) + (if (onlyTm1 && lastTm1) "" else //when there is only tm1 then the last term has no prefix
              (tm1Opt +
                (if (lastNonTm1) "" else ("_" + (cptt + 1))) //last affected component does no get an integer prefix
                ))
            val coalescedName = if (i.isFolded2(tZ, myRoot) || i.isV) i.name else names(numI)
            val coalescedNameTm1 = coalescedName + (if (!onlyTm1Last) tm1Opt else "") //precise the name by adding "tm1"
            coalesc += (nameOfAffectedNow -> coalescedNameTm1)
            tSymbScalar.addOne(coalescedNameTm1 -> tSymbVar(i.name).asInstanceOf[InfoNbit[_]]) //.regifyIf(coalescedName != names(numI)))
            val readNextMuVar = Instr.readR(iInputMuInstName, r)
            val nameOfFinalAffectedTm1 = names(numI) + "tm1" + "_" + tm1Sum(numI)
            //iInputMuInstOrdered(scheduleOfLastAffectedTm1).names.head+"tm1#" + nbDelayed
            val readCurrentRedVar =
              if (firstNonTm1) //we retrieve the other sum using a tm1, it introduces another Z variable, to be removed later
                ASTB.tm1(Instr.readR(nameOfFinalAffectedTm1, r))(r)
              else
                Instr.readR(nameOfAffectedPrevious, r)
            val newMuInstrExp =
              if (cptTm1(numI) == 1 && isTm1(j)) readNextMuVar //the first myInstruction is a simple affectation
              else Instr.reduceR(readCurrentRedVar, readNextMuVar, //the other apply the binary operator of the muInstruction
                op.asInstanceOf[redop[Ring]], r)
            val newMuInstrExpTm1 = if (onlyTm1Last) ASTB.tm1(newMuInstrExp)(r) else newMuInstrExp
            result(j) = Affect(nameOfAffectedNow, newMuInstrExpTm1)
          }
        }
        result.toList
      }
    }
    /**
     *
     * @param i shifting instruction
     * @return muInstr generated from a shift are computed using specific processing implementing a rotation from the unshifted
     */
    def foldShift(i: Affect[_]) = {
      assert(i.isShift) //i must be a shift
      val muInstUnShift = permuteAndFixScheduledMu2(i.unShifted) //we compute the shift schedule from the argument's scheduile
      val (_, List(last)) = muInstUnShift.splitAt(5) //isolate last instruction/we put last instruction first
      val Ishifted: Instr = defI(i.unShifted) //apply same permutation as muInstUnShift
      val s2 = Ishifted.mySchedule2(tZ, myRoot, align2root)
      val permutedMuShifted = dataStruc.Align2.compose2(s2, oldmuI(i.name).toArray)
      //replace first MUaffectation of permutedMushifted by last MuAffectation
      val inew = Affect(permutedMuShifted(5).names(0), last.exps(0))
      permutedMuShifted(5) = inew
      Util.rotRn(permutedMuShifted, 1).toList
    }
    for (name <- oldmuI.keys)
      permuteAndFixScheduledMu2(name)
    (newMuI, tSymbScalar, coalesc)
  }
  /**
   *
   * @param muI    muInstructions assodciated to instructions
   * @param dagis  instructions
   * @param defI   instruction which defines the variable
   * @param tZone  current zones, used to find out if instruction is folded or not
   * @param myRoot root of instruction, used to find out zone
   * @return produce a list of muInstr in the right order.
   *         shift instruction receives a special processing
   *         1- they exchange priority with the shifted instruction, in order to be scheduled first
   *         2- they supress the shifted instruction from their input neighors, in order to be schedulable first
   *         3- they add the input neighbors of the schifted instruction, so as not to be scheduled too early.
   *
   *
   */
  def scheduleMuCode(muI: Map[String, List[Instr]], dagis: DagInstr, defI: Map[String, Instr], tZone: Map[String, Zone], myRoot: Map[String, Instr]) = {
    /** mu-Instruction left to execute */
    var muI2: Map[String, List[Instr]] = muI //HashMap.empty
    def  allInstructionCleared=muI2.values.filter(_.nonEmpty).isEmpty
    // val tabInstr = dagis.visitedL.toArray
    /** variables using a given instruction */
    var isUsing: HashMap[String, HashSet[String]] = HashMap.empty
    /** variables used by an instruction */
    var usedVar2: HashMap[String, Set[String]] = HashMap.empty
    /** token betweens the  two instructions setting the two variables */
    var token: HashMap[(String, String), Int] = HashMap.empty
    /** the priority corresponding to the topological order */
    var priority: HashMap[String, Int] = HashMap.empty

    /** the real correct order is the opposite */
    def diff(t2: String) = -priority(t2)

    /** the instructions ready are put in a queue with this priority */
    val readyInstr = new collection.mutable.PriorityQueue[String]()(Ordering.by(diff))
    /** the shifts which receives special treatment */
    var shifts: HashSet[String] = HashSet.empty
    /** first instructions to be executed */
    var inputInstr: HashSet[String] = HashSet.empty
    /** instructions without input */
    var inputLessInstr: HashSet[String] = HashSet.empty

    var prio = 0
    var result: List[Instr] = List()
    for (i <- dagis.visitedL) { //initalise the vars: usedVar2, priority, isUsing
      var u = i.usedVars()
      //for shifttoto instruction we must add used(toto) to used (shiftToto) because shiftToto will use the same variable as toto
      if (i.isShift) {
        u /*++=*/ = defI(i.names.head.drop(5)).usedVars()
        shifts += i.names.head
      }
      if (u.isEmpty) inputLessInstr += i.names.head
      usedVar2 += i.names.head -> u
      for (v <- u) {
        isUsing += v -> (if (isUsing.contains(v)) (isUsing(v) + i.names.head)
        else HashSet(i.names.head))
        token += (i.names.head, v) -> 0
      }
      priority += i.names.head -> prio //used in the priority queue
      prio += 1
    }

    def permutePrioShiftWithShifted = {
      for (s <- shifts) {
        val p = priority(s)
        val shifted = s.drop(5)
        priority += s -> priority(shifted)
        priority += shifted -> p
        val u = 1
      }
    }

    /**
     *
     * @param i
     * @return true if contains token on output links
     */
    def noTokenOutput(i: String): Boolean = {
      if (isUsing.contains(i))
        for (i2 <- isUsing(i))
          if (token(i2, i) > 0) return false
      true
    }

    /**
     *
     * @param i   variable name set by an instruction,
     * @param   l locus of instruction
     * @return adds tokens after firing
     */
    def addSeveralToken(i: String, l: Locus): Unit =
      if (isUsing.contains(i))
        for (i2 <- isUsing(i)) {
          val densityOut = tSymbVar(i2).locus.density
          val nbToken =
            if (defI(i).isFolded2(tZone, myRoot))
              Math.max(1, densityOut / l.density) //  >1 if output neigbor has higer density
            else //i triggers only once, and sends all its token which are equal to its density
              densityOut
          token += ((i2, i) -> (token(i2, i) + nbToken)) //adds the token beween i and i2
        }


    /**
     *
     * @param p   name of parameter,
     * @param   l locus of instruction
     * @return adds tokens after firing
     */
    def addSeveralTokenFromParameter(p: String, l: Locus): Unit =
      if (isUsing.contains(p))
        for (i2 <- isUsing(p)) {
          val densityOut = tSymbVar(i2).locus.density
          val nbToken =
          //parameter  triggers only once, and sends to nodes $n$ using it, a count of  token equal to $n$'s density so that $n$ can fires all its muinst
            densityOut //a parameter " triggers " only once
          token += ((i2, p) -> (token(i2, p) + nbToken)) //adds the token beween i and i2
        }


    /**
     *
     * @param i name of an i
     * @return true if each input line of instruction i contains at least one token
     */
    def oneTokenOnEveryInput(i: String): Boolean = {
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          if (token(i, i2) < 1)
            return false
      return true
    }

    /**
     *
     * @param i register set by an instruction
     */
    def consumeToken(i: String) =
      if (usedVar2.contains(i))
        for (i2 <- usedVar2(i))
          token += ((i, i2) -> (token(i, i2) - 1))

    /**
     *
     * @param i
     * @return true if instruction is ready to fire
     */
    def isReady(i: String) = defI.contains(i) && noTokenOutput(i) &&
      muI2(i).size > 0  && oneTokenOnEveryInput(i) //there are still muInstruciolns to schedule

    def isBinopEdge(i:String)=(""+ defI(i).exps.head).startsWith("binopEdge")

    /**
     *
     * @param i
     * if ready, put instruction in priority queue
     */
    def checkReadiness(i: String): Unit = {
      if (isReady(i) && defI.contains(i))
        readyInstr += i
    }
    def init() = {
      //send token to input instructions
      for (p <- paramD) {
        addSeveralTokenFromParameter(p, tSymbVar(p).locus)
        for (n <- isUsing(p)) inputInstr += n
      }
      for (input <- (inputInstr ++ inputLessInstr))
        checkReadiness(input) //it can happen that instructions have no input
    }

    /**
     *
     * @param i
     * @return get the next muInstruction from the already scheduled list associated to i, and removes it from this list
     */
    def nextMuInstr(i: String): Instr = {
      val muInstLeft = muI2(i)
      val res = muInstLeft.head
      muI2 += (i -> muInstLeft.tail) //updates the muInstruction left to be scheduled
      res
    }

    /**
     *
     * @param l      locus of instruction i
     * @param linput locus of input
     * @param i
     * @return computes wether we send or not/=
     *         redop do not send token at each firing, it depends on the fanout
     */
    def weSend(l: Locus, linput: Locus, i: String): Boolean =
      if (!l.isTransfer && linput.isTransfer) //We have a reduction op
      //we here consider the specific case where we reduce a parameter
      {
        val iisfolded = defI(i).isFolded2(tZone, myRoot)
        if (iisfolded)
          (muI2(i).size - 1) % l.fanout == 0  //this has been programmed with reduction in mind
        //muI2(i).size mu instructions left to execute
        else (muI2(i).size == 1) //if its not folded the reduction is done in a single mu instr?I'd rather write true here
      }
      else true

    /**
     * fire an instruction
     *
     * @param i the instruction
     * @return next muInstr executed from $i
     **/
    def fire(i: Instr): Instr = {
      consumeToken(i.names.head)
      val locus = tSymbVar(i.names.head).locus
      val input = usedVar2(i.names.head)
      val singleInputParamD = input.size == 1 && tSymbVar(input.head).k.isParamD //we here consider reduction of a paramD
      if (inputLessInstr.contains(i.names.head) || singleInputParamD || {
        val inputLocus = tSymbVar(usedVar2(i.names.head).head).locus
        weSend(locus, tSymbVar(input.head).locus, i.names.head) //we send will be  sometimes false for reduction . This is a delicate place.
      })
        addSeveralToken(i.names.head, locus)
      nextMuInstr(i.names.head)
    }

    init()

    while (readyInstr.nonEmpty) { //main loop
      val next: Instr = defI(readyInstr.dequeue())
      result = fire(next) :: result
      var neighbors: Set[String] = usedVar2(next.names.head) + next.names.head
      if (isUsing.contains(next.names.head))
        neighbors = neighbors ++ isUsing(next.names.head)
      neighbors.map(checkReadiness(_))
    }
    assert(allInstructionCleared) //si ca marche pas probleme dans le scheduling
    result.reverse
  }

  def coalesc2(str: String) = coalesc.getOrElse(str, str)
  /** if an id x is used a single time, remplace read(x) by its expression.
   * This applies in particular, for transfer happenning just before reduction */
  def simplify(): DataProg[InfoType[_]] = {
    /** do not simplify variable $v$used once, if register (coalec) used for computing $v$ is redefined before $v$ is used */
    def checkIfRedefined(candidateSimplif: Predef.Set[String]): Predef.Set[String] = {
      /** contains variables whose declaration have been visited, but whose use not yet visited */
      var allUsed: HashMap[String, Predef.Set[String]] = HashMap()
      var live: Predef.Set[String] = HashSet()
      var result = candidateSimplif
      for (instr <- dagis.visitedL.reverse) {
        val v = instr.names(0)
        val used = instr.usedVars()
        allUsed += v -> used //we remember variable used for a given ide
        for (u <- used) {
          live -= u; //we know they are used once
        }
        for (l <- live) { //look for redefinition of a register used by l before single use of l
          var cancel = false
          for (usedByl <- allUsed(l))
            if (coalesc2(usedByl) == coalesc2(v)) //we look if l uses a variable that coalesc like v
              cancel = true //if found such variables, we cancel simplification of l
          if (cancel) {
            live -= l
            result -= l //implies not to be simplified
          }
        }
        if (candidateSimplif.contains(v)) live += v;
      }
      result
    }

    /**
     *
     * @param candidateSimplifInstr instruction  candidate for simplification
     * @return true if candidateSimplifInstr does not uses a variable v defined
     *         in the interval [id, output(id)] or [output(id),id], indeed
     *         if it would, than moving candidateSimplifInstr, would change its semantic
     *         due to the fact that v would not contain the same value.
     */
    def checkNotSandwich(candidateSimplifInstr: Affect[_]): Boolean = {
      val List(using) = candidateSimplifInstr.outputNeighbors //there is a single output neighbors because it is used once
      val used = candidateSimplifInstr.inputNeighbors
      val instrs = dagis.visitedL.reverse
      val first = instrs.indexOf(candidateSimplifInstr)
      val last = instrs.indexOf(using)
      val interval = instrs.slice(Math.min(last, first), Math.max(last, first))
      //because of tm1s, it can happen that using(id) comes before id in the instruction list
      used.toSet.intersect(interval.toSet).isEmpty
    }

    val nInstrBeforeSimplif = dagis.visitedL.size
    val p = this.asInstanceOf[DataProg[InfoType[_]]]
    val newTsymbar = p.tSymbVar
    if (isLeafCaLoop) {
      val idUsedOnce: Predef.Set[String] = p.dagis.usedOnce().map(_.names(0)).toSet
      val idUsedOnceNotResult: Predef.Set[String] =idUsedOnce.filter(!tSymbVarSafe(_).k.isParamR)
      val idCandidate4Simplif = checkIfRedefined(idUsedOnceNotResult)
      var defs: Map[String, Instr] = defby(dagis.visitedL)


      val idCand4Simplnotsdwich = idCandidate4Simplif.filter((s: String) => checkNotSandwich(defs(s).asInstanceOf[Affect[_]]))

      val newVisitedL = dagis.visitedL.reverse.map((f: Instr) =>
        if (f.inputNeighbors.map(_.names(0)).toSet.intersect(idCand4Simplnotsdwich).nonEmpty) //f contains some read to be replaced
        {
          val a = new Affect(f.names(0), defs(f.names(0)).exps(0).asInstanceOf[ASTBt[_]].simplify(idCand4Simplnotsdwich, defs))
          defs = (defs + (f.names(0) -> a)) // we update the defs as it might be reused on the fly when we replace a read in an expression which itself will replace another read.      a
          a
        }
        else f
      )
      dagis.visitedL = newVisitedL.reverse.filter((i: Instr) => !idCand4Simplnotsdwich.contains(i.names(0))) //removes the now useless instructions
      WiredInOut.setInputAndOutputNeighbor(dagis.visitedL)
      val nameStillUsed = p.dagis.visitedL.flatMap(_.names).toSet.diff(idCand4Simplnotsdwich)
      val coalescedStillUsed = nameStillUsed.map((str: String) => coalesc.getOrElse(str, str))
      val used = dagis.usedVars
      for (str <- newTsymbar.keys) { //we remove from the table the now useless symbols
        if (str.equals("growvorAsint")) {
          val u = 0
        }
        if (!coalescedStillUsed.contains(str) && !(newTsymbar(str).k == ParamD()) && !(newTsymbar(str).k.isParam)
          && !(newTsymbar(str).k.isLayerField) && !used.contains(str)) {
          //  if (!coalescedStillUsed.contains(str) && !(newTsymbar(str).k == ParamD()) && !(newTsymbar(str).k == ParamD())) {
          newTsymbar.remove(str)
        }
      }
      //dagis.visitedL.map(_.asInstanceOf[Affect[_]].correctName())
      if (dagis.visitedL.size < nInstrBeforeSimplif) simplify() //simplification can enable more simplification!

    }
    //remove from coalesc, symbols no longer in tSymbVar
    val newCoalesc = if (coalesc != null) coalesc.toList.filter((x: (String, String)) => newTsymbar.contains(x._2)).toMap
    else null

    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.simplify }, newTsymbar, paramD, paramR, newCoalesc)


  }


  /** computes a map reInsertionC(nom) if defined it is instruction that should be moved before nom->exp
   * tm1 of an exression using many variables R1<-tm1(exp(R2,... Rn)
   * Rule C; when going towards first instruction, meet one and exactly one affectation for each Ri, i>1, without R1 being used
   * When going towards last instruction, no redefinition of any of the RI
   * R2,..RN  are defined a single time globally we identify that by checking that is not a key of coales.
   * Algo: we maintain the set of Ris still to be met, we also keep the original set.
   * */
  private def movesOfRuleC(instrs: List[Instr]) = {
    var reInsertionC: HashMap[String, String] = HashMap()
    var toBeMet: HashMap[String, Set[String]] = HashMap()

    //it suffices to start by a tm1 (we consider  a simple property) and have name not coalesced
    def checkRuleC(i: Instr, used: Set[String]) = {
      i.exps(0).asInstanceOf[ASTBg].isTm1 && used.intersect(coalesc.keys.toSet).isEmpty &&
        used.toList.filter(isParamR(_)).isEmpty //si on déplace des instruction qui affecte des registres, ca merde pour les indices.
    }

    for (instr <- instrs) {
      var nom = instr.names(0)
      val u: Set[String] = instr.usedVars()
      if (checkRuleC(instr, u)) {
        toBeMet = toBeMet + (nom -> u)
      }
      for (m <- toBeMet) {
        if (u.contains(m._1)||(coalesc.contains(m._1) && coalesc.contains(instr.names.head)&& coalesc(m._1)==coalesc(instr.names.head)))
          toBeMet -= m._1 //case closed negatively
        if (m._2.contains(nom)) {
          if (toBeMet(m._1).contains((nom))) {
            val newToBeMet = toBeMet(m._1) - nom
            if (newToBeMet.isEmpty) {
              toBeMet -= m._1 //case closed positively
              reInsertionC += (nom -> m._1) //record sucess and where to move
            }
            else toBeMet += (m._1 -> newToBeMet)
          }
        }
      }
    }
    reInsertionC
  }

  /**
   *
   * @param reInsertion target is name of instruction to be moved; source is name of instruction where to insert
   * @param instrs
   * @return
   */
  private def detmANDmove(reInsertion: Map[String, String], instrs: List[Instr]) = {
    var tobeMoved: iTabSymb[Instr] = HashMap() //contient l'instruction detmisée auxLO1=auxLO2  detmisése d auxLO1=tm1(auxLO2) insérée trois fois

    val instrSansLesTm=instrs.flatMap(
      (instr: Instr) => {
        val nom = instr.names(0)
        //if(nom=="auxL31")println("ici")

        if (reInsertion.values.toSet.contains(nom)) {
       //   tobeMoved += (nom -> instr.detm1iseHead); //detm1iseR should remove only one tm1, instead of two if there is two. instructions that should be moved
          tobeMoved += (nom -> instr.detm1iseR);
          List()
        }
        else List(instr)
      })
    instrSansLesTm.reverse.flatMap(   //we insert starting from the end of the instruction list,
      (instr: Instr) => {
        val nom = instr.names(0)
        var resu = List(instr)
        if (reInsertion.keys.toSet.contains(nom)&&tobeMoved.contains(reInsertion(nom))) {
          resu ::= tobeMoved(reInsertion(nom))
          tobeMoved-=reInsertion(nom) // and once we inserted once, we stop inserting more by forgeting the resinserted instr, from the twobeMoved map. youpee
        }
        resu
      }

    ).reverse //pour annuler l'autre reverse!
  }
  private def detmANDmoveOld(reInsertion: Map[String, String], instrs: List[Instr]) = {
    var tobeMoved: iTabSymb[Instr] = HashMap() //contient l'instruction detmisée auxLO1=auxLO2  detmisése d auxLO1=tm1(auxLO2) insérée trois fois

    instrs.flatMap(
      (instr: Instr) => {
        val nom = instr.names(0)
        if (reInsertion.values.toSet.contains(nom)) {
          tobeMoved += (nom -> instr.detm1iseHead); //detm1iseR should remove only one tm1, instead of two if there is two. instructions that should be moved
          List()
        }
        else {
          var resu = List(instr)
          if (reInsertion.keys.toSet.contains(nom))   //we also need to count occurences.
            resu ::= tobeMoved(reInsertion(nom))
          resu.reverse
        }

      })
  }

  /**
   *
   * @param e expression to analyse for tm1s
   * @return sub expression of $e$ starting with tm1s
   */
  private def tm1s(e: AST[_]) = {
    val d = new Dag[AST[_]](List(e))
    d.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1)
  }

  /**
   *
   * @param instrs instructions to analyse
   * @return (x,y) where there exist an instruction with a single tm1 of the form x= exp .... tm1(y)
   *  mais il est pas forcément qui démarrent l'expression.
   */
  private def instrsWithaTm1Reg(instrs: List[Instr]) = {
    var result: HashMap[String, String] = HashMap()
    for (instr <- instrs) {
      val theTm1s: List[AST[_]] = tm1s(instr.exps(0))
      if (theTm1s.size <= 1)
        for (e <- theTm1s.reverse)
          e.inputNeighbors(0) match {
            case r@Read(_) => //we returns tm1s of read, because they can be delayed.
              // if (result.contains(instr.names(0)))     throw new Exception("there is two possible tm1(Rx) for this R1")
              result += (instr.names(0) -> r.which) //if x= ...tm1(y) on renvoie x -> y
            case _ =>
          }
    }
    result
  }

  /**
   * @return tm1 of a single register R1<-exp ...tm1(R2),
   *         //rule A    if R2 is not affected before the instruction
   *         if R2 is a paramD, it has to be delayed, using an integer in Load
   *         if R2 is affected after==> the tm1 is simply supressed.
   *         unless R1 is a result parameters
   *         // rule A' if R2 is a param D, and R1 is a just a tm we move the instruction to the end
   *         // rule B   if R1 is not affected before the instruction
   *         //      and R2 is not affected after the instruction, until last R1's use ==>
   *         move the instruction after last R1's use
   * @param candReg instruction which contains a tm1(var) somewhere
   * @param instrs
   */
  private def ruleAandB(candReg: Map[String, String], instrs: List[Instr]): (Predef.Set[String], HashMap[String, String]) = {
    var candA = candReg.keys.toSet //candidR1.keys.toSet //candidate for simplest rule
    //data parameters need to be delayed.
    candA = candA.filter(r => !tSymbVarSafe(candReg(r)).k.isParamD)
    var candB = candA //candidate for the second a bit more complex rule
    /** lastUse(x)=instruction where x was used last if x is in cand2, x=exp should be inserted after lastuse(x) */
    var lastUse: HashMap[String, String] = HashMap()
    /** register which should be redefined */
    var beforeDef: HashSet[String] = HashSet()
    var live: HashSet[String] = HashSet()
    val candBCoalesc = candB.map(coalesc2(_))
    for (instr <- instrs) {
      val nom = instr.names(0)
      if (beforeDef.contains(nom))
        candB -= nom //R1 is re-defined before
      for (r1 <- beforeDef.intersect(candA))
        if (coalesc2(nom) == coalesc2(candReg(r1))) //r2 is redefined before definition of r1         }
          candA -= r1
      val newUsed = instr.usedVars().map(coalesc2(_))
      for (nowUsed <- newUsed.diff(live))
        if (!lastUse.contains(nowUsed))
          lastUse += (nowUsed -> nom)
      live = live.union(candBCoalesc.intersect(newUsed)) //live is a set of coalesced
      for (r1 <- candB)
        if (
          live.contains(coalesc2(r1)) && //R1 will be used
            coalesc2(nom) == coalesc2(candReg(r1))) //after R2 is redefined (now)
          candB -= r1

      if (candA.contains(nom)) { //we just pass the definition candA is still equal to its original value
        live -= coalesc2(nom)
        beforeDef += nom
      }
    }
    candB = candB.diff(candA) //candidates veryfying A and B are hanled as A

    def pred(s: (String, String)) = candB.contains(s._1) //we need a map for candB to know where to move.

    val reInsertionB = lastUse.filter(pred).map(_ swap) //allows to reuse move, unfortunately, there can be several such lastUse, so we need reverse order? or count number of occurence of the instruction.
    (candA, reInsertionB)
  }
  def isParamR(str: String) = tSymbVarSafe(str).k.isParamR
  /** tm1 operator are normaly supressed by adding registers, nevertheless,
   * different rules can be applied to avoid the cost of adding register:
   * juste removing the tm1 (rule A)
   * moving the instruction forward (rule B) or backward.(rule C)
   * adding a store instruction (rule D)
   * after detmify, all affects are replaced by stores. */
  def detm1Ify(): DataProg[InfoNbit[_]] = {


    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    if (isLeafCaLoop) {
     // if(p.dagis.visitedL.size==20)  println("ici")

      val candReg: Map[String, String] = instrsWithaTm1Reg(p.dagis.visitedL)
      val (candA: Predef.Set[String], reInsertionB: Map[String, String]) = ruleAandB(candReg, p.dagis.visitedL)
//signification du couple reInsertion b: (var1, var2) faut déplacer l'affectationn var1 aprés var2?
      if (candA.nonEmpty) {
        System.out.println("attention, flat detmisation of " + candA)
        //we now  remove tm1s, from candA
        p.dagis.visitedL = p.dagis.visitedL.map(
          (instr: Instr) => if (candA.contains(instr.names(0)))
            instr.detm1iseR else instr
        )
      }

      //we now  remove tm1s, and move instructions from candB
      p.dagis.visitedL = detmANDmove(reInsertionB, p.dagis.visitedL.reverse).reverse


      val reInsertionC: Map[String, String] = movesOfRuleC(p.dagis.visitedL)
      p.dagis.visitedL = detmANDmove(reInsertionC, p.dagis.visitedL)

      //Rule D;  replace affect (paramR,tm1(exp) by store(paramR,-1,exp) ==> if we do that we run the risk of writing the current value before reading it
      p.dagis.visitedL = p.dagis.visitedL.map((instr: Instr) => {
        val n = instr.names(0)
        if (isParamR(n) && instr.exps(0).asInstanceOf[ASTBg].isTm1) {
          val formerRadius =
          // assert(p.tSymbVar(n).k==ParamRR(1)) //if we store a tm1, it must have a radius one => no that was not true
            p.tSymbVar.addOne(n -> p.tSymbVar(n).decrementRadius())
          new Affect(n, instr.exps(0).asInstanceOf[ASTBg].detm1ise)
        }
        else instr
      })
      // instr.asInstanceOf[Affect[_]].toStoreDetmise()



      //for the tm1 that could not be easily supressed using optimizing tricks, we now proceed to standard detmify through creation of new registers tmun=tminus1which means new affectation.
      val toBeRepl: List[AST[_]] = p.dagis.dagAst.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1) //we could filter out more stuff because it consumes register
      // and registers are a precious ressourcefor(e<-toBeRepl)

      for (e <- toBeRepl) { //we look if there is  tm1 in tm1, it is an added difficulty
        val d = (new Dag[AST[_]](List(e.inputNeighbors(0)))) //builds the dag of tm1's expr in order to see if itself contains other tm1
        if (d.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1).nonEmpty) {
          //assert(false, "plusieurs tm1 emboités dans une meme expr, mefiance, vérifier si ca marche")
        }
      }
      dagis.affectizeTm1(toBeRepl.asInstanceOf[List[ASTBt[_]]])
      //we check that all the tm1s have been removed
      dagis.resetDag
      val tm1sLeft: List[AST[_]] = p.dagis.dagAst.visitedL.filter(_.asInstanceOf[ASTBt[_]].isTm1)
      if (!tm1sLeft.isEmpty) {
        for (t <- tm1sLeft) (System.out.println("\n" + t.toStringTree))
        assert(tm1sLeft.isEmpty, "there are still some Tm1s left. " + tm1sLeft.mkString("\n"))
      }
      val macroFields = dagis.newAffect.map(_.exp)
      // p.updateTsymb( macroFields, MacroField()) // when a variable is used twice it should be evaluated in a macro

      //   val g = new CodeGen(tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc)
      updateTsymbNbit(macroFields.reverse, MacroField()) //the order with wich we scan the created macrofield is important because
      //when there are several tm1, their definition depends on each other
      val u = 1

    }
    new DataProg(dagis, funs.map { case (k, v) ⇒ k -> v.detm1Ify() }, p.tSymbVar, paramD, paramR, coalesc)
  }


  /**
   * @return the program is still scalar affectation, but there is no call to boolean functions, only boolean operators,
   *         such as Scan or Map, and they are organized as a sequence of doubly nested loops with direction left or right
   *         right is used to compute <, because we consider msb first
   *         left is used when doing addition which considers lsb first.
   */
  def loopIfy(): DataProgLoop[InfoNbit[_]] = {
    val p = this.asInstanceOf[DataProg[InfoNbit[_]]]
    var constants: TabSymb[Boolean] = new mutable.HashMap() //stores the constant variables, and their values
    var instrNumber = 0

    /**
     *
     * @param instr instruction to be compiled
     * @return set of packet of scalar instructions corresponding to the compiled code,
     *         each packet can be executed in a single loop
     */
    def loopIfyInstr(instr: Instr): InstrLoop = {
      val exp = instr.exps(0).asInstanceOf[ASTBg] //ici c'est un store
      val decall = exp.deCallify(HashMap.empty[String, ASTBt[B]])
      // println("\n"+decall.toStringTree)
      val af = Affect(instr.names(0), decall) //reconstruit l'affectation sans le store
      val trueDag = new DagInstr(List(af)) //reconstruit le Dag depuis le generateur
      trueDag.dagAst.addGreaterOf(List(decall)) //add all subtree of map, scan to dags
      val iT0: collection.Set[AST[_]] = trueDag.inputTwice
      val iT1 = iT0.filter(isNotRead)
      val iT: collection.Set[AST[_]] = iT1.filter(ASTB.isNotMap1Read(iT1)) //we could filter out more stuff because it consumes register and registers are a precious ressource
      val outputStoredSet = trueDag.dagAst.visitedL.filter(outputStored).toSet //affectify operators which need to store their outputs
      val chDir: Set[ASTBg] = decall.SetDirAndReturnChangedDir()
      val toBeReplaced: Set[AST[_]] = iT.union(outputStoredSet).union(chDir.asInstanceOf[Set[AST[_]]])
      //val toBeRepl: List[AST[_]] = trueDag.dagAst.visitedL.filter(a => toBeReplaced(a) && isNotRead(a));
      // toBeRepl.map(_.setNameIfNull3());
      val treeDag: DagInstr = trueDag.affectIfy(toBeReplaced, "_ta")
      //it is possible that some of the subtrees have "Both()" as direction
      //we use the prefix "ta" to distinguish the temp scalar register
      //we now update the symbol table with bit size.
      val macroFields = trueDag.newAffect.reverse.map(_.exp) //there is now no layerFields,
      updateTsymbNbit(macroFields, MacroField())     //I added reverse, because in order to be able to compute the bit size, we need to take them in the right order
                                                            //modifies the symbol table so as to include the new registers, plus bit size
      //println(dagis)

      /** cheks that all integer have compatible scanning directions */
      def compatibleDir(d1: Option[Dir], d2: Option[Dir]): Boolean = {
        if (d1 != d2 && d1 != Some(Both()) && d2 != Some(Both()) //if one dir is Both, it could be either Left or Right so no pb
        ) return false
        true
      }

      /** OutputStored register used to compute a given register */
      val usedby: Map[String, Set[String]] = treeDag.usedBy((i: Instr) => i.exps(0).isInstanceOf[OutputStored])
      /** OutputStored register which are using a given register */
      val isusing = treeDag.isUsing((i: Instr) => i.exps(0).isInstanceOf[OutputStored])

      /** predicate defining connected component forming independant packets executable as loops
       *
       * @param src    instruction creating a field $f
       * @param target instruction using that field
       * @return true if src and target should be in the same packet, we d' need to check a coherent direction.
       *         we also check that there is no outputStored between src and target,
       *         if there is one, it should belong to target and not to src, so src and target could not be in the same packet
       * */
      def pipelineProximity2(src: Instr, target: Instr): Boolean = {
        // val test1=target.exps(0).isInstanceOf[OutputStored]
        // val test2=src.exps(0).isInstanceOf[OutputStored]
        (!target.exps(0).isInstanceOf[OutputStored]) &&
          compatibleDir(ASTB.instrDirection(src), ASTB.instrDirection(target)) &&
          (src.exps(0).isInstanceOf[OutputStored] || //if src is itself an outputStored, then it's ok to evaluate it in the same group
            usedby(src.names(0)).intersect(isusing(target.names(0))).isEmpty)
      }

      val wrap = immutable.HashMap.empty[Instr, treeDag.Wrap] ++ treeDag.visitedL.map(x => x -> treeDag.Wrap(x))
      val (loops1: Map[Instr, List[Instr]],_) = treeDag.indexedComponents(pipelineProximity2, true, wrap)
      //todo construire un dag produit un topological sort gratuitement, comme on a fait pour le Dag de zone, ca serai plus élegant.
      val loops2: Seq[List[Instr]] = treeDag.topologicSort2(loops1, wrap).reverse //we sort them so as to process them in the right order
      var result: List[Packet] = List()
      for (packet: List[Instr] <- loops2) { //todo when coalescing,  care should be taken that temporary variables used in the computation of one loop can reused in the next loop
        result = Packet(packet, tSymbVar.asInstanceOf[TabSymb[InfoNbit[_]]], coalesc, constants) :: result //we re-establish natural processing topological order
      }
      new InstrLoop(instr, result.reverse, {
        instrNumber += 1;
        instrNumber
      }) //we also recover natural processing order
    }

    if (isLeafCaLoop) {
      val loops: List[InstrLoop] = dagis.visitedL.reverse.map(loopIfyInstr(_))
      val instrs = loops.flatMap(_.loops.flatMap(_.instrs.reverse)) //instrs of a packet are also considered in reverse, since
      //everything is in reversed order
      val d = DagInstr(instrs)
      new DataProgLoop[InfoNbit[_]](d, p.funs.map { case (k, v) ⇒ k -> v.loopIfy() }, p.tSymbVar, paramD,
        paramR, coalesc, loops)
    }

    else new DataProgLoop[InfoNbit[_]](dagis, p.funs.map { case (k, v) ⇒ k -> v.loopIfy() }, p.tSymbVar,
      paramD, paramR, coalesc, null)
  }
}
