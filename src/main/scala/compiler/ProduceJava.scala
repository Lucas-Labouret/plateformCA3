package compiler

import compiler.AST.Read
import compiler.ASTB.{False, True, nbitExpAndParam}
import compiler.Circuit.{TabSymb, compiledCA, iTabSymb, labelsOfFields, naameCA, pkgCA, theStatified}
import compiler.DataProg.{allLayerFromCompiledMacro, nameDirCompilLoops}
import compiler.Instr.deployInt2
import compiler.Locus.{all2DLocus, allLocus}
import compiler.ProduceJava.totalGateCount
import dataStruc.Util.{CustomClassLoader, append2File, compileJavaFiles, componentNumber, copyArray, hasBeenReprogrammed, hierarchyDisplayedField, loadClassAndInstantiate, myGetDeclaredMethod, parenthesizedExp, pop, prefixDash, prefixDot, radicalOfVar, radicalOfVar2, radicalOfVarIntComp, radicalOfVarRefined, removeAfterChar, rootOfVar, sameRoot, shortenedSig, suffixDot, writeFile}
import compiler.VarKind.LayerField
import dataStruc.{Named, Util}
import dataStruc.Named.{isLayer, noDollarNorHashtag, noHashtag}
import simulator.CAloops2
import simulator.SimulatorUtil
import simulator.XMLutilities.readXML

import java.io.File
import java.lang.reflect.Method
import java.util.regex.Pattern
import scala.::
import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.convert.ImplicitConversions.`collection asJava`
import scala.collection.{Map, mutable}
import scala.collection.immutable.{HashMap, HashSet}
import scala.jdk.CollectionConverters._
import scala.util.Random
import scala.xml.{Elem, Node, NodeSeq, XML}

object ProduceJava {
  /** will contain the gate count, once the calls have been compiled */
  var totalGateCount = 0
}

/** provide method in order to  produce the final java code */
trait ProduceJava[U <: InfoNbit[_]] {
  self: DataProgLoop[U] =>
  /** stores and compiles the java of the macros, stores and compile the CA code, returns  the CA java program, */
  def produceStoreAndCompileAllJavaFile: CAloops2 = { //we need to generate spatial signature for macros before we can adress the main.
    val leafLoops = subDataProgs.filter(p => p._2.isLeafCaLoop) //si pas recompilé yaura pas tout!
    val codeLoops: iTabSymb[String] = leafLoops.map({ case (k, v) => (k -> v.asInstanceOf[ProduceJava[U]].javaCodeCAloop(k)) }) //retrieves all the recompiled CA loops
    val (codeLoopsMacro, codeLoopsAnonymous) = codeLoops.partition({ case (k, v) => !k.startsWith("_fun") }) //anonymous functions start with _fun

    val grouped: Predef.Map[String, Map[String, String]] = codeLoopsMacro.groupBy({ case (k, v) => k.substring(0, k.indexOf(".")) }) //  what comes before the dot is the name of the class where to regroup macros
    /** contains the loops but also many other parameters */
    var codeAllLoops = ""
    val customLoader = new CustomClassLoader("target/scala-2.13/classes/") //we have to use the custom loader, because class are compiled at run tim!e
    for (macroLoopName <- grouped.keys) { //for loops, the code is distributed in several file, for clarity. We handle each one, one by one
      val macroLoopPath = nameDirCompilLoops + macroLoopName + ".java"
      /** computes which macro are already defined */
      val alredyDef: Set[String] =
        if (!new File(macroLoopPath).exists()) //if macro file does not exists, creates it, and initiale its content with a preamble
        {
          val preambule = //this is a brand-new set of macros
            "package compiledMacro;\n"+
            "import simulator.PrShift;\n"+
            "\n"+
            "public class "
          writeFile(macroLoopPath, preambule + macroLoopName + " {\n}") //new compiled java macro will be inserted just before last accolades.
          new HashSet[String]() //there is no macro yet defined, since the class is non-existing (brand new)
        }
        else
          myGetDeclaredMethod("compiledMacro." + macroLoopName).toSet //class names contains a dot instead of an antislash
      val notYetDefined: Map[String, String] = grouped(macroLoopName).filter(x => !alredyDef.contains(suffixDot(x._1))) //we keep only names which are not already defined
      if (notYetDefined.nonEmpty) { // generates the code of the loops correcponding to the current java file of macrox
        val codeLoops = (notYetDefined.values.mkString("\n")).replace('#', '$'); //'#' is not a valid char for id in java
        codeAllLoops = codeLoops + codeAllLoops //codeAllLoops is gathered, just for printing/debugging purpose
        append2File(macroLoopPath, codeLoops) //we add the code of the macro which was not yet defined.
        val compilationSuccess = compileJavaFiles(List(macroLoopPath)) //we compile the macro before the main, so that the main can use it.
        assert(compilationSuccess, " compilation macro: " + macroLoopPath + " planté, poil au nez")
        System.out.println(" compilation macro: " + macroLoopPath + " reussie")
        val loadedClassC = customLoader.findClass("compiledMacro." + macroLoopName) //reload ensures that the compiler of main can access the new macros
      }
    }
    val codeMain: String = javaCodeMain(codeLoopsAnonymous.values.mkString("\n")).replace('#', '$'); //'#' is not a valid char for id in java file
    val nameCA = naameCA.capitalize + "CA" // radicalOfVar(paramR(0)) + "CA" //name of the produced java file is equal to the name of the layer wrapping around all the compiled prog
    //val pkgCAcompiled=pkgCA.replace("progOf","compiled")
    val nameCAjava = nameCA + ".java"
    val targetJavaFileName="src/main/java/"+pkgCA+"/"+nameCAjava
    //writeFile(nameDirCompilCA + nameCAjava, codeMain + "\n") //stores the code of the main (with anonmymous loop)
    writeFile(targetJavaFileName, codeMain + "\n") //stores the code of the main (with anonmymous loop)
    val sourceFiles = List(targetJavaFileName)
    //val sourceFiles = List(nameDirCompilCA + nameCAjava)
    val compilationSuccess = compileJavaFiles(sourceFiles)
    assert(compilationSuccess, "compilation of main CA:" + targetJavaFileName + " a planté, poil au nez")
    System.out.println("compilation of main CA:" + targetJavaFileName + " a réussi")
    val toto="compiledCA." + nameCA.capitalize
    val tata = pkgCA+"." + nameCA.capitalize
    //val classCA: Class[_] = customLoader.findClass("compiledCA." + nameCA.capitalize) //we reload the just compiled class, so that it points to the recompiled macro
    val classCA: Class[_] = customLoader.findClass(tata) //we reload the just compiled class, so that it points to the recompiled macro
    val progCA = loadClassAndInstantiate(tata, customLoader)

    //val classCA: Class[_] = customLoader.findClass(pkgCA+"." + nameCA.capitalize) //we reload the just compiled class, so that it points to the recompiled macro
    //val progCA = loadClassAndInstantiate(pkgCA+"." + nameCA.capitalize, customLoader)

    progCA.asInstanceOf[CAloops2]
  }

  /**
   * @param nameMacro name of a macro CAloop,
   * @return java code of this loop, and also number of gates to be consulted using reflection
   */
  def javaCodeCAloop(nameMacro: String): String = {
    val shortSigIn = shortenedSig(paramD);
    val shortSigOut = shortenedSig(paramR)
    val localSpatialLayers = tSymbVar.filter(x => x._2.k.isLayerField && noDollarNorHashtag(x._1))
    val layerNames = localSpatialLayers.keys.toSeq.sorted.toList
    val templateURL = if (nameMacro.startsWith("_fun"))
      "src/main/java/compiledCA/template/templateCAloop2.txt"
    else
      "src/main/java/compiledCA/template/templateCAloop.txt" //for macroLoop, we need to store the gatecount
    val gateCount =
      // if(nameMacro.startsWith("_fun"))
      gateCountMacroLoop
    //  else   dataStruc.Util.readStaticField("compiledMacro."+radical( nameMacro ) , methodName(nameMacro)+"GateCount")//we need to read a static  "slopDelta_3_1_2_1_1GateCount"  in class "compiledMacro.grad"

    //we proceed by filling slot in a template named templateCAloop.txt, each slot is filled using a specific method
    replaceAll(templateURL, Map(
      "GATECOUNT" -> {
        gateCount.toString
      },
      "NAMEMACRO" -> {
        def removeBeforeDot(s: String): String =
          if (s.contains('.')) //this is indeed not an anonymous macro
            s.drop(s.indexOf(".") + 1)
          else s

        removeBeforeDot(nameMacro)
      },
      "PARAMETERS" -> {
        /**
         * add type to parameters, either int[] or int[][],
         * one dimension is enough for spatial type boolV, two dimensions are needed for other locus
         * parameters are also passed as 1D array if they are Uint of one bit, and V(). this should not
         */
        def javaIntArray(s: String) = (if (needOnlyoneBit(s)) "int[] " else "int[][] ") + s

        val parameters = (shortSigIn ::: (shortSigOut ::: layerNames)).map(javaIntArray)
        parameters.mkString(", ")
      },
      "ANCHORPARAM" -> {
        /**
         * @param shortened name of spatial parameters
         * @param original   names of scalar parameters, in same order
         * @return Produce the code to inintialize 1D array from 2D arrays
         */
        def anchorParam(shortened: List[String], original: List[String]): List[String] = {
          var res: List[String] = List()
          var i = 0
          for (s: String <- shortened) {
            if (isBoolV(s)||isBool(s))
              i += 1 //no need to anchor, parameter is already a 1D arrau
            else {
              var j = 0; //j iterates on the indexes of the different scalar componendt
              try while (radicalOfVar(original(i)) == s) { //we scan through the parameter having same radical
                val crochets = if (needOnlyoneBit(s)) "" else "[" + j + "]"
                res = original(i) + " = " + s + crochets :: res;
                j += 1;
                i += 1 //affect each scala component
              } catch {
                case _: IndexOutOfBoundsException =>
              }
            }
          }
          res
        }

        //we anchor data parameters, result parameters, and constant def layers.
        val anchor = (anchorParam(shortSigIn, paramD) :::
                      anchorParam(shortSigOut, paramR) :::
                      anchorParam(layerNames, layerNames.flatMap(s => tSymbVar(s).locus.deploy(s)))
                     ).reverse.mkString(",\n              ")
        if (anchor.nonEmpty) "        int[] " + anchor + ";\n" else "" //we may not need to anchor anything.
      },
      "PROPAGATEFIRSTBIT" -> {
        val callsToPropagate: Seq[String] = paramD.map((s: String) =>
          "        p.prepareBit(" + s + ")"
        ) //for the moment we do the propagation on all data parameters
        val radius1Out = shortSigOut.filter(tSymbVarSafe(_).k.isRadius1)
        val paramR = shortSigOut.filter(tSymbVarSafe(_).k.isParamR)
        val paramRbooV = paramR.filter(tSymbVarSafe(_).locus==Locus.locusV)
        val callsToPropagate2 = radius1Out.map((s: String) => {
          val l = tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1
          "        p.prepareBit(" + s + ",compiler.Locus." + l.javaName + ")"
        })
        val callsToMirror = paramRbooV.map((s: String) => {
          val l = tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1
          "        p.mirror(" + s  + ")"
        })
        val callsToPrepareBit = paramR.map((s: String) => {
          val l = tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1
          "        p.prepareBit(" + s + ")"
        })

        (if (callsToMirror.nonEmpty    ) callsToMirror.mkString(";\n") + ";\n" else "") +
        (if (callsToPrepareBit.nonEmpty) callsToPrepareBit.mkString(";\n") + ";" else "") //on rajoute systematique des preparebit sur les field produit
      },
      "CALINENUMBER" -> (paramD ::: paramR)(0), //There must be at least one param,we need to read it so as to know the length which is the number of CA lines.
      "DECLINITPARAM" -> {
        /** declares all the variables local to the loops, and initializes them to zero if needed */
        def declInitParam = {
          /** variable which are delayed must be indentified so as to be initialized */
          def isDelayed(s: String): Boolean = {
            val res = delayed.contains(removeAfterChar(s, '#'))
            //System.out.println(delayed)
            res
          }

          val testCoalesc = coalesced
          val intReg = (standaloneRegister ++ coalesced.keys).filter(noHashtag) //should be declared todo gestion plus precise des dieses
          // val intReg = (standaloneRegister ++ coalesced.keys).filter(noDollarNorHashtag(_)) //should be declared todo gestion plus precise des dieses
          val boolReg: Iterable[String] = intReg.flatMap((s: String) => deployInt2(s, tSymbVarSafe(s))) //intReg which have a single component are not deployed

          boolReg.toList.sorted.map((s: String) => if (isDelayed(s) || true) s + " = 0" else s).mkString(",\n            ") //todo preciser keski est delayed
        }

        val dip = declInitParam;
        if (dip.size > 0)
          "        //initialisation \n" +
          "        int " + dip + ";" else ""
      },
      "LOOPBODY" -> {
        /* val t = totalCode
         val removeFalse = t.filter(e=> e != False()&&e != True()) */
        //certaine expression se simplifie sur false ou true

        // totalCode.map(_.toStringTreeInfix(tSymbVar.asInstanceOf[TabSymb[InfoType[_]]])).grouped(4).map(_.mkString(";")).mkString(";\n ")
        "            " +
        totalCodeCoalesced.map(_.toStringTreeInfix(this.asInstanceOf[DataProg[InfoType[_]]]))
                          .grouped(4)
                          .map(_.mkString(";\n            "))
                          .mkString(";\n            ")
      }
    ))
  }

  /**
   *
   * @param codeLoopAnonymous code of the anonymous macros
   * @return code of the main regrouped together with the code of the anonymous macro, to make them accessible from the CA's long list of calls
   *
   */
  def javaCodeMain(codeLoopAnonymous: String): String = {
    /**
     *
     * @param tSymbVarAndConstLayer tSymbVar plus names of constant Layers defined in subProgram (should be declared in the main)
     * @return list of offset for all named fields. Used for 1-to anchor named 1D arrays, 2-to list memory planes
     * */
    def offsetsInt(tSymbVarAndConstLayer: iTabSymb[InfoNbit[_]]): Map[String, List[Int]] = {
     val result= tSymbVarAndConstLayer.map { case (k, v) => (k,
        //   if (v.t == (V(), B()) /*|| v.t == B()*/)   List(adress(coalesc(k))) else
        if ( v.t == B()) {
          //print("totot")
          val tata=coalesc(k)
          List(adress(k))
          //val toto: String =coalesc(k);   List(adress(toto))
        }
        else
        {
          //pour les constante booleenne, leur type est directement B
          val offsetstring = v.locus.deploy2(k, tSymbVarSafe(k))
          for (of <- offsetstring)
            if (!coalesc.contains(of))
              throw new Exception("trouve pas " + of + " dans coalesc")
          offsetstring.map((s: String) => adress(coalesc(s))).toList
        })
      }
      result
    }

    val spatialOfffsetsInt = offsetsInt((tSymbVar ++ layerSubProgStrict).filter(x => noDollarNorHashtag(x._1)))
    // val spatialOfffsetsIntMain = offsetsInt((tSymbVar ++ layersMain).filter(x => noDollarNorHashtag(x._1)))
    val (theCallCode: Seq[String], decompositionLocus, theDisplayed) = javaOfTheCallInTheMain()

    def initLayer(spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, String] = {
      HashMap[String, String]() ++ spatialLayer.map({ case (s, i) => (s -> i.k.asInstanceOf[LayerField].init) })
    }
    /** apparemment j'ai besoin d'un anchor different pour les names */
    def anchorOneVarNamed(oneVar: (String, List[Int])) = {
      val ints = oneVar._2
      var res = ints.map("m[" + _ + "]").mkString(",")
      if (!isBoolV(oneVar._1) && !isBool(oneVar._1) && (oneVar._2.size > 1))
        res = " new int[][]{" + res + "}" //we have a 2D array
      res = oneVar._1 + "=" + res;
      res
    }

    def anchorOneVar(oneVar: (String, List[Int])) = {
      val ints = oneVar._2
      var res = ints.map("m[" + _ + "]").mkString(",")
      if (!isBoolV(oneVar._1) && !isBool(oneVar._1) )//&& (oneVar._2.size > 1))
        res = " new int[][]{" + res + "}" //we have a 2D array
      res = oneVar._1 + "=" + res;
      res
    }

    // def javaIntArray(s: String) = (if (isBoolV(s)) ("int [] ") else ("int [][] ")) + s
    def anchorNamed(offset: Map[String, List[Int]]): String = {
      val problems=offset.filter(x => !isBool(x._1) && !isBoolV(x._1)  && x._2.size == 1)
      val (offset1D, offset2D) = offset.partition(x => isBoolV(x._1) || isBool(x._1) || x._2.size == 1)

      (if (offset1D.nonEmpty) "        int[] " + offset1D.map(anchorOneVarNamed(_)).mkString(",\n              ") + ";\n" else "") +
      (if (offset2D.nonEmpty) "        int[][] " + offset2D.map(anchorOneVarNamed(_)).mkString(",\n                ") + ";\n" else "")
    }

    //we use the same template technique as the one used for CAloops
    val res=replaceAll("src/main/java/compiledCA/template/templateCA.txt", Map(
      "GATECOUNT" -> totalGateCount.toString, //totalOp.toString,
      "NAMEPACKAGE" -> pkgCA,
      "NAMECA" -> naameCA.capitalize, //radicalOfVar(paramR(0)).capitalize,
      "MEMWIDTH" -> ("" + mainHeapSize), //TODO on calcule pas bien la memwidth)
      "DECLNAMED" -> {
        /** code that declares all the named arrays 1D and 2D */
        def DeclNamed(offset: Map[String, List[Int]]): String = {
          val (var1D, var2D) = offset.keys.partition(offset(_).size == 1) //we distinguish 1D arrays from 2D arrays.
          (if (var1D.nonEmpty) "int[]" + var1D.mkString(",") + ";\n" else "") +
            (if (var2D.nonEmpty) "int[][]" + var2D.mkString(",") + ";\n" else "")
        }

        ("" + DeclNamed(spatialOfffsetsInt))
      },
      "DECLNOTNAMED" -> {
        /** Codes that declares unamed arrays */
        def declNotNamed(decomposition: Map[Locus, Map[List[Int], Int]]): String = { //todo queskispass si c'est un tableau 1D?
          val var1D = (0 until decomposition(V()).size).map("V" + _) //name of unamed points to its locus.
          var var2D: List[String] = List() //needs 2D arrays
          for (l: Locus <- all2DLocus) {
            var2D = var2D ++ (0 until decomposition(l).size).map(l.shortName + _)
          }
          (if (var1D.nonEmpty) "int[] " + var1D.mkString(",") + ";\n" else "") +
            (if (var2D.nonEmpty) "int[][] " + var2D.mkString(",") + ";\n" else "")
        }

        ("" + declNotNamed(decompositionLocus))
      },
      "LISTCALL" -> {
        "        " + theCallCode.reverse.mkString("\n        ")
      },
      "ANCHORNAMED" -> {
        /** code that anchors named arrays on memory */
        anchorNamed(spatialOfffsetsInt)
      },
      "ANCHORNOTNAMED" -> {
        /** Codes that decompose array 2D into memory slices */
        def anchorNotNamed(decomposition: Map[Locus, Map[List[Int], Int]]): String = { //todo queskispass si c'est un tableau 1D?
          var codeDecl: List[String] = List()
          for (l: Locus <- allLocus) if (decomposition(l).nonEmpty) {
            val (offset1D, offset2D) = decomposition(l).partition(x => x._1.size == 1) //separates  BoolV which are stored on one plane
            if (offset1D.nonEmpty) codeDecl ::= "int[]" + offset1D.map(x => anchorOneVar((l.shortName + x._2, x._1))).mkString(",") + ";\n"
            if (offset2D.nonEmpty) codeDecl ::= "int[][]" + offset2D.map(x => anchorOneVar((l.shortName + x._2, x._1))).mkString(",") + ";\n"
          }
          // seedE = new int[][]{m[8], m[9], m[10]};
          if (codeDecl.nonEmpty) codeDecl.mkString("\n") else ""
        }

        anchorNotNamed(decompositionLocus)
      },
      /*  "COPYLAYER" -> { //iL contains only the variable totoll not toto
          val iL = initLayer(layerSubProg2).keys.filter(isLayer(_)).filter(x => !x.startsWith("lldef") && tSymbVar.contains(x.drop(2))) //we check that the layer without ll exists
          //anchoring both lltoto and toto in memory.
          //todo faut virer def
          val llandNotll = spatialOfffsetsInt.filter(x => iL.contains(x._1) || iL.contains("ll" + x._1))
          "" + anchorNamed(llandNotll) +
            iL.toList.map(s => "copy(" + s + "," + s.drop(2) + ");").mkString("")
        },*/
      "FIELDOFFSET" -> {
        def fieldOffset(offset: Map[String, List[Int]]): String = {
          def offsetOneVar(oneVar: (String, List[Int])) = {
            val ints = oneVar._2
            var res = ints.map("" + _).mkString(",")
            res = "map.put(\"" + oneVar._1 + "\", li(" + res + "));";
            res
          }
          "        " + offset.map(offsetOneVar).mkString("\n        ")
        }
        val spatialOfffsetsInt2 = spatialOfffsetsInt.filter(x => !x._1.startsWith("def"))
        fieldOffset(spatialOfffsetsInt2)
      },

      "FIELDSTAT"-> {
        def fieldStat(stats: Map[String, String]): String = {
        def processOneStat(oneVar: (String, String)):String = {
           "map.put(\"" + oneVar._1 +  "\""+ "," +  "\"" +  oneVar._2 + "\");"
        }
        "        " + stats.map(processOneStat).mkString("\n        ")
      }
        //val labelsOfFields2 = spatialOfffsetsInt.filter(x => !x._1.startsWith("def"))
        fieldStat(theStatified)
      },

      "FIELDLABEL" -> {
        def fieldLabel(labels: Map[String, List[String]]): String = {
          def labelsOneVar(oneVar: (String, List[String])) = {
            val labels = oneVar._2
            var res = labels.map("\"" + _ + "\"" ).mkString(",")
            res = "map.put(\"" + oneVar._1 + "\", ls(" + res + "));"
            res
          }
          "        " + labels.map(labelsOneVar(_)).mkString("\n        ")
        }
        //val labelsOfFields2 = spatialOfffsetsInt.filter(x => !x._1.startsWith("def"))
        fieldLabel(labelsOfFields)
      },

      "FIELDLOCUS" -> {
        /**
         *
         * @param names
         * @param spatialLayer
         * @return
         */
        def fieldLocus(names: Iterable[String], spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, Locus] = {
          val l: Map[String, Locus] = spatialLayer.map({ case (k, v) => k -> v.t.asInstanceOf[(Locus, Ring)]._1 })
          // .filter(x => !tSymbVar.contains(x._1)) //removes  layers defined in main
          val namesWithLocus=names.filter(tSymbVar(_).t.isInstanceOf[(Locus, Ring)])
          HashMap[String, Locus]() ++ namesWithLocus.map((s: String) => s -> tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1) ++ l
        }

        fieldLocus(spatialOfffsetsInt.keys, layerSubProgStrict).map((kv: (String, Locus)) => //we need to know the locus, as soon as  we need to know the bit planes
          "        map.put(\"" + kv._1 + "\"," + "compiler.Locus." + kv._2.javaName + ")").mkString(";\n") + ";"
      },
      "BITSIZE" -> {
        /** number of bits for non boolean variables. */
        def fieldBitSize(names: Iterable[String], spatialLayer: Map[String, InfoNbit[_]]): HashMap[String, Int] = {
          val l: Map[String, Int] = spatialLayer.filter(_._2.nb > 1).map({ case (k, v) => k -> v.nb })
            .filter(x => !tSymbVar.contains(x._1)) //removes integer layers defined in main
          HashMap[String, Int]() ++ names.filter(tSymbVar(_).nb > 1).map((s: String) => s -> tSymbVar(s).nb) ++ l
        }

        fieldBitSize(spatialOfffsetsInt.keys, layerSubProg2).map((kv: (String, Int)) =>
          "        map.put(\"" + kv._1 + "\"," + kv._2 + ")").mkString(";\n") + ";"
      },
      "DISPLAYABLE" -> //theDisplayed contains two kinds of name:aux and segmented, first step should separate the segmented
        {
          if (theDisplayed.isEmpty)
            throw (new Exception("you forgot to call show, no fields are displayed "))
          if (!sameRoot(theDisplayed)) {
            System.out.println(theDisplayed.filter(_.startsWith("aux")))
            throw (new Exception("some fields do not encode a path" + theDisplayed))
            //val ordered=orderDisplayed(theDisplayed)
          }
          val s = parenthesizedExp(rootOfVar(theDisplayed.head), hierarchyDisplayedField(theDisplayed));
          s + "."
        },
      "INITLAYER" -> {
        val iL = initLayer(layerSubProg2)
        iL.map((kv: (String, String)) =>
          "        map.put(\"" + kv._1 + "\",\"" + kv._2 + "\")").mkString(";\n") + ";\n" + ";"
      },
      "PREPAREBITS" -> {
        val layers: Map[String, U] = layerSubProg2

        val callsToPropagate2 = layers.keys.map((s: String) => "        p.prepareBit(" + s + ")")

        val callsToMirror = layers.keys.map((s: String) => {
          val l = tSymbVar(s).t.asInstanceOf[(Locus, Ring)]._1
          "        p.mirror(" + s + ",compiler.Locus." + l.javaName + ")"
        })
        "\n" //we assume that fields are already  stored in mirored and propagated form
       // callsToMirror.mkString(";") + ";\n" + callsToPropagate2.mkString(";") + ";\n"
      },
      "ANONYMOUSLOOP" -> codeLoopAnonymous
    ))
    res
  }

  /** the sequence of calls of macros realizing the desired CA computation,
   *
   * @return the calls, plus a map called "decompositionLocus", which for each locus, and each group of memory plane,
   *         associates a number identifying an array of bit planes, used in the program.
   *         plus the set of  Displayed fields, which are simply arguments of calls to show */
  def javaOfTheCallInTheMain(): (List[String], Map[Locus, Map[List[Int], Int]], Set[String]) = {
    var lastCallCode: String = null //used to avoid generating many copy or many memo
    /** names of displayed variables,  updated as a side effect when generating the call Codes, each time we meet a call to display */
    var theDisplayed: Set[String] = HashSet()
    var decompositionLocus: Map[Locus, Map[
      List[Int], Int]] = HashMap() ++ allLocus.map(_ -> HashMap()) //empty map for each locus
    val theCalls = dagis.visitedL.reverse.asInstanceOf[List[CallProc]] //compiled calls
    var theCallCode: List[String] = List()
    for (call <- theCalls) { //rewrite the calls, by regrouping parameters
      val paramsD: List[String] = call.exps.map(_.asInstanceOf[Read[_]].which) //names of parameters passed
      //on rajoute les layers si y en a
      val paramsR: List[String] = call.names;
      val params = paramsD ::: paramsR;

      var callCode: String = call.procName + "(" //we always put the called procedure name. we now need to add the params
      var i = 0 //counter of scalar parameter
      var paramCode: List[String] = List() //code of the param for the current considered call
      var gateCountOfCall = 0
      call.procName match {
        //we first consider specific system call show, copy, memo, debug
        case "set1" | "reset0" =>
          callCode= callCode + paramsR(0)  //gros bricolage
          val result=0
        case "show" =>
          val toto=(call.usedVarsIncludingLayers().toList)
          val callCodeArg = radicalOfVar(toto.head) //we take the radical for diminishing the number of parameters
          theDisplayed += callCodeArg //sideeffect, update theDisplayed. display has allways a single arg which is the field to be displayed
          callCode += callCodeArg //in fact we could supress calls to show. We still leave them, just so that we can check those in the compiled java.
        case "stat" =>
          val twoNames=call.usedVarsIncludingLayers().toList.map(radicalOfVar(_)).distinct //si y a trois bits, ca produit 4 element de base, s
          val List(isDef,values)=twoNames
           theStatified += (isDef -> values) //sideeffect, update theDisplayed. display has allways a single arg which is the field to be displayed
          callCode += twoNames.mkString(",") //in fact we could supress calls to show. We still leave them, just so that we can check those in the compiled java.

        case "copy" => assert(paramsD.size == 1 && paramsR.size == 1) //we copy bit by bit, hence int by int.
          val pR: String = radicalOfVar(paramsR(0))
          val pD: String = if (tSymbVarSafe(paramsR(0)).t == (V(), B()))
            radicalOfVarIntComp(paramsD(0))
          else radicalOfVar(paramsD(0))
          val locuspR = tSymbVarSafe(pR).locus
          //val copiedConst=tSymbVarSafe(pD).t==B() //verifier
          val copiedConst=tSymbVarSafe(paramsD(0)).t==B() //verifier
          val locuspD = if(copiedConst) V() else  tSymbVarSafe(paramsD(0)).locus //evite de consulter pd qui contient des crochet

              //here we have scalar used for constant, of type B, which we can assume to be Vertex
          //si on utilise Elt i, y aura un #i a la fin de paramD et pas de # a la fin de paramR
          val weHaveAnElt = paramsD(0).dropRight(1).endsWith("#") && !(paramsR(0).dropRight(1).endsWith("#"))
          val specifComponent: String = if (weHaveAnElt)
            "," + paramsD(0).last
          else " " //rajoute le numéro de la component, pour elt.
          if (locuspR.isTransfer && !locuspD.isTransfer) { //marche pas pour E,F
            //c'est le broadcast qui renvoie void je pense, utilisé par copy

            callCode = (if(copiedConst)  "broadcaast1("  else "broadcaast(" )+ 6 / locuspD.density + ","
          } //6 copy from 1D array to 1Darray are turned into a call to broaadcast from 1D arrau to 2D array
          //val l: mutable.LinkedHashSet[String] = mutable.LinkedHashSet(pR, pD)
         // callCode += pD  + "," + pR  // bizarrement j'ai eu plus besoin de spécifier la component, c'est déja fait
          callCode += pD + specifComponent + "," + pR // mais cela compilait n'importe quoi sur homogeneize, donc je l'ai remis.
        case "memo" => val l: mutable.LinkedHashSet[String] = mutable.LinkedHashSet() ++ params.map(radicalOfVar(_)) //copy and memo have the same effect
          callCode += l.toList.mkString(",")
        case "bug" => val nameBug = radicalOfVar(call.exps.head.asInstanceOf[Read[_]].which) //on apelle bug avec un read, c'est obligé
          val locusBug = tSymbVar(nameBug).locus.toString.dropRight(2) //on regard le locus de la variable surveillée. dropRight enleve les deux parenthéses
          paramCode = List(nameBug, "llbug" + locusBug, "\"" + nameBug + "\"", "bugs").reverse
        //faudrait enregistrer la liste des locus de bug?
        case _ => //we now consider the interesting case: a call to a real CAloop
          paramCode = List("p") //this is a method PrShift that does a preliminary shift if radius is >0yyy

          //we can reconstruct spatial types, and bit numbers directly from the effective parameters:
          // call names and expressions, no need for reflection, at the end!:
          val dataParam = call.exps.map((x) => x.asInstanceOf[Read[_]].which)
          val resultParam = call.names

          def concatCallCode:List[String]={
            radicalOfVar(resultParam(0))::dataParam.map(radicalOfVarIntComp)
          }
          if (call.procName.startsWith("compute.concat")) {

            //check that data anr result are all with #
             paramCode=concatCallCode ++ paramCode
            System.out.println("concat") //c'est standard
          }
          else{
          val spatialParam = shortenedSig(dataParam ::: resultParam)
          val bitSigSafe = spatialParam.map(tSymbVarSafe(_).nb)
           val anteSpatialSigSafe=spatialParam.map(tSymbVarSafe(_).t).filter(!_.isInstanceOf[(Locus, Ring)])
            if(anteSpatialSigSafe.nonEmpty)
              print("pb")  //a cause des constante, on a des type B() qui se trimballe, qu'on va remplacer par V(),B()
            val safeSpatialSigSafe=spatialParam.map(tSymbVarSafe(_).t).map(
              {case t:(Locus, Ring)=>t
                case B() => (V(),B()) //on escamote B()
              case _ => throw new Exception("c'est soit B soit un brave locus plus ring")
              })
          //val spatialSigSafe = spatialParam.map(tSymbVarSafe(_).t.asInstanceOf[(Locus, Ring)])
          /** for each radical, the number of effective parameter with identical radical. Carefull,if it is 6, it does not imply that we have a transfer, it could be a UnitE with 2 bits for example */
          val densityDirectlyMeasured: List[Int] = spatialParam.map(s => params.filter(radicalOfVar(_) == (radicalOfVar(s))).size) //on teste l'egalité pour eviter les pb avc les prefixes.
          assert(densityDirectlyMeasured.sum == params.size, "regardez si y a pas un nom de parametre qui est suffixe d'un autre" + params.size + "neq" + densityDirectlyMeasured.sum)

          for (((spatialType, nbit), densityDirect) <- safeSpatialSigSafe zip bitSigSafe zip densityDirectlyMeasured) { //retrieve spatial type and  bitSize   of parameters.
            val locusParamPossiblyWrong: Locus = spatialType._1 //locus is wrong because it is computed from the name of the effective parameter. It is not to be trusted, when broadcasting is done.
            var densityParamPossiblyWrong = nbit * locusParamPossiblyWrong.density //locus is wrong implies density is wrong too
            //pour elt, densityParamPossiblyWrong is wrong, because we pass only one of the numerous bits forming an uint, so we take intoaccount the density directly measured


            //we identify wether the current parameter is a component.
            val isComponent: Boolean = {
              nbit > 1 && //todo test removing this, because integer can have a single bit==>  test prog with one bit integer
                spatialType._2 != B() && //we take components of either UI or SI
                densityDirect * nbit == densityParamPossiblyWrong //density possibly wrong is density of parameter before taking a component.
            }


            if (isComponent) {
              val rad = radicalOfVar(params(i))
              Util.checkSingleComponentNumber(params.filter(radicalOfVar(_)==rad))
              val component = componentNumber(params(i))
              paramCode = "copy(" + rad + "," + component + "," + nbit + ")" :: paramCode
              i+=densityDirect
            }
            else
            { if (densityParamPossiblyWrong > densityDirect)
              densityParamPossiblyWrong = densityDirect  //je sais plus trop pourquoi
              if (spatialType == (V(), B()) && densityDirect < 6) { //we can have seedDist$2 passed to a boolV, therefore, we should transform it into seedDist[2]
                paramCode = radicalOfVarIntComp(params(i)) :: paramCode; //this is what is done by radicalOfVarIntComp
                i += 1
              }
              //until now we applied same processing wether it is a name or a heap variable
              else {
                /** we look at the type of effective parameter, in order to find the type of the formal parameter */
                val infoParamEF = tSymbVarSafe(radicalOfVar(params(i)))
                val locusParamEF = infoParamEF.locus //this does not work, because effective parameter has been obtained by duplication using a direct interpretation of broadcast
                val nbitParamEF = infoParamEF.nb //since we directly measure how much bits are sent in the effective parameters,
                // we have to take the number of bits into account.
                if (!locusParamPossiblyWrong.isTransfer && densityDirect / nbitParamEF == 6 /* !locusParamEf.isTransfer*/ ) //we detect that we have done a broacast,
                  if (spatialType == (V(), B())) {
                    paramCode = "broadcaaast(" + radicalOfVar(params(i)) + ")" :: paramCode; i += densityDirect
                  }
                  else {
                    paramCode = "broadcaast33(" +nbitParamEF+","+ 6 / locusParamPossiblyWrong.density + "," + radicalOfVar(params(i)) + ")" :: paramCode; i += densityDirect
                  }
                //we prooceed differently depending wether the params are mem (isheap) or name of fields
                else if (isHeap(params(i))) { //its a "mem[x]
                  var indexesMem: List[Int] = List()
                  for (j <- 0 until densityParamPossiblyWrong) { //iterate over the nbit scalar parameters of the form mem[2]
                    indexesMem = adress(params(i)) :: indexesMem; i += 1
                  } //builds the list of memory offset associated to the locus
                  indexesMem = indexesMem.reverse
                  if (!decompositionLocus(locusParamPossiblyWrong).contains(indexesMem)) { //check wether that array2D of memory slices has already been used
                    val newMapOfLocus = decompositionLocus(locusParamPossiblyWrong) + (indexesMem -> decompositionLocus(locusParamPossiblyWrong).size)
                    decompositionLocus = decompositionLocus + (locusParamPossiblyWrong -> newMapOfLocus)
                  }
                  paramCode = locusParamPossiblyWrong.shortName + (decompositionLocus(locusParamPossiblyWrong)(indexesMem)) :: paramCode //name of formal paramer is locus plus rank stored in decompositionLocus
                }
                else //its not  a mem
                {
                  paramCode = radicalOfVar(params(i)) :: paramCode;
                  i += densityParamPossiblyWrong
                }
              }
            }}}
          /** fundef if recompiled */
          val progCalled: DataProgLoop[U] = subDataProgs.getOrElse(call.procName, null) //gets the called dataProg, we won't be able to do that, when doing modular compilation.
          // CA loops can  contain layers.
          val allLayerSafe: List[String] = //we consider the two cases:1- prog is being recompiled, 2-prog has already been compiled
            if (progCalled != null) //prog is being recompiled, we can use it to get the layers from the symbolTable
              progCalled.allLayers.filter(noDollarNorHashtag(_))
            else // prog had already been compiled, we retrieve the layer using scala relection, layers are the last parameters to the macro loops.
              allLayerFromCompiledMacro(call.procName)
          if (allLayerSafe.nonEmpty) // CA loops can  contain layers.
            paramCode = allLayerSafe.toList ++ paramCode //this portion is not suppressed because access to localProg is still possible
          gateCountOfCall =
            if (progCalled != null)
              progCalled.gateCountMacroLoop // progCalled
            else dataStruc.Util.readStaticField("compiledMacro." + prefixDot(call.procName),
              suffixDot(call.procName) + "GateCount").asInstanceOf[Int] //we need to read a static  "slopDelta_3_1_2_1_1GateCount"  in class "compiledMacro.grad"
      }
      callCode += paramCode.reverse.mkString(",") + ");"
      //had the gateCount as a comment
      if (gateCountOfCall != 0) {
        callCode += "// " + gateCountOfCall + " gate"
        totalGateCount += gateCountOfCall
      }
      if (!callCode.equals(lastCallCode) && !call.locus.equals("show"))
        theCallCode = callCode :: theCallCode //in case of copy or memo of integer, several times the same call code will be generated
      lastCallCode = callCode //in which  case we keep only the first one by ignoring the following
    }
    (theCallCode, decompositionLocus, theDisplayed)
  }

  /** see latex, from the call, retrieve the layer used from the parameter names of the already compiled macro loop */


}
