package simulator

import compiler.{Locus, V}
import dataStruc.Named
import dataStruc.Util.lastSegment
import simulator.Controller.disableBinding
import simulator.ExampleData._
import simulator.Medium.christal
import simulator.Simulator.{nameGlobalInit, nameSimulParam}
import simulator.XMLutilities._
import simulator.colors.mainColors

import java.awt.Color
import java.awt.Color.cyan
import java.util
import javax.swing.{InputMap, JComponent, KeyStroke}
import scala.collection.JavaConverters._
import scala.collection.convert.ImplicitConversions.`map AsScala`
import scala.swing._
import scala.swing.event.{ButtonClicked, SelectionChanged, ValueChanged}
import scala.xml._

/**
 *
 * @param nameCA    name used to find out where param and progCA are
 * @param paramCA   mutable  because updated as we interact with display, and also stored
 * @param progCA    contains the code for the loops
 * @param chosenDir directory containing the CA code
 */
class Controller(val nameCA: String, var globalInit: Node, val globalInitName: String,
                 var simulParam: Node, val simulParamName:String, var displayParam: Node,
                 val progCA: CAloops2, val chosenDir: String, val mf: MainFrame)
  extends ToolBar() { //the controller inherits the toolBar, so that it can easily identifies which button was ckicqued, using the button's variable  name
  /** sometimes we try different random root, so as to explore different possible runs. */
  var randomRoot: Int = xInt(simulParam, "simul", "@randomRoot")
  var density: Int = xInt(simulParam, "simul", "@density")
  var paramStat: Int = xInt(simulParam, "simul", "@paramStat")
  var darkness:Int= xInt(simulParam, "simul", "@darkness")
  //var t:Int=xInt(simulParam, "simul", "@t0")
  /** we need to know the locus of fields which are either displayed or initialized */
  val locusOfDisplayedOrDirectInitField: Map[String, Locus] = progCA.fieldLocus.asScala.toMap
  /** we need to know the number of ints of fields which are either displayed or initialized */
  val bitSizeDisplayedOrDirectInitField: Map[String, Int] = progCA.fieldBitSize().asScala.mapValues(_.toInt).toMap
  /** the method used to initialize the direct init fields. */
  val initName: util.HashMap[String, String] = progCA.init() //fromXMLasHashMap(displayParam, "inits", "@init")
  /** labels used to show fields which need text, such as  constraint, moves, or instructions */
  val textOfFields: Map[String, List[String]] = progCA.textOfFields().asScala.toMap
  val partial: Map[String, String] = progCA.partial().asScala.toMap
  /**  fields displayed as text*/
  val displayedAsText: Set[String]=textOfFields.keySet

  /** memory offset of the bit planes  representing  field, the size of the list corresponds to the density of the field */
  val memFieldsOffset: Map[String, List[Integer]] = progCA.fieldOffset().asScala.toMap
  /** this is for the display, this is not the number of lines and columns. */
  val CAwidth: Int = xInt(simulParam, "display", "@CAwidth")

  val globalInitNames: Array[String] = fromXMLasList((globalInit \\ "inits").head).toArray
  val selectedGlobalInit: Int = xInt(globalInit, "selected", "@rank") //which is the starting value for global init
  val randomInitNames: Array[Int] = (0 to 9).toArray
  val densityInitNames: Array[Int] = (0 to 99).toArray
  val darknessInitNames: Array[Int] = (0 to 99 by  5).toArray
  val statInitNames: Array[String] = progCA.partial().map{case(k,v)=>lastSegment(k)+lastSegment(v)}.toArray
    //Circuit.theStatified

  /** check that global variables (layer and shown) do not share offset. */
  def invariantFieldOffset(): Unit = {
    val h: String = progCA.displayableLayerHierarchy()

    def isGlobal(nameVar: String): Boolean = Named.isLayer(nameVar) || h.contains(nameVar) //true if needs to be allways accessible

    val varOfMyCell: Array[String] = new Array(progCA.CAmemWidth)
    for ((s, l) <- memFieldsOffset) //we check no more than two variables allocated on a given offset
      for (offset <- l) {
        val v = varOfMyCell(offset)
        if (isGlobal(s))
          assert(v == null || (!isGlobal(v)), "two variables " + varOfMyCell(offset) + " " + s + " in cell " + offset)
        varOfMyCell(offset) = s
      }
    //for (i <- 0 until varOfMyCell.length)       assert(varOfMyCell(i) != null, "unusedMemoryCell " + i) there can in fact be holes in the heap
  }
  invariantFieldOffset()
  /** by default, if not supplied, number of lignes is 1/sqrt(2) number of columns */
  def CAheight: Int = {
    try {
      xInt(simulParam, "display", "@CAheight")
    }
    catch {
      case _: java.lang.NumberFormatException => (CAwidth / Math.sqrt(2)).toInt
    }
  }

  /** Jcomponent displaying the tree of layers which can expands by cliking on it */
  var layerTree: LayerTree = null //cannot be  directly set  upon creation of controller, because of double recursive definition
  /** a controller manages several environements */
  var envList: Vector[Env] = Vector() //cannot be  directly set  upon creation of controller,

  /** layerTree is suplied latter, because of mutual recursive link between controller and layerTree */
  def init(lt: LayerTree): Unit = {
    listenTo(lt) //we will need to repaint it upond expansion or coloring
    layerTree = lt
    layerTree.hideRoot
  }

  /** part of the xml param which cannot be (yet) changed during a simulation */
  private val fixed: NodeSeq = simulParam \\ "fixed"
  /** Colors of displayed layers */
  private var colorCode: Map[String, String] = fromXMLasHashMap(displayParam, "colorOfField", "@color")
  val shown: String = progCA.displayableLayerHierarchy()
  colorCode = colorCode.filter(t => shown.contains(t._1)) //
  //((s:(String,String)=>shown.contains(s._1))

  /** associate a color to each displayed field , fiedls names are the keys, colors are the values which need ot be decoded from hexadecimal */
  var colorDisplayedField: Map[String, Color] = colorCode.mapValues((s: String) => new Color(Integer.decode(s))).toMap
  /** We 'll have to generate the voronoi in space. We consider that V() is allways displayed */
  colorDisplayedField = colorDisplayedField.filter(x => locusOfDisplayedOrDirectInitField.contains(x._1)) //if a field is nolonger defined and used to be colored, it has to be removed from the displayed
  var displayedLocus: Set[Locus] =
    colorDisplayedField.keys.map(locusOfDisplayedOrDirectInitField(_)).toSet + V()
  var currentProximityLocus=   proximityLocus(displayedLocus)
  private def updateProximity=     currentProximityLocus=   proximityLocus(displayedLocus)
  /**
   *
   * @param loci     locus which are displayed
   * @return    graph of adjacency between $loci
   * removes adjacency which compromise planarity,
   * hypothesis is that those are only punctual adjacency
   * this will create plannar graph with face of degree 4, which thereafter should be correctly split.
   */

  private def proximityLocus(loci:Set[Locus]): Map[Locus, Set[Locus]] =  christal(6, 8, 200).proximityLocus(loci)

    /** we'll applies t0 iterations upon initialization to speed up going directly to the interesting cases */
 // val t0: Int = xInt(simulParam, "simul", "@t0")
  /** true if we start to play immediately */
  var isPlaying: Boolean = xBool(simulParam, "simul", "@isPlaying")
  var showMore:Boolean=true

  /** the layers which are already expanded are saved, so that we do  not need to expand them again from one run to the next */
  var expandedLayers: Set[String] = fromXMLasList((displayParam \\ "expandedLayer").head).toSet
  expandedLayers = expandedLayers.filter(progCA.displayableLayerHierarchy().contains(_)) //we remove layers no longer existing

  /** updates the xml containing all the Param of the CAs, for the moment we only save expanded layers, and displayed fields, with their colors
   * we drop the two hexa digit of the alpha component of colors, it is not used */
  private def updateAndSaveXMLparamCA(): Unit = {
    displayParam =
      <displayParam>
        <expandedLayer>
        {expandedLayers.map(nameLayer => <Layer>
          {nameLayer}
        </Layer>)}
      </expandedLayer>
        <colorOfField>
          {colorDisplayedField.keys.map(nameField => {
          val c = colorDisplayedField(nameField) //we and with 0xFFFFFF because we do use the alpha parameter
          <layer color={"0x" + c.getRGB.toHexString.toUpperCase.drop(2)}>
            {nameField}
          </layer>
        })}
        </colorOfField>
      </displayParam>
    XML.save("src/main/java/compiledCA/displayParam/" + nameCA + ".xml", displayParam)
  }


  private def updateAndSaveXMLGlobalInit(): Unit = {
    val newGlobalInit =
      <initMethod>
        {globalInit \\ "inits"}<selected rank={"" + globalInitNames.indexOf(globalInitList.selection.item)} seed={"" + randomRoot }/>
      </initMethod>
    XML.save("src/main/java/compiledCA/globalInit/" + nameGlobalInit, newGlobalInit)
  }

  /** must update randomRoot, but also density */
  private def updateAndSaveXMLSimulParam(): Unit = {
    val newSimulparam = simulParam.asInstanceOf[Elem].copy(child = simulParam.child.map {
      case simul @ <simul>{_*}</simul> =>
        simul.asInstanceOf[Elem] % Attribute(null, "randomRoot", randomRoot.toString, Null)
      case other => other
    })
    val newnewSimulparam = newSimulparam.asInstanceOf[Elem].copy(child = newSimulparam.child.map {
      case simul @ <simul>{_*}</simul> =>
        simul.asInstanceOf[Elem] % Attribute(null, "density", density.toString, Null)
      case other => other
    })
    val newnewnewSimulparam = newnewSimulparam.asInstanceOf[Elem].copy(child = newnewSimulparam.child.map {
      case simul @ <simul>{_*}</simul> =>
        simul.asInstanceOf[Elem] % Attribute(null, "darkness", darkness.toString, Null)
      case other => other
    })
    XML.save("src/main/java/compiledCA/simulParam/" + nameSimulParam, newnewnewSimulparam)
  }



  class SimpleButton(ic: javax.swing.Icon) extends Button() {
    icon = ic
    contents += this
    Controller.this.listenTo(this) //Controller.this refer to the enclosing controller
  }


  val InitButton = new SimpleButton(initIcon)
  val ForwardButton = new SimpleButton(forwardIcon) //myButton(forwardIcon, this)
  val BackwardButton = new SimpleButton(backwardIcon) //myButton(forwardIcon, this)
  val FastForwardButton = new SimpleButton(fastForwardIcon) //myButton(forwardIcon, this)
  val FastBackwardButton = new SimpleButton(fastBackwardIcon) //myButton(forwardIcon, this)
  val PlayPauseButton = new SimpleButton(if (isPlaying) pauseNormalIcon  else playNormalIcon)
  val PlayReverseButton = new SimpleButton(playReverseIcon)
  val ShowCrossButton = new SimpleButton(closeBoxIcon)


  val speedSlider = new Slider {
    min = 0
    max = 18
    value = 0
    majorTickSpacing = 6
    minorTickSpacing = 2
    paintTicks = true
    paintLabels = true
    contents += this
    Controller.this.listenTo(this)
  }

  val speed = new Label("Speed : 0")
  contents += speed
  Controller.this.listenTo(this)

  //val globalInit: Array[String] = Array("center", "border", "yaxis","random")  //"onCircle", "random", "poisson", "blakHole"

  //Create the combo box, select the item at index 3.
  //Indices start at 0, so 3 specifies blackHole.
  val globalInitList = new ComboBox[String](globalInitNames) {
    selection.item = globalInitNames(selectedGlobalInit)
  }
  val randomInitList = new ComboBox[Int](randomInitNames) {
    selection.item = randomRoot
  }
  val densityInitList = new ComboBox[Int](densityInitNames) {
    selection.item = density
  }
    val darknessInitList = new ComboBox[Int](darknessInitNames) {
    selection.item = darkness
  }

  val statInitList = new ComboBox(statInitNames) {
    //selection.index=paramStat
  }
  //val randomRootField = new TextField("" + randomRoot, 2)
  contents += (globalInitList, randomInitList,densityInitList,darknessInitList,statInitList) //, randomRootField)

  listenTo(globalInitList.selection, randomInitList.selection,densityInitList.selection,darknessInitList.selection,statInitList.selection)
  //todo add a jcombo to select a number between 0 and 9
  /** When we switch mode between pause and play, the icon of the PlayPause button toggles */
  private def togglePlayPauseIcon(): Unit = {
    PlayPauseButton.icon =
      if (isPlaying) pauseNormalIcon
      else playNormalIcon
  }
  def checkNewLocus(loci:Set[Locus]) {
    val newLocus=loci.diff(displayedLocus)
    if (newLocus.nonEmpty) //we have a new locus to display
    {
      displayedLocus ++= newLocus
      updateProximity
      for (env <- envList)
        env.medium.voronoise(displayedLocus, currentProximityLocus)
    }
  }

    peer.setRollover(true)
  disableBinding(peer) //we want to use spacebar and left/right for other purpose than switching buttons in the toolbar
  listenTo(this.keys)
  //listenTo(mouse.clicks)


  reactions += {
    /*case EditDone(_) =>
      randomRoot = Integer.parseInt(randomRootField.text)
      InitButton.doClick() //we assume that we want a new random setting*/
    case ExpandLayer(s) =>
      expandedLayers += s
      updateAndSaveXMLparamCA()
      layerTree.hideRoot
      layerTree.repaint()
      mf.pack() //resize the window allocated to the tree so that the tree prints entirely
    // mf.unmaximize()
    // we hope it recomputes size of tree windows so as to accomodate
    //this.repaint()
    case CollapseLayer(s) =>
      expandedLayers -= s
      updateAndSaveXMLparamCA()
      layerTree.hideRoot
      layerTree.repaint()
      mf.pack()
    case ToggleColorEvent(s) =>
      val l = locusOfDisplayedOrDirectInitField(s)
      colorDisplayedField =
        if (colorDisplayedField.contains(s)) //we supress a color
        {
          colorDisplayedField -= s
          displayedLocus = colorDisplayedField.keys.map(locusOfDisplayedOrDirectInitField(_)).toSet + V()
          //checkNewLocus(HashSet(l)) c'est pas adapté en fait.
          if (!displayedLocus.contains(l)) {  //there is one locus minus
            updateProximity
            for (env <- envList)     env.medium.voronoise(displayedLocus,currentProximityLocus)
          }
          colorDisplayedField - s
        }
        else { //we add a color
          //checkNewLocus(HashSet(l))c'est pas adapté en fait.
        if (!displayedLocus.contains(l)) //we have a new locus to display
          {displayedLocus += l
           updateProximity
           for (env <- envList)
             env.medium.voronoise(displayedLocus,currentProximityLocus)
         }
         val mainColorLeft = mainColors.toSet.diff(colorDisplayedField.values.toSet)
         if (displayedAsText.contains(s)) colorDisplayedField + (s -> Color.black) //text field are in black
         //looks for a color
         else if (mainColorLeft.nonEmpty) {
           var naturalChoice = Math.abs(s.hashCode) % mainColors.length //the hashcode of the field name is used to associate a color to the field
           while (!mainColorLeft.contains(mainColors(naturalChoice)))
             naturalChoice = (naturalChoice + 1) % mainColors.length //look for the first main color not used yet
           colorDisplayedField + (s -> mainColors(naturalChoice))
         }
         else {throw new Exception("non color left amongst the main colors")
           colorDisplayedField
         } //we could not find a new color, the new field does not get a color! this won't happen supoesedly
       }
     updateAndSaveXMLparamCA()
     layerTree.hideRoot
     layerTree.repaint()
     repaintEnv()
   case ButtonClicked(InitButton)  =>//| KeyReleased(_, Key.A, _, _)
     val wasPlaying = isPlaying
     if (isPlaying) {
       PlayPauseButton.doClick()
     } //we need a temporary pause of the computing thread, so as to avoid having two threads run simultaneously
     initEnv()
     repaintEnv()
     requestFocus() //necessary to enable listening to the keys again.
     if (wasPlaying) PlayPauseButton.doClick()

   case ButtonClicked(PlayPauseButton) =>//| KeyReleased(_, Key.Space, _, _) =>
     isPlaying = !isPlaying
     togglePlayPauseIcon()
     if (isPlaying)
       playEnv(true) //lauch the threads
    case ButtonClicked(PlayReverseButton) =>//| KeyReleased(_, Key.Space, _, _) =>
      isPlaying = !isPlaying
      //togglePlayPauseIcon()
      if (isPlaying)
        playEnv(false) //lauch the threads
   case ButtonClicked(ForwardButton)=> //| KeyReleased(_, Key.Right, _, _)
     forwardEnv()
     repaintEnv()
    // requestFocus()
   case ButtonClicked(FastForwardButton)  =>
     fastForwardEnv()
     repaintEnv()
    // requestFocus()}
   case ButtonClicked(BackwardButton)  =>
     backwardEnv()
     repaintEnv()
   // requestFocus()
   case ButtonClicked(FastBackwardButton)  =>
     fastBackwardEnv()
     repaintEnv()
   case ButtonClicked(ShowCrossButton)  =>
     showMore= !showMore
     repaintEnv()
     //requestFocus()
case SelectionChanged(`globalInitList`) =>
     initButtonClick()//InitButton.doClick()
     updateAndSaveXMLGlobalInit()
   case SelectionChanged(`randomInitList`) =>
     randomRoot = randomInitList.selection.item
     initButtonClick()//InitButton.doClick()
     updateAndSaveXMLSimulParam()
    case SelectionChanged(`densityInitList`) =>
      density = densityInitList.selection.item
      initButtonClick()//InitButton.doClick()
      updateAndSaveXMLSimulParam()
    case SelectionChanged(`darknessInitList`) =>
      darkness= darknessInitList.selection.item
    //  initButtonClick()//InitButton.doClick()
      updateAndSaveXMLSimulParam()
   case ValueChanged(`speedSlider`) =>
     speed.text = s"Speed : ${speedSlider.value}"
 }

 /** ca bug si je fait initButton.doClick(), je ne sais pas pourquoi peut etre parceque
  * j'ai bricolé des changement de sdk et de version de  donc j'ai ecrit le code séparément, la ca a l'ai d'aller*/
 def initButtonClick(): Unit = {
   val wasPlaying = isPlaying
   if (isPlaying) {
     PlayPauseButton.doClick()
   } //we need a temporary pause of the computing thread, so as to avoid having two threads run simultaneously
   initEnv()
   repaintEnv()
   requestFocus() //necessary to enable listening to the keys again.
   if (wasPlaying) PlayPauseButton.doClick()
 }
 focusable = true
 requestFocus

 private def repaintEnv(): Unit = {
   for (env <- envList)
     env.repaint()
 }

  /**
   *
   * @param fwd plays forward if true, else backward
   */
 private def playEnv(fwd:Boolean): Unit =
   for (env <- envList)
     {env.play(fwd)

     }


 //2^speedSlider.value


 private def forwardEnv(): Unit =
   for (env <- envList)
     env.forward()
 private def backwardEnv(): Unit =
   for (env <- envList)
     env.backward(1)

 private def fastForwardEnv(): Unit =
   for (env <- envList)
     env.fastForward(Math.pow(2,speedSlider.value).toInt)
 private def fastBackwardEnv(): Unit =
   for (env <- envList)
     env.backward(Math.pow(2,speedSlider.value).toInt)

 private def initEnv(): Unit =
   for (env <- envList)
     env.init()
}

import java.awt.Color._
import java.lang.Integer.decode

object Controller {
 /** space and arrows where binded to toolBar browsing, this method let them become available keys for replacing  button clicking */
 def disableBinding(c: JComponent): Unit = {
   val im: InputMap = c.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
   for (key <- List("RIGHT", "LEFT", "SPACE")) //keys to be disabled so as to be used for own purpose
     im.put(KeyStroke.getKeyStroke(key), "none")
 }

}

private object colors {
 //primary, secondary and tertiary colors aranged on a "color wheel" which exhibits a toroidal metric.
 private val chartreuseGreen = new Color(decode("0x80FF00"))
 private val springGreen = new Color(decode("0x00FF80"))
 private val azure = new Color(decode("0x0080FF"))
 private val violet = new Color(decode("0x8000FF"))
 private val rose = new Color(decode("0xFF0080"))
 val mainColors: Array[Color] = Array(red, orange, yellow, chartreuseGreen, green, springGreen, cyan, azure, blue, violet, magenta, rose)
 //gray tones are used for fixed system layers such as debug, liveIf,
 val grays: Array[Color] = Array(darkGray, gray, lightGray, white)
}
