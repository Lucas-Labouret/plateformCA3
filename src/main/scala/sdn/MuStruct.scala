package sdn

import compiler.AST.{Layer, delayed}
import compiler.ASTL.{ASTLg, delayedL}
import compiler.SpatialType.BoolV
import compiler.repr.{nomB, nomV}
import compiler.{AST, ASTBt, ASTL, ASTLfun, ASTLt, B, CallProc, Circuit, I, Locus, Ring, SI, UI, V, repr}
import dataStruc.{BranchNamed, DagNode, Named}
import dataStruc.DagNode.EmptyBag
import sdn.ForceAg
import sdn.ForceAg.{Agg, Aggg}
import sdn.MuStruct.allMuStruct

import scala.Predef.->
import scala.collection.immutable.{HashMap, HashSet}
import scala.collection.mutable

/**
 * Trait that enables the carrying of system instructions (debugging, displaying, etc.).
 *
 * This trait allows AST nodes to carry compiler directives such as show, debug, and other system
 * instructions. Previously, only layers could use system instructions, but this generalization
 * enables any AST node to carry such instructions.
 *
 * @see [[CallProc]]
 */
trait carrySysInstr{
  /** List of system instruction procedures to be applied by the compiler */
  var syysInstr: List[CallProc] = List.empty;
}

/**
 * Trait that defines a component having a [[muis]] (layer/strate) with system instructions support.
 *
 * This trait is a marker that indicates a class has a `muis` (Multi-Unit Interface Support) field
 * that implements both layer functionality and system instruction carrying capability.
 *
 * @see [[carrySysInstr]]
 */
trait hasMuisSysInstr{
  /** The layer/strate that supports system instructions */
  val muis: ASTLg with carrySysInstr
}

/**
 * Provides methods for adding debugging and display system instructions to AST nodes.
 *
 * This trait offers a convenient interface for adding various types of compiler directives
 * to the system instruction list, including debugging breakpoints, statistics tracking,
 * and output display with custom labels. All methods work by appending [[CallProc]] entries
 * to the underlying [[muis]] system instructions list.
 *
 * @note This trait requires the implementing class to extend [[hasMuisSysInstr]]
 */
trait shoow{
  self: hasMuisSysInstr =>

  /**
   * Adds a debugging breakpoint for the given value.
   *
   * @param v the AST value to debug
   */
  def buugif(v: AST[_]): Unit =
    muis.syysInstr ::= CallProc("bug", List(), List(v))

  /**
   * Adds a conditional statistics tracking instruction.
   *
   * @param isDef condition that determines whether statistics should be collected
   * @param value the value to track statistics for
   * @tparam L the locus (spatial type) of the condition
   * @tparam R the ring (value type) to track
   */
  def staat[L<:Locus,R<:I](isDef:ASTLt[L,B],value:ASTLt[L,R]): Unit =
    muis.syysInstr ::= CallProc("stat", List(), List(isDef,value))

  /**
   * Adds one or more values to the display output.
   *
   * @param vs variable arguments of AST values to display
   */
  def shoow(vs: AST[_]*): Unit =
    for (v <- vs) muis.syysInstr ::= CallProc("show", List(), List(v))

  /**
   * Adds a value to display output with custom field labels.
   *
   * @param v the AST value to display
   * @param ls list of custom labels for the fields of the value
   */
  def shoowText(v: AST[_],ls:List[String]): Unit = {
    muis.syysInstr ::= CallProc("show", List(), List(v))
    Circuit.labelsOfFieldsBeforeName = Circuit.labelsOfFieldsBeforeName + ((v , ls))
  }

  /**
   * Adds one or more values to the display output with empty labels.
   *
   * @param vs variable arguments of AST values to display
   */
  def shot(vs: AST[_]*): Unit =
    for (v <- vs) shoowText(v, List())
}

/**
 * Layer-based Directed Acyclic Graph (LDAG) accessor.
 *
 * This class provides access to the root element of the computation hierarchy stored in
 * the global [[MuStruct.allMuStruct]] collection. It ensures that the compute entry point can be
 * efficiently accessed throughout the simulation/compilation process.
 *
 * @see [[MuStruct]]
 * @see [[MuStruct.allMuStruct]]
 */
class LDAG{
  /**
   * Returns the root element of the computation hierarchy.
   *
   * The particle is always the first MuStruct created and inserted into the global
   * allMuStruct collection, serving as the entry point for all computations.
   *
   * @return the root MuStruct element
   */
  def  particle: MuStruct[_ <: Locus, _ <: Ring] = allMuStruct.head
}

/**
 * Trait that transforms a Layer into a Strate compatible with the MuStruct hierarchy.
 *
 * This trait enables layers to function as strates (computation units) within the MuStruct
 * framework by providing delayed next-state computation. It allows layers to maintain
 * their spatial and ring type parameters while fitting into the directed acyclic graph
 * structure of MuStruct.
 *
 * @tparam L the locus (spatial type) of the layer
 * @tparam R the ring (value type) of the layer
 *
 * @see [[ASTL.Strate]]
 * @see [[LayerS]]
 */
trait Stratify[L<:Locus,R<:Ring] extends ASTL.Strate[L,R] {
  self: Layer[(L, R)] =>

  /** Predicate representing the current state of the layer */
  val pred: ASTLt[L, R] = this.asInstanceOf[ASTLt[L,R]]
  /** Next state computation, delayed to allow proper cycle handling */
  //todo faire a l'envers: on defini munext, et on dit que next = delayed munext
  override val munext: ASTLt[L, R] = delayedL(this.next.asInstanceOf[ASTLt[L,R]])(self.mym)
}

/**
 * A Layer variant that integrates system instruction support.
 *
 * This abstract class extends the standard Layer with the [[Stratify]] trait to fit into the
 * MuStruct hierarchy, and adds the [[carrySysInstr]] trait to enable storage and management
 * of compiler system instructions (debugging, display, statistics tracking, etc.). This allows
 * layers to participate fully in the compiler's directive system.
 *
 * @tparam L the locus (spatial type) parameter
 * @tparam R the ring (value type) parameter
 *
 * @param nbit number of bits for the layer state representation
 * @param init initial state as a string
 * @param m implicit representation for the spatial type
 * @param n implicit representation for the value type
 *
 * @see [[Layer]]
 * @see [[Stratify]]
 * @see [[carrySysInstr]]
 */
abstract class LayerS[L<:Locus,R<:Ring](override val nbit: Int, override val init: String)(implicit m: repr[L],n:repr[R])
  extends Layer[(L,R )](nbit,init) with Stratify[L,R] with ASTLt[L,R] with carrySysInstr()

/** si mixé avec, transforme une layer en mustruct */
//trait LayerToStrate[L<:Locus,R<:Ring] extends  Stratify[L,R] with ASTLt[L,R] with carrySysInstr  { this: AST.Layer[(L,R)] =>}

/**
 * Multi-Unit Structure: The core element of the Layer-based Directed Acyclic Graph (LDAG).
 *
 * MuStruct represents a computation unit in the hierarchical simulation/compilation framework.
 * Each MuStruct:
 * - Is automatically registered in the global [[allMuStruct]] collection upon creation
 * - Extends [[DagNode]] to participate in directed acyclic graph ordering and updates
 * - Carries identification through [[Named]] and branch naming via [[BranchNamed]]
 * - Supports system instruction management through [[hasMuisSysInstr]] and [[shoow]]
 * - Executes through a [[muis]] (layer/strate) that can be updated in proper order
 *
 * The naming path flows through MuStruct instances rather than through individual layers,
 * providing a hierarchical naming scheme for the entire system.
 *
 * @tparam L the locus (spatial type) representing the location/space type
 * @tparam R the ring (value type) representing the value type of the state
 *
 * @see [[LDAG]]
 * @see [[MuStruct.allMuStruct]]
 * @see [[DagNode]]
 * @see [[hasMuisSysInstr]]
 */
abstract class MuStruct[L<:Locus,R<:Ring] extends  DagNode[MuStruct[_<:Locus,_<:Ring]]
  with Named with BranchNamed with hasMuisSysInstr with shoow {
  allMuStruct.append( this) //insert new created muStruct on  last position of already instanciated mu struct

  /** Support of agent, implemented as a layer. Also stores system instructions for the agent */
  val muis: ASTL.Strate[L,R] with ASTLt[L,R] with carrySysInstr

  /** @return the locus type of this MuStruct*/
  def locus: Locus = muis.locus//todo, on pourrait calculer cela directement
}

/**
 * Trait that provides an empty bag implementation for MuStruct elements.
 *
 * This trait extends the [[EmptyBag]] interface to handle empty collections of MuStruct
 * instances in the directed acyclic graph framework.
 *
 * @see [[EmptyBag]]
 * @see [[MuStruct]]
 */
trait muEmptyBag extends EmptyBag[MuStruct[_ <: Locus, _ <: Ring]]
/** Bound agent need not layers */
//abstract class BoundAg[L<:Locus] extends Agent[L]
/** movable agent stores their chi in a layer, in order to be able to modify it. */

/**
 * Companion object for [[MuStruct]] containing global state and utility methods.
 *
 * This object manages the global collection of all MuStruct instances and provides
 * methods for updating and debugging the hierarchical structure of the simulation/compilation framework.
 */
object MuStruct{
  /** Global collection of all MuStruct instances in order of creation */
  var allMuStruct: mutable.ArrayDeque[MuStruct[_<:Locus,_<:Ring]] = mutable.ArrayDeque()

  /**
   * Displays all MuStruct instances in the collection.
   *
   * This method prints the string representation of each MuStruct.
   *
   * @note that this can only be called after the DataProg has been built and names have been assigned using reflection.
   */
  def showMustruct(): Unit =
    for(m<-allMuStruct) System.out.println(m.toString)

  /**
   * Sets the flip priority of move operations and flip cancellations for all ForceAg instances.
   *
   * After construction, this method iterates through all MuStruct instances and configures
   * the flip priority and cancel settings for any ForceAg agents.
   */
  def setFliprioOfMoveAndFlipAfterConstr(): Unit = for(m<-allMuStruct) m match {
    case a: ForceAg[_] =>
      a.setFliprioOfMove()
      a.setFlipCancel()
    case _ => ()
  }

  /**
   * Sets the synchronized flip for all Aggg instances.
   *
   * This method processes MuStruct instances in reverse order to properly update the synced flip
   * of input agents. The synced flip is stored in the constraint itself as a destination.
   */
  def setFlipSynced(): Unit =
    for(m<-allMuStruct.reverse) m match {
    case a: Aggg =>
      a.setFlipSync()
    case _ => ()
  }

  /**
   * Debugging utility method for displaying special debug information.
   *
   * This method iterates through all MuStruct instances and displays any special debug
   * information that may be useful for troubleshooting. Currently targets Vor instances.
   */
  def showTrucPourDebugger(): Unit =
  for(m<-allMuStruct) m match {
    case v:Vor =>
      v.tmp=v.bf.lightConcave
      v.shoow(v.tmp)
    case _ =>
  }

  //var sortedMuStruct:List[MuStruct[_<:Locus,_<:Ring]]=List()

  //def const[L <: Locus, R <: Ring](cte: ASTBt[R])(implicit m: repr[L], n: repr[R]): ASTLt[L, R] = Coonst(cte, m, n)
}
