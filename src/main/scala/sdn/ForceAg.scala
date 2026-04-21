package sdn

import compiler.AST.Layer
import compiler.ASTBfun.derivative
import compiler.ASTL.{delayedL, unop}
import compiler.ASTLfun.{andLB2R, e, eq0, lt2, neighbors, neq, orScanRight}
import compiler.SpatialType.{BoolV, UintV}
import compiler.repr.nomE
import compiler.{ASTLt, B, Locus, V}
import dataStruc.{BranchNamed, Named}
import progOfmacros.Comm.neighborsSym
import progOfmacros.Wrapper.{exist, unary2Bin}
import sdn.Globals.root4naming

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** makes precise where a constraint applies*/
sealed trait Impact

/** constraint is applied whether it is empty or not */
case class Both() extends Impact

/** constraint will prevent filling (resp emptying), if noFill is true (resp. false)*/
case class One(noFill: Boolean) extends Impact //on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire


/** an entity such has a boolV or more generally a mustruct, which provide hasIsV, can be completed with utilAgent */
trait HasIsV {
  /**
   * used for computing flip cancelation depending on impact of constraint, so that constraint can act non only
   * which can be both(),  noFill(true) noFill(false)
   * case class One(noFill: Boolean) extends Impact
   * on veut pouvoir calculer le complementaire d'une contraint, forbid et oblige sont complementaire
   * not only for BoolV Agent, but also for Ev Agents
   */
  val isV: BoolV
  val notIsV: BoolV = ~delayedL(isV) //can be defined on agent, delayed is needed because  isV is not known yet
}
/**
* agents are boolean muStruct udated using force
  * * @tparam L  locus of the agent's support, we can have Vagent L=V, Ve AgentsL=Ve, ....
* For the moment we consider that all agents extend hasIsv, it may be the case that E-agents, do not.
  */
abstract class Agent[L <: Locus] extends MuStruct[L, B] with HasIsV {
  /** also used by DetectedAg */
  val agthis: Agent[L] = this
  var flipAfterConstr: BoolV = null
  var flipAfterSync: BoolV = null

  //Invariant : les contraintes sont  stoquée chez l'agent contraint qui est moi meme, mais aussi c.bounding.
  def checkInvariantSync: Unit = for ((_, c) <- constrsync) assert(c.bounding == this)
  var deflipSync: BoolV = null
  // each constrsync contributes a deflipsync that reduces flipAfter Constr
  def setFlipSync()={
    deflipSync= isV & ~isV  //on part de falseV
    checkInvariantSync
    //on va visiter tout les agent borné par l'agent courant, pour calculer le deflipSync de l'agent courant
    for((_,c)<-constrsync)
      deflipSync=deflipSync | c.zoneSync & c.cancel(flipAfterConstr,c.bounded.flipAfterSync)
    //to do, faudrait faire évoluer flipAfterConstr on se rends compte déja la que il faut considérer des chemins.
    flipAfterSync=flipAfterConstr & ~ deflipSync
    /** we can verify  deflipSync is false, for detected agents such as gcenter */
    //deflipSync=flipAfterSync ^ flipAfterConstr
   // if( constrsync.nonEmpty)   { val (_,c)=constrsync.head;   deflipSync=c.zoneSync & c.cancel(c.bounding.flipAfterSync,c.bounded.flipAfterSync)   }

  }
  /** flipAfterConsrtr is used as a first approximation to compute next, which is neccesary to know in order to compute keepOutside
   * however, when we build the force keepOutside, we do not have yet flipafterConstr, hence we need the delayed version */
  //val dflipAfterConstr=delayedL(flipAfterConstr)
  //var flipRandomlyCanceled: BoolV=null
  /** the two boolV will be synchronized flip being progressively rarefied.
   * if an agent forces several others, then its synchronized flip will be iteratively adjusted.
   * Whenever each output agents updates,    * we will likely have to iterate over path of increasing lenght
   * on a graphe where edges corresponds to synchronized agents,
   * and check intersection of constraints on intersection on synchronized zone,  */
  val constrsync= new scala.collection.mutable.LinkedHashMap[String,ConstrSync]()
  def addConstrSync(name:String, shortName:Char, c: ConstrSync) = {
    if(constrsync.contains(shortName+name))    throw new Exception("une contrainte sync du nom "+name+" exite déja, changez le nom siou plait")
    constrsync(shortName+name)=c  }
  /**  */
}

/** on l'ajoute a un agent qui souhaite en inclure un autre */
trait keepInsideForce {
  self : Agent[V]=>
  /** place where new self appears , available for agent which are detected agents */
  val nouveau= muis.munext & ~muis.pred
  val alreadyThere=muis.munext & muis.pred
  val willBeThere=muis.munext
  /** if there is an ag present next to nouveau , it will be pushed to fill the nouveau
   * noneed to empty whatever, so empty remains false.  */
  def keepInside:Force=  new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      /** the surrounding agent does not yet contain nouveau */
      val nouveauToFill = nouveau & ~ag.muis
      /** if not null will create a push in order to fill nouveau which are not yet filled */
      val push=neighbors(nouveauToFill) & e(ag.muis)
      val coveredByPush=exist(neighborsSym(push))
      /** should be true everywhere */
       val oui = MoveC1(~ag.muis & ag.muis, push)
      /** we must not empty voronoi in places where it will contain gcenters*/
      val non = MoveC1(willBeThere & ag.muis,e(root4naming.myFalse))
      MoveC2(oui,non)
    }
  }}
  /** if there is an ag present on nouveau , it will be emptied to prevent overlapp
   *  * noneed to empty whatever, so empty remains false.
   *  We have a problem, since keep outside needs to be computed
   *     - before computing the moves of voronoi,
   *     - after computing the flipAfterConstr of particles.
   *     =>In the first pass, we compute both flipOfMove and flipAfterCons
   *   NB as flipAfterSYnc is updated, in inputagent, so is the forced move,
      At the end of this process, the idea is that the final forced Move
        created from  a movable should no create inpossible move in the boundagents
   *  */
  trait keepOutsideForce{
    self : ForceAg[V] =>
  def keepOutside:Force=  new Force() {
    override def actionV(ag: MovableAgV): MoveC = {
      val fliipAafterCoonstr=    flipAfterConstr //le normal qui produit des millions de neouds
      val nouveauAfterConstr= ~muis.pred  & fliipAafterCoonstr //true if the particle agent fills
        val nouveauToEmpty = nouveauAfterConstr & ag.muis   // and if there was a voronoi it should therefore empties
      val remainThere  =   muis.pred   & ~fliipAafterCoonstr    //particle was there and remain there, voronoi should not come

      /** if not null will create a emptying of  nouveau where ag is filled */
      val oui = MoveC1(nouveauToEmpty, e(root4naming.myFalse))
      /** we must not push voronoi towards vertices that will contain particles */
        val willbethere=nouveauAfterConstr | remainThere
      val non = MoveC1(muis.pred & ~muis.pred ,ag.bf.brdVeIn & neighborsSym(e(willbethere)))  //particle was there and remain there, voronoi should not come
      MoveC2(oui,non)
    }
  }
}


/** detected Agents directly compute their next state using a field called "detected"
 * typically, gCenter is a detected agent
 * they are not really agent because they do not undergo forces.
 * we can compute deflipSimult, also for those agents, in order to check that no deflip will apply
 * indeed, if a deflip would apply it would modify the simple detection.*/
abstract class DetectedAgV ( val detected: BoolV )  extends Agent[V] {
  /** support of agent, implemented as a layer. we also use it to store a list  of system instructions */
  override val muis=new Layer[(V, B)](1, "globalInv") with ASTLt[V,B]  with Stratify [V,B] with carrySysInstr   {
    override val  next = detected  }
  override val isV: BoolV = muis
  /** artificially reconstructed, we will be able to watch if it happens to be canceled by simult constraint */
   flipAfterConstr=muis ^ muis.next
  def showme={shoow(detected,muis,deflipSync)}
  override def checkInvariantSync: Unit = {
    super.checkInvariantSync
    buugif(deflipSync) //synchronisation should not disturb the completely deterministic movement of a detected agent.
    //it should never happen that a failure of flip of voronoi due for example to blob constraints, causes a failure of flip of
    //gabriel centers.
  }
}

//class Gcenter(arg: ) extends DetectedAgV

object ForceAg{
  /** Type alias for a generic forced agent with any supported locus type. */
  type Agg = ForceAg[_ <: Locus]
  /** Type alias for any agent (forced or detected) with any supported locus type. */
  type Aggg = Agent[_ <: Locus]
}

/**
 * Base class for agents whose next state is computed from forces and constraints.
 *
 * `ForceAg` models the "active" branch of agents (as opposed to purely detected agents such as
 * `DetectedAgV`). Subclasses provide trigger/flip encodings (`allTriggered`, `allTriggeredYes`,
 * `allFlip`) and random tie-breaking bits (`prioRand`), while this class orchestrates:
 *
 * - building moves from declared forces,
 * - selecting the highest-priority effective move,
 * - staged cancellation through local/mutex/sextex constraints,
 * - exposing debugging views for selected moves and active constraints.
 *
 * Typical lifecycle per simulation step:
 * 1) `setFliprioOfMove()`
 * 2) `setFlipCancel()`
 * 3) synchronization phase (`Agent.setFlipSync`) handled at orchestration level.
 *
 * @tparam L locus type (spatial support of the agent)
 */
abstract class ForceAg[L <: Locus] extends Agent[L] {
  //val priorityObliged:Int

  /**
   * Forces grouped by priority. Each map key is `shortName + name`.
   *
   * A force is converted into a centered move during `applyForces`.
   */
  val forces: ArrayBuffer[mutable.LinkedHashMap[String,Force]] = ArrayBuffer()

  /** Returns all registered forces, including structural/bounding forces when relevant. */
  def allForces: mutable.Seq[mutable.LinkedHashMap[String, Force]] = forces

  /**
   * Registers a force at a given priority level.
   *
   * @param priority priority bucket index
   * @param name human-readable force name
   * @param shortName short prefix used by debug displays
   * @param f force definition
   */
  protected def addForces(priority: Int, name: String, shortName: Char, f: Force ): Unit = {
    //we may have to store set of moves, if we need add move of same priority.
    val ht = forces(priority)
    assert(!ht.contains(name), "each force must have a distinct priority");
    forces(priority)(shortName+name) = f
  }

  /**
   * Generated moves grouped by priority, in centered representation.
   *
   * Each priority level stores a `LinkedHashMap` keyed by `shortName + name` to preserve
   * declaration order for display and diagnostics.
   */
  val moves: ArrayBuffer[mutable.LinkedHashMap[String,MoveC]] = ArrayBuffer() //empty at the beginning

  /**
   * Adds a new priority slot for both forces and generated moves.
   *
   * @return index of the created priority level
   */
  def introduceNewPriority(): Int = {
    moves+= mutable.LinkedHashMap[String,MoveC]();
    forces+= mutable.LinkedHashMap[String,Force]();
    moves.size-1
  }
  /**
   * Adds a generated move to a priority level.
   *
   * @param priority priority bucket index
   * @param name move name
   * @param shortName short prefix used by debug displays
   * @param m centered move generated from a force
   */
  protected def addMoves(priority:Int, name:String, shortName:Char, m: MoveC): Unit = {
    //we may have to store set of moves, if we need add move of same priority.
    val ht=moves(priority)
    assert(!ht.contains(name), "each force must have a distinct priority");
    moves(priority)(shortName+name)=m
  }

  /** Generates centered moves from all declared forces. */
  def applyForces: Unit = {
    var priority = 0
    for(mapForces <- allForces) {
      for((name,f)<-mapForces)
          addMoves(
            priority,
            name.drop(1),
            name(0),
            f.action(this.asInstanceOf[MovableAgV]))
          priority+=1
    }

  }

  /**
   * Ordered constraints keyed by `shortName + name`.
   *
   * Each value is a function because constraints are instantiated with runtime `fliprio` information,
   * which is not available at registration time.
   */
  val constrs: mutable.LinkedHashMap[String, PartialUI => Constr] =
    new scala.collection.mutable.LinkedHashMap[String,PartialUI =>Constr]()

  /**
   * @param name more explicit name
   * @param shortName used for display in CApannel
   * @param c constraint to be added to the list of agent's constraint
   *          it is a function because at the time of adding the constraint, prio and flip are not known yet
   */
  def addConstraint(name:String, shortName:Char, c: PartialUI=>Constr): Unit = {
    if(constrs.contains(shortName+name))
      throw new Exception("une contrainte du nom " + name + " exite déja, changez le nom siou plait")
    constrs(shortName+name) = c
  }



  /** Per-priority trigger encoding (subclass-specific for movable/bound agents). */
  def allTriggered: UintV
  /** Per-priority "bug" diagnostics for move proposals. */
  def allBug: UintV
  /** Per-priority trigger encoding restricted to positive/"yes" transitions. */
  def allTriggeredYes: UintV
  /** Flips for all priorities */
  def allFlip: UintV

  //variable defined when computing fliprioOfMove
  /** True where selected positive and selected global priorities diverge (quiescent state). */
  var isQuiescent: BoolV = null
  /** Highest triggered move considering yes/no branches. */
  var yesnoHighestTriggered: UintV = null
  /** Highest triggered move considering positive branch only. */
  var yesHighestTriggered: UintV = null
  /** Cached bug diagnostics at selection time. */
  var allBugs: UintV = null
  /**  adds some randomness to forces' priority, allowing to  break symetry in case of tournament with equal force priority */
   val prioRand: UintV
   /** Selected move as `(defined, priority)` pair after force arbitration. */
   var fliprioOfMove: PartialUI = null

  /** Flat name -> move view used by reflection/debug tooling. */
  val mergedMoves: mutable.HashMap[String, MoveC] with Named with BranchNamed =
    new mutable.HashMap[String, MoveC]() with Named with BranchNamed {}

  /**
   * Computes `fliprioOfMove` from generated moves.
   *
   * This method:
   * - materializes moves from forces,
   * - selects highest triggered priority (global and "yes" variants),
   * - computes effective flip bits,
   * - computes quiescence and priority value used by local constraints.
   *
   * Side effects: updates `mergedMoves`, `yesnoHighestTriggered`, `yesHighestTriggered`,
   * `allBugs`, `isQuiescent`, and `fliprioOfMove`.
   */
  def setFliprioOfMove() = {
    applyForces
    /** stores all the moves in a single hashMap, with the name of the force as key, so that we can easily shoow them */
    for (m <- moves; (k, v) <- m) mergedMoves(k.drop(1)) = v
    /** does a computation to be repeated specifically for yes moves */
    def processMoves(all:UintV):(UintV,UintV,UintV)={
      /** bouche les trous avec un orscanright */
      val filled=orScanRight(all)
      (filled,unop(derivative, filled),unary2Bin(filled))
    }

    val (filledTriggered,/** all false except for highest priority move */ highestTriggered, prioDet: UintV) = {
      processMoves(allTriggered)
    }
    yesnoHighestTriggered=highestTriggered
    /** selectionne le flip parmis les flip des mouvement proposés */
    val flipOfMove = neq(highestTriggered & allFlip)

    /** on le fait aussi pour les "yes" move */
    val (yesFilledTriggered, yHT, yesPrioDet) = {
      /**
       * Makes a global logical or, of boolean which are true for C2moves,
       * if false then there will not be negative move
       * and yesFilledtriggered is equal to fill triggered, thereby simplifying the computation
       */
      val presenceOfC2moves = moves.map(_.values.map({case _: MoveC2 =>true case _: MoveC1 =>  false}).reduce(_ | _)).reduce(_ | _)
      if (!presenceOfC2moves ) (filledTriggered, highestTriggered, prioDet)
      else processMoves(allTriggeredYes)
    }
    allBugs=allBug
    yesHighestTriggered = yHT //used for printable purpose
    /** selected positive move has lower priority than selected move, implies quiescence */
    isQuiescent = lt2(yesPrioDet, prioDet)
    val prioYes: UintV = prioRand :: yesPrioDet
    /**
     * nullify prio if vertice is quiescent we are interested only in high prio only if move is generated
     * this priority is the one to be used when evaluationg local constraints
     */
    val prioYesNotQuiescent = Util.addLt(andLB2R(~isQuiescent, prioYes))
    fliprioOfMove=new PartialUI(flipOfMove, prioYesNotQuiescent)
  }
  //setFliprioOfMove() //this is now done separately
  //val flipCancelLocal=  new scala.collection.mutable.LinkedHashMap[String,BoolV]() with Named {}

  /**
   * Random high-probability mask used to thin flips after synchronization.
   * Implemented as OR of two independent random bits.
   */
  val highproba: BoolV =
    root4naming.addRandBit().asInstanceOf[BoolV] | root4naming.addRandBit().asInstanceOf[BoolV]

   /** Constraint cancellation bits after local stage. */
   var  allFlipLocalCanceled: UintV = null
   /** Partial flip state after local constraints. */
   var flipAfterLocalConstr: PartialUI=null
   /** Constraint cancellation bits after mutex/mutApex/tritex stage. */
   var  allFlipMutexCanceled: UintV = null
   /** Partial flip state after mutex/mutApex/tritex constraints. */
   var flipAfterMutexConstr: PartialUI = null
   /** Constraint cancellation bits after sextex stage. */
   var  allFlipSextexCanceled: UintV = null
   /** Partial flip state after sextex constraints. */
   var flipAfterSextexConstr: PartialUI = null
   /** Cached partition of constraints by semantic family. */
   var splitConstr: SplitHashMapTyped.Split[String] = null

  /**
   * Evaluates a subset of constraints and merges their cancellation bits.
   *
   * @param fliprio current partial flip/prio state
   * @param subConstrs ordered subset of constraints to evaluate
   * @return packed cancellation bits, one slice per constraint
   */
  def allFlipCancel(fliprio: PartialUI, subConstrs:mutable.LinkedHashMap[String,sdn.PartialUI => sdn.Constr]): UintV = {
    /** stores results of applies the passed contraint in subConstr, using fliprio */
    val flipCancel = new scala.collection.mutable.LinkedHashMap[String,BoolV]() with Named {}
    for ((name, c) <- subConstrs)   flipCancel(name) = ~c(fliprio).where & fliprio.defined //where also takes into account flipOfMove
    val allFlipCancel: Array[UintV] = flipCancel.values.toArray.map(_.asInstanceOf[UintV])
    allFlipCancel.reduce(_ :: _)
  }

  /**
   * Applies staged constraint filtering and computes `flipAfterConstr`.
   *
   * Stages are applied in this order: local -> mutex/mutApex/tritex -> sextex.
   * This preserves more movement opportunities while keeping directional constraints last.
   *
   * Side effects: updates split/canceled fields and `flipAfterConstr`.
   */
  def setFlipCancel()= {
    // We separate local  then  mutex, mutapex, tritex and then sextex
    // it increases movement, mutex  will be more selective, since they come after
    // local constraints have been applied
    // also sextex will choose a direction among those remaining valid.
    // in order to be able to spot progressive narrowing of flip, in case of bugs

    splitConstr = SplitHashMapTyped.splitConstrs(constrs)

    // New staged computation more precise.
    allFlipLocalCanceled = allFlipCancel(fliprioOfMove, splitConstr.locals)
    flipAfterLocalConstr = fliprioOfMove.rarefies(eq0(allFlipLocalCanceled))

    // On regroupe les différents mutex et tritex, car ils opérent en exclusion les uns de autres.
    // Par exemple, apexmutex n'opére pas en meme temp que mutex ni que tritex
    allFlipMutexCanceled =
      allFlipCancel(flipAfterLocalConstr, splitConstr.mutexes++splitConstr.mutApexes++splitConstr.tritexes)
    flipAfterMutexConstr =
      flipAfterLocalConstr.rarefies(eq0(allFlipMutexCanceled))

    // On calcul le sextex uniquement quand c'est nécessaire
    if(splitConstr.sextexes.nonEmpty){
      allFlipSextexCanceled = allFlipCancel(flipAfterMutexConstr, splitConstr.sextexes)
      flipAfterSextexConstr = flipAfterMutexConstr.rarefies(eq0(allFlipSextexCanceled))   }
    else flipAfterSextexConstr = flipAfterMutexConstr

    //former global computation.    allFlipCancel=allFlipCancel2(fliprioOfMove,constrs);   val noFlipCancel=eq0(allFlipCancel)

    val noFlipCancel = flipAfterSextexConstr.defined
    flipAfterConstr = noFlipCancel  & fliprioOfMove.defined
    //we will randomly cancel only if not obliged flip
  }

  /** Final stochastic thinning applied after sync stage. */
  def flipRandomlyCanceled: BoolV = flipAfterSync & highproba


  /**
   * Stores the label (first letter of name) of each move for all priorities.
   *
   * This lettre is to be displayed if move is selected.
   * There can be at  most  one positive move selected.
   * If move is blocking nothing get displayed, and  isquiscent will be true.
   */
  def codeMove: Iterable[String] = {
    assert(moves.size > 1,"faut au moins deux move, sinon pb entier codé par un bool")
    moves.map(_.keys.head.charAt(0).toString)
  }

  /** Displays selected positive move diagnostics (without blocking-only moves). */
  def showPositiveMoves={
    shoowText(yesHighestTriggered,codeMove.toList)
    shoowText(yesnoHighestTriggered,codeMove.toList)
    // shoowText(prioDeet,List())
    shoowText(allBugs,codeMove.toList)
  }

  // /** shows also  moves that block movement */
  // def showMoves={ shoowText(highestTriggered,codeMove.toList)}

  /** Displays flip/prio internals, including quiescence and staged filtering outputs. */
  def showAllFlip: Unit = {
    shoowText(fliprioOfMove.valuc, List() )
    shoow(fliprioOfMove.valuc.lt)
    shoow(fliprioOfMove.defined, isQuiescent, flipAfterConstr,flipAfterLocalConstr.defined,
      flipAfterMutexConstr.defined)
  }

  /**
   * Stores the label (first letter of name) of each constraint.
   *
   * This lettre is to be displayed on vertices where the constraint is active.
   * There can be several active constraints.
   */
  def codeConstraint(constrs:mutable.LinkedHashMap[String,PartialUI=>Constr]): Iterable[String] =constrs.keys.toList.map(_.charAt(0).toString)

  /** Shows a letter corresponding to the constraint, for all constraint which effectively contribute in reducing flip */
  def showConstraint={
    // shoowText(allFlipCancel,codeConstraint(constrs).toList)
    shoowText(allFlipLocalCanceled,codeConstraint(splitConstr.locals).toList)
    shoowText(allFlipMutexCanceled,codeConstraint(splitConstr.mutexes++splitConstr.mutApexes++splitConstr.tritexes).toList)
    if(splitConstr.sextexes.nonEmpty)  shoowText(allFlipSextexCanceled  ,codeConstraint(splitConstr.sextexes).toList)
  }

  /** Convenience debug entry point: move diagnostics + constraint diagnostics + flip internals. */
  def showMe: Unit = {
    showPositiveMoves
    showConstraint
    showAllFlip
  }
}
