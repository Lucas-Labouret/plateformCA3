package compiler

import Constraint._
import dataStruc.Align2._


import scala.collection.immutable.{ArraySeq, HashSet}

/**
 * Represents a set of schedules of a 2Dfield's components.
 * @param locus 2Dtype of the field
 */
sealed abstract class Constraint(val locus:Locus)
{  /**The number of possible schedules checking the constraint.  */
  def card:Int
  /**Defined for constraint between a T component and an E/F component,
   * if there is a unique possible T schedule, for each E (or each F) schedule
   * it transforms an E or an F schedule into a T schedule*/
  def propagateFrom(a: Array[Int]): Option[Array[Int]] = None

  /** Verifies if a  schedule satisfies the constraint
   *
   * @param a schedules to be checked */
  def verified(a: Seq[Int]): Boolean

  /** Applies a permutation to a constraint.  Used for aligning  to a new  root
   * valid only for transfer constraints
   *
   * @param p the alignement to the new root */
  def permute(p: Array[Int], locus: Locus): Constraint

  /** @return all the schedules verifying the constraint  */
  def schedules: HashSet[Seq[Int]]= {
    // Générer les permutations des chiffres 0 à 5
    val lazyPerms = permutations(Seq(0, 1, 2, 3, 4, 5))

    // Appliquer le filtre
    val filteredPerms: Seq[Seq[Int]] = lazyPerms.filter(verified)

    // Consomme et affiche seulement les 5 premières permutations filtrées
    HashSet[Seq[Int]]()++filteredPerms
  }
  def printSchedules(): String = {
    var result: String = "";
    for (s: Seq[Int] <- schedules)
      result += s.map(locus.the6sufx(_)).mkString("->")+" "
    result
  }

  /** Compute a joint constraint.  generates the schedules for the smallest card, and verify with the other.
   * unless specific cases where it can be deduced in a cheaper way */
  def intersect(c: Constraint): Constraint = {
    require(c.locus == this.locus, "intersected constraint must have identical loci")
    if (c.isInstanceOf[AllConstr] || (c == this)) this
    else if (c.card < card) c.intersect(this) // c has smallest card
    else Schedules(HashSet.empty[Seq[Int]] ++ schedules.filter(c.verified), c.locus)
  }

  /** In general an isolated constraint has at least one schedule satifying it */
  def empty: Boolean = false

  /** constraint obtained by picking one schedule
   * TODO could be improved to avoid generate all the schedules, but only the first one! */
  def pick(): Constraint = {
    if (empty) throw new RuntimeException("empty constraint cannot be picked + this")
    val s = schedules
    Schedules(HashSet(s.head), locus)
  }
}

object Constraint {
  // Fonction pour générer les permutations de manière paresseuse
  def permutations[T](seq: Seq[T]): LazyList[Seq[T]] = {
    if (seq.isEmpty) LazyList(Seq.empty)
    else {
      for {
        i <- LazyList.from(seq.indices) // Indices des éléments
        perm <- permutations(seq.take(i) ++ seq.drop(i + 1)) // Récursion sur les sous-séquences
      } yield seq(i) +: perm
    }
  }


  def intersect(c1: Option[Constraint], c2: Option[Constraint]): Option[Constraint] =
    (c1, c2) match {
      case (None, None) => None
      case (None, Some(c)) => Some(c)
      case (Some(c), None) => Some(c)
      case (Some(c), Some(cc)) => Some(c.intersect(cc))
    }

  def permute(c: Option[Constraint], p: Array[Int], l: Locus): Option[Constraint] =
    c match {
      case None => None;
      case Some(c2) => Some(c2.permute(p, l))
    }

  def noneIsEmpty(cs: List[Constraint]): Boolean = {
    for (c <- cs) if (c.empty) return false;
    return true
  }

  def noneEmpty(cs: List[Constraint]): Boolean = cs.map(_.empty).reduce((x, y) => x || y)

  def intersect(cs: List[Constraint], l: Locus): Constraint = {
    var res: Constraint = AllConstr(l)
    for (c <- cs) res = res.intersect(c)
    res
  }
  final case class Aligned(val srcInstr:Affect[_], override val locus: Locus) extends Constraint(locus){
    var src:Zone=null  //checher la zone qui contient srcInstr.

    override def intersect(c:Constraint)={
      if(c.verified(src.pickedSchedule)) this else Schedules(HashSet(), locus)
    }
    /**   The number of possible schedules checking the constraint. */
    override def card: Int = 1

    /** Verifies if a  schedule satisfies the constraint
     *
     * @param a schedules to be checked, returns true if a is a possible shedule */
    override def verified(a: Seq[Int]): Boolean = throw new Exception(" faut pas tester verfified");false

    /** Applies a permutation to a constraint.  Used for aligning  to a new  root
     * valid only for transfer constraints
     *
     * @param p the alignement to the new root */
    override def permute(p: Array[Int], locus: Locus): Constraint = this

    /** @return all the schedules verifying the constraint */
    override def schedules: HashSet[Seq[Int]] = HashSet(src.pickedSchedule)
  }

  final case class H1beforeH2(override val locus: Locus,b:Array[Int]=Array(0,1,2,3,4,5) )extends Constraint(locus){
    /**   The number of possible schedules checking the constraint. */
    override def card: Int = 90

    /** Verifies if a  schedule satisfies the constraint
     *
     * @param a schedules to be checked, returns true if a is a possible shedule */
    override def verified(a: Seq[Int]): Boolean = a(b(0))<a(b(1)) && a(b(2))<a(b(3)) && a(b(4))<a(b(5))
    /** Applies a permutation to a constraint.  Used for aligning  to a new  root
     * valid only for transfer constraints
     *
     * @param p the alignement to the new root */

    override def permute(p: Array[Int], l: Locus): H1beforeH2 = H1beforeH2(locus, compose(invert(p), b))
    /** @return all the schedules verifying the constraint */


  }

  /** constraint defined by schedules. */
  final case class Schedules(b: HashSet[Seq[Int]], override val locus: Locus) extends Constraint(locus) {
    def card: Int = b.size

    def permute(p: Array[Int], l: Locus): Schedules = Schedules(b.map(_.map(p(_))), l)

    override def schedules: HashSet[Seq[Int]] = b

    override def empty: Boolean = schedules.isEmpty

    override def verified(a: Seq[Int]): Boolean = b.contains(a)

    private def printSched(a: Seq[Int]) = a.map(locus.the6sufx(_))

    override def toString: String = "on " + locus +
      (if (b.size == 1) "  picked" else ("there is " + b.size)) +
      "  schedules: " + printSchedules()
  }

  def empty(l: Locus): Schedules = Schedules(HashSet(),l)
  /**  constraint allways true.*/
    final case class AllConstr(override val locus:Locus) extends Constraint(locus){
    private val id=(0 to locus.density-1).toSeq
    def card: Int = factorial(locus.density)
    def permute(p: Array[Int],l:Locus ): Constraint =AllConstr(l)
    //def schedules=  HashSet.empty[Seq[Int]]++id.permutations
    override def pick()=Schedules(HashSet(id), locus)
    override def intersect(c: Constraint): Constraint = c
    override def verified(a: Seq[Int]): Boolean = true
  }

  /** @param b is an intrinsic permutation on 6 integers. */
   final case class Cycle(b:Seq[Int] , override val  locus:TT) extends Constraint(locus) {
    {
      require(b.length == locus.density)
    }

    /** Cycles could go both direction so we should multiply by two.  we consider just one, for "simplification" */
    def card: Int = b.length

    def permute(p: Array[Int], l: Locus): Constraint = Cycle(compose(p, compose(b, invert(p))).toArray[Int], l.asInstanceOf[TT])

    override def toString: String = "Cycle " + (orbitofZero.map(locus.les6sufx(_)).mkString("->"))
    override def schedules: HashSet[Seq[Int]] = {
      checkCycleLength()
      var result = HashSet.empty[Seq[Int]];
      var sched: Seq[Int] = orbitofZero;
      var possible = b
      for (i <- 0 to b.length - 1) {
        result = result + sched;
        sched = rotateLeft(sched)
      }
      result;
    }
    override def pick()=Schedules(HashSet(orbitofZero), locus)

    override def verified(a: Seq[Int]): Boolean = a == orbit(a(0), b)

    /**
     * @param init starting integer
     * @param perm permution
     * @return the orbit of $init
     */
    private def orbit(init: Int, perm: Seq[Int]): Seq[Int] = {
      var r = List[Int]();
      var c: Int = init;
      for (i <- 0 to 5) {
        r = c :: r; c = perm(c)
      };
      r.reverse}
    private lazy val orbitofZero =orbit(0,b)
    private def checkCycleLength()={
      /** c stores orbital,   */
      var c=Array.fill[Int](b.size)(0);var cycleLength=0
      var next =0;      val t:Array[Boolean]=Array(true,true,true,true, true,true)
      for(i<-0 to 5) { //intialisation of c needs to
        c(i)=b(next); t(next)=false;   next=b(next)
        if(!t(next)){if(cycleLength==0) cycleLength=i+1;
          next=t.indexOf(true) //explore the (possibly numerous) cycles.
        }
      }
      if(cycleLength!=6) throw new RuntimeException("for the moment we consider only cycles of length 6"+this )

    }
  }

  /** @param locus must be a transfer locus
   * @param b array of size 6 which maps  each   components of locus to a simplicial component of slocus,
   *  A partition constraint links a Tcc set of schedule to an Scc set of schedules
   *  Upon reduction from vE to E, the partition is E.proj = (0, 0, 1, 1, 2, 2)
   *   *  */
  final case class Partition( b:Seq[Int],slocus:S, override val locus:TT) extends Constraint(locus) {
    {
      require(b.size == 6, "a partition specifies a mapping for 6 components")
      require(!slocus.isInstanceOf[V], " partitionning towards  V does not constrain")    }
    override def toString: String ={
      val distrib=Array.fill[List[String]](slocus.density)(List())
      for (i<-0 to 5)   distrib(b(i))=locus.les6sufx(i)::distrib(b(i))
      "Partition "+ "targetlocus"+ slocus+" "+ distrib.map(_.mkString(",")).mkString("|")
    }
    def card: Int = slocus.card
    def permute(p: Array[Int], l: Locus): Partition = Partition(compose(invert(p), b), slocus, l.asInstanceOf[TT])
   override def schedules: HashSet[Seq[Int]] = if (slocus.isInstanceOf[V]) AllConstr(locus).schedules
    else {  val possible=slocus.partitionnables.get.toList
      HashSet.empty ++  possible.map(  compose(_, rectify).toSeq)     }
    override def verified(a: Seq[Int]): Boolean = slocus.partitionable(compose(a, b))
    /***
     * @param x transfer schedule that is partitionnable
     * @return projection on the Slocus of the partition
     */
      def project(x:Seq[Int])=slocus.scheduleProj (compose(x,  b)).toSeq
      def invProject(x:Seq[Int]) = {
        require(x.length== slocus.density )
         x.flatMap(bm1(_)).toSeq  }

    /** invert of b, there is several value for each int */
    private lazy val bm1={val toto= Array.fill[List[Int]](slocus.density)(List()); for (i<-5 to 0 by -1)  toto(b(i))=i::toto(b(i));toto}
    /**
     * let c=b o rectify, we have c(0)=c(1) =0, c(2)=c(3)=1 c(4)=c(5)=2
     */
      private lazy val rectify={
       val distrib2=Array.fill(6)(0)
        for (i<-0 to slocus.fanout -1)   for(j<- 0 to slocus.density -1)
            distrib2(i+ j * slocus.fanout) = bm1(j)(i)
        for(i<-0 to 5) require(b(distrib2(i))==i/slocus.fanout) //verification
        distrib2
      }
  }

  /**
   * @param p Partition linking and SCC to a SCC
   * @param c Constraints to be propagated
   * Wrapper to case class Propagate, handles the easy case p==c, and finds out the locus of the result
   * returns a constraint obtained by propagating $c or vice versa*/
  def propagate(p:Partition,c:Constraint ):Constraint= {
      if (c == p) {   AllConstr(p.slocus) }
    else c.locus match {
      case p.locus =>  PropagateToS(p, c)
      case p.slocus => PropagateToT(p, c)
    }
  }
  /** Build a new constraint out of two constraints, the first one being a partition
   *  @param p partition defines a binding between an s-locus and a t-locus,
   *  @param c constraints on a tlocus that must be propagated to the s-locus
   *  @ return  propagated constraints*/
  final  case class PropagateToS(p:Partition,c:Constraint) extends Constraint(p.slocus){
    {require(c.locus.isInstanceOf[TT])}
    def card: Int = c.card  //TODO a vérifier si on pourrait pas etre plus précis
    def permute(p: Array[Int], l: Locus): PropagateToS = throw new RuntimeException("Propagated constraint need not be permuted" )
    override def schedules: HashSet[Seq[Int]] = {
      val sch1= c.schedules.filter(p.verified(_))
      HashSet.empty ++ sch1 .map( p.project(_))  //we project only those schedules which can be partitionned
    }

    override def verified(a: Seq[Int]): Boolean = throw new RuntimeException("Difficult to implement, we should program the invert function" )
    /** We redefined intersect in order to force evaluation of schedules */
    override def intersect(c:Constraint):Constraint= {
      require(c.locus == this.locus, "intersected constraints have distinct loci")
      if (c.isInstanceOf[AllConstr] || (c == this)) this
      else if(c.card<card) c.intersect(this)
      else {//we have to replace PropagateTo by a set of schedules (schedulised form), in order to be able to check for verified.
        val schedulised=Schedules(schedules,locus)
        Schedules(HashSet.empty[Seq[Int]] ++ schedules.filter(schedulised.verified(_)),c.locus)
      }
    }
  }
  /** Build a new constraint out of two constraints, the first one being a partition
   *  @param p partition defines a binding between an s-locus and a t-locus,
   *  @param c constraints on a slocus that must be propagated to the other locus
   *  @ return  propagated constraints*/
  final case class PropagateToT(p:Partition,c:Constraint) extends Constraint(p.locus){
    {require(c.locus.isInstanceOf[S])}
    def card: Int = c.card  //TODO a vérifier si on pourrait pas etre plus précis
    def permute(p: Array[Int], l: Locus): Constraint =throw new RuntimeException("Propagated constraint need not be permuted" )
    override def schedules: HashSet[Seq[Int]] =  throw new RuntimeException("Difficult to implement, we should program the invert function" )
    //slocus.partitionnables.head.map(compose(_, b).toSeq)
    override def pick()= Constraint.Schedules(HashSet[Seq[Int]](p.invProject(c.pick().schedules.head)),locus)
    override def verified(a: Seq[Int]): Boolean = c.verified( p.project(a))
    /** We redefined intersect in order to force evaluation of verified */
    override def intersect(c:Constraint):Constraint= {
      require(c.locus == this.locus, "intersected constraint have distinct loci")
      if(c.isInstanceOf[AllConstr] || (c==this)) this
      else { val s= c.schedules
        val s2 =s.filter(verified(_))
        Schedules( HashSet.empty[Seq[Int]]++ s2,c.locus)
      }
    }
  }
  /** Constraint on transfer schedules */
  final case class BeginWithEither(b:List[Int] ,override val locus:Locus) extends Constraint(locus){
    def card: Int =b.length*factorial(5)
    def permute(p: Array[Int],l:Locus ): Constraint =BeginWithEither(b.map(p(_)),l)
    override def schedules: HashSet[Seq[Int]] ={
      val u=b.map((x: Int) =>   complement6(List(x)).toList.permutations.map(x :: _)).flatten.map(_.toArray )
      // immutable.HashSet.empty[Seq[Int]] ++ b.map((x: Int) =>   complement6(List(x)).toList.permutations.map(x :: _)).flatten
      var S= HashSet.empty[Seq[Int]]
      for (t<-u) S=S+t
      S
    }
    override def verified(a: Seq[Int]): Boolean = return b.contains(a(0))
  }

  final case class PartitionSucc( b:Array[Int],s:S,override val locus:Locus) extends Constraint(locus){
    def card: Int =s.cardSucc //it depends where we starts. Cycles could go both direction, so we should multiply by two.  we consider just one, for "simplification"
    def permute(p: Array[Int] ,l:Locus): Constraint =PartitionSucc(compose(invert(p),b) ,s,l )
    override  def schedules: HashSet[Seq[Int]] =null //TODO a completer
    override def propagateFrom(s2:Array[Int]):Option[Array[Int]]= s.propagateFrom(s2,b)
    override def verified(a: Seq[Int]): Boolean = false //TODO a completer
  }

  @scala.annotation.tailrec
  private def factorial(n: Int, accum:  Int = 1):  Int =   if (n == 0)   accum   else    factorial(n - 1, n * accum)
  private def complement6(l:List[Int]): HashSet[Int] =   HashSet(0,1,2,3,4,5,6)--l




}