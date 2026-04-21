package compiler

/** A ring defines the data types stored over the loci. */
sealed class Ring //j'appelle cela Ring parceque ca a une structure d'anneau avec or et and.

/** Boolean */
final case class B() extends Ring
/** Integer */
class I extends Ring //le type entier n'etends pas boolean, car OR,AND,XOR ne sont pas defini pour les entiers.
/** Unsigned Integer */
final case class UI() extends I
/** Signed Integer */
final case class SI() extends I

/** used for boolean function that have the same code for either UI or SI. */
//final case class UISI() extends I //both signe and unsigned

/** used for boolean function that have the same code for either UI or SI or Boolean??. */
//final case class UISIB() extends Ring
