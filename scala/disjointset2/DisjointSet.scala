package disjointset2

import annotation.tailrec

/** Immutable disjoint set data structure, with a flat representation. */
final class DisjointSet[A](val equivalences: Map[A, List[A]] = Map.empty[A, List[A]]):
  def repr(a: A): A =
    getEquivs(a).head

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

  private def getEquivs(a: A): List[A] =
    equivalences.getOrElse(a, List(a))

  def union(a: A, b: A): DisjointSet[A] =
    val newClass = getEquivs(a) ++ getEquivs(b)
    DisjointSet(equivalences ++ newClass.map(_ -> newClass))
