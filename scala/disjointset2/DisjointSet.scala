package disjointset2

import annotation.tailrec

/** Immutable disjoint set data structure, with a flat representation. */
final class DisjointSet[A](val equivalences: Map[A, List[A]] =
  Map.empty[A, List[A]]):
  def union(a: A, b: A): DisjointSet[A] =
    val newClass = getEquivs(a) ++ getEquivs(b)
    DisjointSet(equivalences ++ newClass.map(_ -> newClass))

  def find(a: A): A =
    getEquivs(a).head

  private def getEquivs(a: A): List[A] =
    equivalences.getOrElse(a, List(a))

  def equiv(a: A, b: A): Boolean =
    find(a) == find(b)
