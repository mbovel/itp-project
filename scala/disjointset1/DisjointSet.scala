package disjointset1

import annotation.tailrec

/** Simple immutable implementation of a disjoint set data structure, without
  * rank or path compression.
  */
final class DisjointSet[A](parents: Map[A, A]):
  def union(a: A, b: A): Unit =
    val aRepr = find(a)
    val bRepr = find(b)
    DisjointSet(parents + (aRepr -> bRepr))

  @tailrec
  def find(a: A): A =
    val repr = parents.getOrElse(a, a)
    if repr == a then a else find(repr)

  def equiv(a: A, b: A): Boolean =
    find(a) == find(b)
