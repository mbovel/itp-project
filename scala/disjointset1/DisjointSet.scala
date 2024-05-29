package disjointset1

import annotation.tailrec

/** Immutable implementation of a disjoint set data structure, based on
  * union-find without rank or path compression. */
final class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A]):
  @tailrec def repr(a: A): A =
    val parent = parents.getOrElse(a, a)
    if parent == a then a else repr(parent)

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = repr(a)
    val bRepr = repr(b)
    DisjointSet(parents + (bRepr -> aRepr))
