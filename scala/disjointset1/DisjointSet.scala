package disjointset1

import annotation.tailrec

/** Immutable implementation of a disjoint set data structure, based on
  * union-find without rank or path compression.
  */
final class DisjointSet[A](val parents: Map[A, A] = Map.empty[A, A]):
  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = find(a)
    val bRepr = find(b)
    DisjointSet(parents + (bRepr -> aRepr))

  @tailrec
  def find(a: A): A =
    val repr = parents.getOrElse(a, a)
    if repr == a then a else find(repr)

  def equiv(a: A, b: A): Boolean =
    find(a) == find(b)
