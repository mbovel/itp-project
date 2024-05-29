package disjointset3

import annotation.tailrec

/** Immutable disjoint set data structure, with a flat representation. */
final case class DisjointSet[A](val classes: List[List[A]]):
  def union(a: A, b: A): DisjointSet[A] =
    val aClass = findEqClass(a).getOrElse(List(a))
    val bClass = findEqClass(b).getOrElse(List(b))
    if aClass == bClass then DisjointSet(classes)
    else
      val newClasses = (aClass ++ bClass) :: classes.filterNot(c => c == aClass || c == bClass)
      DisjointSet(newClasses)

  def repr(a: A): A =
    findEqClass(a).getOrElse(List(a)).head

  private def findEqClass(a: A): Option[List[A]] =
    classes.find(_.contains(a))

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

@main def Main() =
  val ds = DisjointSet[String](Nil).union("x", "y").union("y", "z").union("a", "b")
  println(f"x eq y: ${ds.equiv("x", "y")}")
  println(f"x eq z: ${ds.equiv("x", "z")}")
  println(f"a eq b: ${ds.equiv("a", "b")}")
  println(f"a eq x: ${ds.equiv("a", "x")}")

  // Internals
  val l = List("x", "y", "z")
  println(ds)
  assert(ds.equiv("x", "y"))
