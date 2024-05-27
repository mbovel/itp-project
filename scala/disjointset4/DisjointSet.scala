package disjointset4

/** Immutable disjoint set data structure, as a list of pairs, mapping each element to its representative */
final case class DisjointSet[A](val classes: List[(A, A)]):
  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = find(a)
    val bRepr = find(b)
    DisjointSet(
      ensureRepr(aRepr, ensureRepr(bRepr, classes)).map(p =>
        if p._2 == bRepr then (p._1, aRepr) else p
      )
    )

  def ensureRepr(a: A, classes: List[(A, A)]): List[(A, A)] =
    if (classes.find(p => p._1 == a).isDefined) classes
    else (a, a) :: classes

  def find(a: A): A = classes.find(p => p._1 == a).getOrElse((a, a))._2

  def equiv(a: A, b: A): Boolean =
    find(a) == find(b)

@main def Main() =
  val ds =
    DisjointSet[String](Nil).union("x", "y").union("y", "z").union("a", "b")
  println(f"x eq y: ${ds.equiv("x", "y")}")
  println(f"x eq y: ${ds.equiv("x", "z")}")
  println(f"a eq b: ${ds.equiv("a", "b")}")
  println(f"a eq x: ${ds.equiv("a", "x")}")

  // Internals
  val l = List("x", "y", "z")
  println(ds)
  assert(ds.equiv("x", "y"))
