package disjointset4

/** Immutable disjoint set data structure, as a list of pairs, mapping each
  * element to its representative */
final case class DisjointSet[A](val classes: List[(A, A)]):
  def repr(a: A): A =
    classes.find(p => p._1 == a) match
      case None         => a
      case Some((_, r)) => r

  def equiv(a: A, b: A): Boolean =
    repr(a) == repr(b)

  def union(a: A, b: A): DisjointSet[A] =
    val aRepr = repr(a)
    val bRepr = repr(b)
    val gPrime = ensureRepr(ensureRepr(classes, aRepr), bRepr)
    DisjointSet(gPrime.map(p => if p._2 == bRepr then (p._1, aRepr) else p))
  
def ensureRepr[A](classes: List[(A, A)], a: A): List[(A, A)] =
  classes.find(p => p._1 == a) match
    case None    => (a, a) :: classes
    case Some(_) => classes

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
