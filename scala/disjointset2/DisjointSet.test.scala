//> using test.dep org.scalameta::munit::1.0.0-M12

package disjointset2

class DisjointSetTests extends munit.FunSuite:
  test("transitivity1"):
    val ds = DisjointSet[String]().union("x", "y").union("y", "z")
    assert(ds.equiv("x", "y"))
    assert(ds.equiv("x", "z"))

    // Internals
    val l = List("x", "y", "z")
    assert(ds.equivalences == Map("x" -> l, "y" -> l, "z" -> l))
