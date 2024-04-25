//> using test.dep org.scalameta::munit::1.0.0-M12

package disjointset3

class DisjointSetTests extends munit.FunSuite:
  test("transitivity1"):
    val ds =
    DisjointSet[String](Nil).union("x", "y").union("y", "z").union("a", "b")
    assert(ds.equiv("x", "y"))
    assert(ds.equiv("x", "z"))
    assert(ds.equiv("a", "b"))
    assert(!ds.equiv("a", "x"))
