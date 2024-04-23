//> using test.dep org.scalameta::munit::1.0.0-M12

package disjointset1

class DisjointSetTests extends munit.FunSuite:
  test("transitivity1"):
    val ds = DisjointSet(Map("x" -> "y", "y" -> "z"))
    assert(ds.equiv("x", "y"))
    assert(ds.equiv("x", "z"))
