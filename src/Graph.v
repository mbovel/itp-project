Require Import Coq.Lists.List.
Import List.
Import ListNotations.

Module Type GRAPH.
  Parameter A: Type.
  Parameter axioms : list (A * A).
  Parameter graph: Type.

  Parameter empty : graph.
  Parameter make: list (A * A) -> graph.
  Parameter is_eq : graph -> A -> A -> Prop.
  Parameter insert : (A * A) -> graph -> graph.
End GRAPH.