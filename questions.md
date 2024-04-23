# Questions

## Why do we need `repair`?

When adding a new equality `x <- y`, the `repair` procedure canonicalizes all nodes where `y` appears, for transforming `f(y)` to `f(x)`.

Why do we need to do it eagerly when adding an equality? Couldn't we do it lazily by canonicalizing operands when checking for an equivalence?

No, we can't. Here is an example showing why this doesn't work:

```
f(a) <- f(b)
f(c) <- f(d)
a
b <- c
d
```

Show that `f(a) = f(d)`.

There is no way to find it out if we haven't "repaired" the graph beforehand to derive that `f(b) = f(c)`.

## Why do we need to repair in BFS order?

