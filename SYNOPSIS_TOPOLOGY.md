# Synopsis: general topology (`ToMathlib.Topology`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library depends only on
Mathlib and the pinned TauCeti library, and extends the corresponding Mathlib APIs. Its results
are elementary in statement but are used at decisive points in the complex analysis and in the
Schwarz–Christoffel theory.

## Gluing with locally constant differences

Let $X$ be simply connected and locally path connected, $(U_i)$ an open cover, and $f_i$
functions on $U_i$ with values in a group $G$ (not necessarily commutative, with no topology)
such that every quotient $f_i^{-1} f_j$ is locally constant on $U_i \cap U_j$. Then there is a
global function $F$ such that each $F^{-1} f_i$ is locally constant on $U_i$; after
normalization at a base point $F$ is unique, and uniqueness needs only preconnectedness. The
additive version and versions for functions defined only on the members of the cover are
included.

The proof builds the covering space whose transition functions are the given quotients and
uses simple connectedness to trivialize it. In the complex-analysis library this is the
topological core of the existence of global primitives and logarithms on simply connected
domains.

## Coverings and injectivity

* A continuous open map that is injective near every point is a local homeomorphism.
* A proper local homeomorphism from a Hausdorff space is a covering map: fibres are compact
  and discrete, hence finite, and proper maps are closed.
* A covering map from a path-connected space onto a simply connected space is injective
  (lifting of homotopic paths).

Combined, a proper local homeomorphism from a path-connected space onto a simply connected
space is a homeomorphism onto its image. This is the topological argument behind the
one-to-one property of the Schwarz–Christoffel map in Carlson's Theorem 8.2-1.

## Frontiers, exits and connectedness

* An open preconnected set is a connected component of the complement of its frontier.
* In a preconnected space, a closed set $K$ has preconnected complement as soon as some open
  neighbourhood $O \supseteq K$ has $O \setminus K$ preconnected.
* A continuous function on a real interval that starts in an open set and ends outside it has
  a first exit time, at which its value lies on the frontier; the same for paths.

## Baire-category bounds

* A pointwise bounded-above family of lower semicontinuous real functions on a Baire space is
  uniformly bounded above on a nonempty open subset of every nonempty open set; the points
  with a local uniform bound form a dense open set.
* A separately continuous map on a product $X \times K$, with $K$ compact and values in a
  seminormed group, is uniformly bounded on some nonempty open cylinder $V \times K$.

The second statement is the initial step in the proof of Hartogs' theorem on separate
analyticity (see [several complex variables](SYNOPSIS_SCV.md)).

## Finite products of pseudometric spaces

With the supremum distance on a finite product, changing one coordinate of a point of a
closed ball within the corresponding coordinate ball stays in the ball, and coordinatewise
distance bounds telescope to a joint bound by changing one coordinate at a time.
