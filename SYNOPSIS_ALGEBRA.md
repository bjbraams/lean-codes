# Synopsis: general algebra (`ToMathlib.Algebra`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library depends only on
Mathlib and extends Mathlib's `Submodule`, `LinearIndependent` and linear-map APIs.

## Saturation of submodules

Let $R$ be a commutative ring, $M$ an $R$-module, $S \subseteq R$ a multiplicative set and
$P \subseteq M$ a submodule. $P$ is *saturated* at $S$ if $r x \in P$ with $r \in S$ implies
$x \in P$; the predicate makes sense over any semiring. The *saturation* of $P$ is
$$P^{S} = \{\,x \in M : r x \in P \text{ for some } r \in S\,\},$$
realized as the inverse image of the $S$-torsion submodule of $M/P$. It is a submodule
containing $P$, and $P \mapsto P^S$ is a closure operator whose fixed points are the saturated
submodules. No regularity of the denominators is assumed: elements of $S$ may be zero divisors.
For $S = R^{0}$, the non-zero-divisors (over a domain: the nonzero scalars), $P$ is saturated
exactly when $M/P$ is torsion-free.

The saturation is also the inverse image of the localized submodule $S^{-1}P$ under the
localization map $M \to S^{-1}M$; this holds without injectivity of that map.

## Linear dependence in saturated spans

**Theorem.** Over a commutative ring, if $0 \notin S$, then more than $n$ vectors lying in the
saturation of a submodule spanned by $n$ vectors are linearly dependent; equivalently, a
finite family in such a saturated span admits a nontrivial linear relation once its size
exceeds the number of generators.

The ambient module need not be free, finitely generated or torsion-free. The proof transports
linear independence to the localization and uses the bound on the size of an independent
family in a finitely generated module over a commutative ring (strong rank condition).

This is the abstract form of the "clear the denominators" step in Carlson's Theorem 8.4-3: the
associated $R$-functions span a module of bounded rank over rational functions of the nodes,
and the theorem turns a rational dependence into one with polynomial coefficients
(see [the Carlson synopsis](SYNOPSIS_CARLSON.md)).

## Linear functionals over ordered fields

For linear functionals $f, g$ on a module over a linearly ordered field, the inclusion of
negative half-spaces $\{f < 0\} \subseteq \{g < 0\}$ (and its nonstrict variants) holds exactly
when $g$ is a nonnegative (respectively positive) multiple of $f$. No topology is involved.
