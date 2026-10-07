# Synopsis: Pochhammer symbols, Gamma, beta and incomplete Mellin transforms (`Pochhammer`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library depends only on
Mathlib and the pinned TauCeti library. It collects the scalar facts about rising factorials,
the Gamma and beta functions and one-variable Mellin-type integrals that the simplex and
Dirichlet theories need.

Notation: $(a)_n = a(a+1)\cdots(a+n-1)$ is the rising factorial (Mathlib's `ascPochhammer`).
All algebraic identities below are division-free, so they remain valid at zeros of the
symbols.

## Algebraic identities

* $(a)_{m+n} = (a)_m (a + m)_n$, the duplication $(a)_{2n} = 4^n (a/2)_n ((a+1)/2)_n$, and
  reflection identities such as $(-a - n + 1)_n = (-1)^n (a)_n$, together with split-and-reflect
  forms.
* **Chu–Vandermonde for rising factorials.** $(a + b)_n = \sum_k \binom nk (a)_k (b)_{n-k}$ over
  any commutative semiring, in evaluation and scalar-evaluation form, and the multinomial form
  $(\sum_i a_i)_n = \sum_{|m| = n}\binom nm\prod_i (a_i)_{m_i}$. (Mathlib records these for falling
  factorials.)
* $(a)_n/n!$ is the binomial-ring coefficient `Ring.multichoose a n` in characteristic zero.

## The Pochhammer polynomial transform

The linear map of $R[X]$ sending $X^n \mapsto (X)_n$, with its inverse expressed through
Stirling numbers of the second kind and the coefficient formula through Stirling numbers of the
first kind (the rising-factorial forms of DLMF 26.8.7, 26.8.10 and 26.8.39). The forward map
needs only a commutative semiring; the inverse, a commutative ring. Together they form a linear
equivalence preserving degree and leading coefficient, and the transform intertwines
multiplication by $X$ with the shift $X \mapsto X + 1$.

## Estimates

$|(a)_n| \le (|a|)_n$; $|(a)_n| \le n!\,(1 + |a|)^n$ and related factorial-geometric bounds;
a common bound for products of prescribed total degree; power lower bounds from a lower bound on
$\operatorname{Re} a$; $(a)_n \ne 0$ for $\operatorname{Re} a > 0$; comparison of $(1/2)_n$ with
factorials.

## Binomial series

$\sum_{n \ge 0}\frac{(a)_n}{n!} t^n = (1 - t)^{-a}$ for $|t| < 1$ and complex $a$, with
absolute convergence.

## Gamma identities

* The pole-free shift identity $\frac1{\Gamma(w)} = \frac{(w)_n}{\Gamma(w + n)}$ for all complex
  $w$, and $\Gamma(w + n) = (w)_n\Gamma(w)$ at every *Gamma-regular* $w$ (not a nonpositive
  integer); Gamma-regularity is stable under positive integer shifts and implies
  $(w)_n \ne 0$.
* Reciprocal Gamma gains factorial decay under integer shifts: $|1/\Gamma(s + n)|$ is bounded by
  a constant over $n!$ on $\operatorname{Re} s \ge 1$, and uniformly on compact sets after a
  common natural shift, also for shifts of a total parameter $\sum_i b_i$.
* **Simultaneous beta shifts.** The reciprocal beta normalization
  $\Gamma(a + b + 2n)/(\Gamma(a + n)\Gamma(b + n))$ has consecutive ratios tending to $4$, so
  damping by any ratio below $1/4$ gives an absolutely summable sequence; arbitrary complex
  $a, b$ are allowed.

## Beta integrals

$\int_0^c x^{a-1}(c - x)^{b-1}dx = c^{a+b-1}B(a, b)$ (complex kernels and their norms, real
set-integral and nonnegative forms) and $\int_0^1 x^m(1 - x)^n dx = m!\,n!/(m + n + 1)!$.

## Positive powers

The functions $x \mapsto x_+^{s}$ (principal power on $(0, \infty)$, zero on $(-\infty, 0]$) and
$x \mapsto x_+^{s-1}/\Gamma(s)$: continuity across zero for $\operatorname{Re} s > 0$
(respectively $> 1$), and differentiability with
$\frac{d}{dx}\frac{x_+^{s-1}}{\Gamma(s)} = \frac{x_+^{s-2}}{\Gamma(s-1)}$ for
$\operatorname{Re} s > 2$. These are the factors of the Dirichlet density in a chart and drive
tangential integration by parts on the simplex.

## Regularized incomplete Mellin transforms

For $K$ on $[0, a]$ and $\operatorname{Re}\alpha > 0$ put
$\mathcal M_\alpha K = \frac1{\Gamma(\alpha)}\int_0^a t^{\alpha-1}K(t)\,dt$. For $K \in C^N[0, a]$,
subtracting the Taylor polynomial of order $N - 1$ at $0$ gives the exact identity
$$\mathcal M_\alpha K = \sum_{k < N}\frac{K^{(k)}(0)}{k!}\frac{a^{\alpha + k}(\alpha)_k}{\Gamma(\alpha
+ k + 1)} + (\alpha)_N\,\mathcal M_{\alpha + N}(\text{Peano remainder}),$$
whose right side is holomorphic on $\operatorname{Re}\alpha > -N$. Hence
$\alpha \mapsto \mathcal M_\alpha K$ continues holomorphically from $\operatorname{Re}\alpha > 0$
to $\operatorname{Re}\alpha > -N$; multiplication of $K$ by $t^k$ acts as a Pochhammer shift.
This is the one-dimensional engine of the continuation of regularized Dirichlet integrals.
