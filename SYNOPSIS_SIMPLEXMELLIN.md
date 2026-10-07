# Synopsis: the simplex Mellin transform (`SimplexMellin`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library develops the
regularized Dirichlet transform as a transform in its own right. Its definition, entire
continuation and structural laws are in [Dirichlet](SYNOPSIS_DIRICHLET.md), shared with
Carlson's averages; `SimplexMellin` and [Carlson](SYNOPSIS_CARLSON.md) are independent of each
other. The generic inputs (multivariable Mellin transform, Paley–Wiener, Carlson's theorem,
Mellin–Barnes integrals, Ramanujan's master theorem) are in [ToMathlib](SYNOPSIS_ANALYSIS.md),
and simplicial polar coordinates and the moment problem in
[StdSimplexMeasure](SYNOPSIS_STDSIMPLEX.md).

For a kernel $g$ on the standard simplex $\Delta = E_I$,
$$T_b[g] = \int_\Delta\prod_i\frac{u_i^{b_i - 1}}{\Gamma(b_i)}\,g(u)\,du,\qquad
S_g(b) = \int_\Delta\prod_iu_i^{b_i-1}g(u)\,du = \prod_i\Gamma(b_i)\,T_b[g].$$
$T$ is entire in $b$ for kernels smooth near $\Delta$; $S_g$ is the *simplex Mellin transform*.

## Faces, uniqueness and estimates

* **Face formulas.** At $b_i = 0$ the continued transform is the transform, with the remaining
  parameters, of the restriction of $g$ to the face $u_i = 0$ (Carlson's omission of a vanishing
  parameter, for general kernels); at $b_i = -m$, for any $j \ne i$,
  $$T_b[g] = \sum_{a + l = m}\binom ma\,T^{\text{face}}_{b' - le_j}\bigl[(\partial^a_{e_j - e_i}g)|_{u_i = 0}\bigr].$$
  The proof lets the exponent of a regularized incomplete Mellin transform tend to zero and
  iterates tangential integration by parts, valid for all complex parameters.
* **Uniqueness.** The values $T_{m + \mathbf 1}[g]$, $m \in \mathbb N^{I}$, are the monomial
  moments of $g$ up to factorials, so a continuous kernel is determined on $\Delta$ by its
  transform at the positive integer parameters.
* **Estimate.** On every compact set of parameters, $|T_b[g]| \le C\,A$ whenever the derivatives
  of $g$ up to a fixed order are bounded by $A$ on the simplex; on
  $\{\operatorname{Re} b_i > -N\}$ the order $(|I| - 1)N$ suffices.

## The Mellin bridge

In simplicial polar coordinates $x = tu$, for a radial profile $\varphi$ and $\operatorname{Re}
b_i > 0$,
$$\int_{\mathbb R_{>0}^{I}}\prod_ix_i^{b_i - 1}\,\varphi\Bigl(\sum_ix_i\Bigr)\,g\Bigl(\frac{x}{\sum_i x_i}\Bigr)dx
= \mathcal M[\varphi]\Bigl(\sum_ib_i\Bigr)\prod_i\Gamma(b_i)\,T_b[g],$$
an identity of Bochner integrals with no integrability assumption; for $\varphi(t) = e^{-t}$ the
radial factor is $\Gamma(\sum_ib_i)$. Thus $T_b$ is the angular part of the multivariable Mellin
transform with the Gamma factors divided out. For smooth $g$ and $\mathcal M[\varphi]$ entire,
the multivariable Mellin transform is $\prod_i\Gamma(b_i)$ times an entire function, with poles
only at $b_i \in -\mathbb N$.

**Log-ratio coordinates.** Relative to $i_0$, $u(w) = e^{\tilde w}/\sum e^{\tilde w}$
($\tilde w_{i_0} = 0$) parametrizes the open simplex, and
$\int_\Delta f = \int\prod_iu_i(w)\,f(u(w))\,dw$ with
$\prod_iu_i(w) = e^{\sum w}Z(w)^{-|I|}$, $Z(w) = 1 + \sum_je^{w_j}$; the proof evaluates the bridge
at $b = \mathbf 1$ in two coordinate systems instead of computing a Jacobian.

## Inversion and Plancherel

For $g$ continuous on $\Delta$, $c_i > 0$ and $b = c - 2\pi i\xi$: if
$\xi \mapsto \mathcal M[\varphi](\sum b)\prod\Gamma(b_i)T_b[g]$ is integrable on $\mathbb R^{I}$,
then at every interior point
$$g(u) = \varphi(1)^{-1}\int_{\mathbb R^{I}}\prod_iu_i^{-b_i}\;\mathcal M[\varphi]\Bigl(\sum_ib_i\Bigr)
\prod_i\Gamma(b_i)\,T_b[g]\,d\xi$$
(Fourier inversion in logarithmic coordinates; for $\varphi = e^{-t}$ the factor is $e$). The
integrability hypothesis holds, and the formula is unconditional, when $g$ is smooth and
vanishes near the faces and either $\varphi$ is smooth with compact support in $(0, \infty)$ or
$\varphi = e^{-t}$ (the function inverted is then the product of the Schwartz function
$\exp\sum(c_iy_i - e^{y_i})$ and a function of temperate growth). Plancherel:
$$\int_{\mathbb R^{I}}\Bigl|\mathcal M[\varphi]\Bigl(\sum b\Bigr)\prod\Gamma(b_i)T_b[g]\Bigr|^2d\xi
= \mathcal M[|\varphi|^2]\Bigl(2\sum c_i\Bigr)\prod_i\Gamma(2c_i)\,T_{2c}[|g|^2].$$

## Paley–Wiener theory

* **Estimates.** If $g$ is continuous and vanishes where some $u_i < \delta$, the native integral
  $T_b[g]$ is already entire (a Pochhammer shift identity), $|S_g(b)| \le \|g\|_1\prod_i\max(1,
  \delta^{\operatorname{Re} b_i - 1})$ uniformly in $\operatorname{Im} b$, and with a smooth
  compactly supported radial factor $\mathcal M[\varphi](\sum b)S_g(b)$ is a Schwartz function on
  vertical planes.
* **Hyperplanes.** On $\sum_ib_i = s$, $S_g(b) = \int e^{\langle b', w\rangle}Z(w)^{-s}g(u(w))\,dw$,
  $b' = (b_j)_{j \ne i_0}$: a Fourier–Laplace transform in $|I| - 1$ variables. Every entire
  function of $b'$ with Paley–Wiener bounds is the restriction of $S_g$ for a kernel continuous
  on the simplex, smooth near it and vanishing near its faces; conversely smooth kernels vanishing
  near the faces give Paley–Wiener restrictions; and the restriction to one hyperplane determines
  a continuous kernel vanishing near the faces.
* **The image.** An entire function $S$ is $S_g$ for a kernel smooth near $\Delta$ and vanishing
  near its faces if and only if (a) $S(b) = \sum_iS(b + e_i)$, (b)
  $|S(b)| \le C\prod_i\max(1, \delta^{\operatorname{Re} b_i - 1})$ for some $\delta > 0$, and (c)
  $S$ has Paley–Wiener bounds on one hyperplane $\sum b = s_0$. Sufficiency uses Carlson's theorem
  on lines transversal to the hyperplanes $\sum b = s_0 - n$. Condition (b) cannot be dropped:
  $\sin(2\pi(\sum b - s_0))S_g(b)$ satisfies (a) and vanishes on $\sum b = s_0$.
* **Lattice values.** For $g$ continuous, $S_g$ is holomorphic on $\operatorname{Re} b > 0$,
  bounded by $\|g\|_1$ on $\operatorname{Re} b \ge 1$, and determined there by the monomial
  moments $S_g(n + \mathbf 1)$, $n \in \mathbb N^{I}$ (Carlson's theorem in several variables).
  Nonnegative lattice data satisfying the sum-shift equation, shifted by $\mathbf 1$, have a
  unique continuation holomorphic on $\operatorname{Re} b > -1$ and bounded on
  $\operatorname{Re} b \ge 0$, given by the measure solving the moment problem; the shift is
  necessary (the point mass at a vertex has no such continuation unshifted).

## A master theorem with simplex structure

For $\Phi$ the function of Ramanujan's master theorem (built from $\varphi$) and $g$ a kernel
on the simplex, $\Phi(\sum x)g(x/\sum x) = \sum_k\varphi(k)(-\sum x)^kg(x/\sum x)$ near the origin,
and
$$\int_{\mathbb R_+^{I}}x^{b - 1}\Phi\Bigl(\sum x\Bigr)g\Bigl(\frac{x}{\sum x}\Bigr)dx =
\frac{\pi}{\sin(\pi\sum b)}\,\varphi\Bigl(-\sum b\Bigr)\prod_i\Gamma(b_i)\,T_b[g]$$
for $\operatorname{Re} b_i > 0$, $\operatorname{Re}\sum b < \delta$. For $g = 1$ this is the
Mellin transform of a function of $\sum x$ alone.
