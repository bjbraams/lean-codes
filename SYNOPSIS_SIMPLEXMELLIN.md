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
  $\{\mathop{\mathrm{Re}} b_i > -N\}$ the order $(|I| - 1)N$ suffices.

## The Mellin bridge

In simplicial polar coordinates $x = tu$, for a radial profile $\varphi$ and $\mathop{\mathrm{Re}}
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
at positive parameters in two coordinate systems instead of computing a Jacobian.
In particular, for every continuous boundary kernel and $\mathop{\mathrm{Re}}b_i>0$,
$$\prod_i\Gamma(b_i)T_b[g]
=\int \exp\Bigl(\sum_i b_i\log u_i(w)\Bigr)g(u(w))\,dw.$$
This allows monomial densities singular at the faces.

## Inversion and Plancherel

For $g$ continuous on $\Delta$, $c_i > 0$ and $b = c - 2\pi i\xi$: if
$\xi \mapsto \mathcal M[\varphi](\sum b)\prod\Gamma(b_i)T_b[g]$ is integrable on $\mathbb R^{I}$,
then at every interior point
$$g(u) = \varphi(1)^{-1}\int_{\mathbb R^{I}}\prod_iu_i^{-b_i}\;\mathcal M[\varphi]\Bigl(\sum_ib_i\Bigr)
\prod_i\Gamma(b_i)\,T_b[g]\,d\xi$$
(Fourier inversion in logarithmic coordinates; for $\varphi = e^{-t}$ the factor is $e$).
For the exponential profile, integrability is proved for **every kernel smooth near the
closed simplex**, including kernels nonzero on its faces. All derivatives of
$G(y) = g(e^y/\sum e^y)$ are bounded: differentiation of normalized exponential
coordinates is polynomial in their values, and the chain rule reduces the estimate to a
smooth function on the compact closed simplex. Thus the logarithmic kernel is the product
of a function of temperate growth and the Schwartz weight
$\exp\sum(c_i y_i-e^{y_i})$. The statements use `SmoothNearStdSimplex`, allowing the
smooth neighborhood to depend on the derivative order.

The sufficient condition now extends to finite regularity: if $g$ has $N$ continuous
derivatives near the closed simplex and $2N>|I|-1$, the inversion integral converges absolutely.
All logarithmic derivatives through order $N$ belong to $L^2$. The angular factor is constant
under diagonal translations, so a diagonal derivative of the logarithmic kernel falls entirely
on its Schwartz weight. Both the kernel and this diagonal derivative therefore lie in $H^N$.
A volume-preserving frequency shear and Cauchy–Schwarz separate the coordinate sum from the
transverse directions; the resulting dual weight belongs to $L^2$ under the stated
sufficient dimension inequality. This gives $L^1$ integrability of the full Fourier transform.
The same condition works for every smooth radial profile supported in a compact subinterval
of $(0,\infty)$ with $\varphi(1)\ne0$. No boundary vanishing is required.
This improves the earlier full-plane bounds $N>|I|$ and $2N>|I|$
(`SimplexMellin.IntrinsicInversion`).

There is now also absolute inversion from a single positive fixed-sum vertical hyperplane,
with the intrinsic sufficient count $2N>|I|-1$ (`SimplexMellin.LogRatioSchwartz`).
For a base point $\beta$ with positive real parts, set
$Q_\beta(w)=\exp(\sum_i\beta_i\log u_i(w))$ and extend intrinsic frequencies by
$\xi_{i_0}=-\sum_{j\ne i_0}\xi_j$. The weight $Q_\beta$ is Schwartz: the map
$w\mapsto\log u(w)$ has temperate growth and a continuous linear left inverse, so it
pulls back the double-exponential Schwartz weight to $Q_{\mathop{\mathrm{Re}}\beta}$,
up to the constant $e^{-1}$. The imaginary part supplies a temperate oscillatory multiplier.
The native transform at $b=\beta-2\pi i\xi$ is exactly the intrinsic Fourier transform
of $Q_\beta(w)g(u(w))$. Bounded angular derivatives and Sobolev Fourier integrability in
$|I|-1$ variables give the stated count. Smooth boundary kernels give Schwartz native
restrictions. No face vanishing is required. Endpoints and optimality are not asserted.

Plancherel gives
$$\int_{\mathbb R^{I}}\Bigl|\mathcal M[\varphi]\Bigl(\sum b\Bigr)\prod\Gamma(b_i)T_b[g]\Bigr|^2d\xi
= \mathcal M[|\varphi|^2]\Bigl(2\sum c_i\Bigr)\prod_i\Gamma(2c_i)\,T_{2c}[|g|^2].$$

This identity now holds for **every continuous kernel on the closed simplex**, with
$\varphi$ continuous on $(0,\infty)$ and convergent first and second radial Mellin
integrals at $\sum c_i$ and $2\sum c_i$. In particular it applies to the exponential
profile and to continuous profiles supported in a compact positive interval; neither
factor needs derivatives. The statements are
`integral_norm_sq_simplexMellinRadial_of_continuous` and
`integral_norm_sq_simplexMellin_of_continuous` in `SimplexMellin.L2`.
The transform is square integrable even when it is not absolutely integrable.
Finite-regularity pointwise inversion is
`regDirichletIntegral_inversion_exp_of_contDiffNear_of_card_sub_one_lt_two_mul` or
`regDirichletIntegral_inversion_radial_of_contDiffNear_of_card_sub_one_lt_two_mul`.
The earlier interfaces retain their statements as wrappers.

`simplexMellinRadialL2` defines the transform of any square-integrable logarithmic kernel
by Mathlib's Fourier isometry. It preserves distances and has an inverse in $L^2$, without
an $L^1$ assumption. On the continuous class above, it agrees almost everywhere with the
native Mellin integral.

`SimplexMellin.WeightedL2` now constructs the exponential-profile transform on the
**complete weighted simplex $L^2$ space**, including arbitrary measurable equivalence classes.
Its measure is
$$d\nu_c(u)=\frac{\Gamma(2\sum_i c_i)}{2^{2\sum_i c_i}}
  \prod_i u_i^{2c_i-1}\,du
=\frac{\prod_i\Gamma(2c_i)}{2^{2\sum_i c_i}}\,d\mathrm{Dirichlet}_{2c}(u).$$
`simplexMellinL2Isometry` is a complex linear isometry from $L^2(\nu_c)$ into
frequency $L^2(\mathbb R^I)$. Its image is closed, and `simplexMellinL2EquivRange`
gives the inverse onto that image. Schwartz kernels are dense, their transforms converge
in $L^2$ under weighted $L^2$ approximation, and the extension agrees almost everywhere
with the native integral for every continuous boundary kernel. This is an extension by
completion; it does not assert convergence of the native Mellin integral for arbitrary
measurable kernels. The index type must be nonempty; singleton coordinates are included.

## Boundary traces and meromorphic continuation

For a smooth boundary kernel, `simplexMomentContinuation` is the product of the entire
regularized transform and the coordinate Gamma factors. It agrees with the native integral
on $\mathop{\mathrm{Re}} b_i>0$, is analytic away from $b_i\in-\mathbb N$, and has a joint
analytic numerator divided by $\prod_{i\in J}(b_i+m_i)$ near an intersection of coordinate
pole hyperplanes. Thus there are at most simple poles in each coordinate.

Fixing the other parameters away from Gamma poles, the transverse residue is
$$\mathop{\mathrm{Res}}\nolimits_{b_i=-m} S_g(b)
=\frac{(-1)^m}{m!}\prod_{j\ne i}\Gamma(b_j)\,
  T_{(b_i=-m)}[g].$$
The face formula expresses the last factor as a binomial sum of transforms of tangential
boundary jets. At $m=0$ it is simply the unnormalized transform of the face trace.
The corresponding pole is removable exactly when that face transform vanishes.
Moreover, removability for **all positive complementary parameters** is equivalent to
$g|_{u_i=0}=0$; moments of the trace prove the reverse implication.
These face statements assume at least two coordinates.

There is also a native boundary limit, with the other parameters fixed in the convergence
region:
$$\lim_{\varepsilon\downarrow0}\varepsilon\,
 S_g(b_1,\ldots,\varepsilon,\ldots)
 = S_{g|_{u_i=0}}(b_{\widehat i}).$$
The continuation and residue results are in `SimplexMellin.Poles`. Pole statements concern
punctured germs, not the totalized Gamma values at the pole centers.

## Frequency decay

For a $C^N$ kernel near the closed simplex and fixed $c_i>0$,
$$\|\xi\|^N\left|\Gamma\Bigl(\sum b_i\Bigr)S_g(b)\right|\le C_N,
\qquad b=c-2\pi i\xi.$$
The logarithmic kernel has $N$ integrable derivatives, so this follows from Mathlib's Fourier
derivative estimates. On each hyperplane $\sum_i\xi_i=t$ the radial Gamma factor is a
nonzero constant. Hence
$$\|\xi\|^N|S_g(c-2\pi i\xi)|\le C_{N,t}\quad(\sum_i\xi_i=t).$$
Smooth boundary kernels have rapid decay on every such hyperplane, even when they are nonzero
on the faces (`SimplexMellin.BoundaryDecay`). Stationary-phase decay on same-sign rays, where
the total frequency grows, remains open.

## Paley–Wiener theory

* **Estimates.** If $g$ is continuous and vanishes where some $u_i < \delta$, the native integral
  $T_b[g]$ is already entire (a Pochhammer shift identity), $|S_g(b)| \le \|g\|_1\prod_i\max(1,
  \delta^{\mathop{\mathrm{Re}} b_i - 1})$ uniformly in $\mathop{\mathrm{Im}} b$, and with a smooth
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
  $|S(b)| \le C\prod_i\max(1, \delta^{\mathop{\mathrm{Re}} b_i - 1})$ for some $\delta > 0$, and (c)
  $S$ has Paley–Wiener bounds on one hyperplane $\sum b = s_0$. Sufficiency uses Carlson's theorem
  on lines transversal to the hyperplanes $\sum b = s_0 - n$. Condition (b) cannot be dropped:
  $\sin(2\pi(\sum b - s_0))S_g(b)$ satisfies (a) and vanishes on $\sum b = s_0$.
* **Lattice values.** For $g$ continuous, $S_g$ is holomorphic on $\mathop{\mathrm{Re}} b > 0$,
  bounded by $\|g\|_1$ on $\mathop{\mathrm{Re}} b \ge 1$, and determined there by the monomial
  moments $S_g(n + \mathbf 1)$, $n \in \mathbb N^{I}$ (Carlson's theorem in several variables).
  Nonnegative lattice data satisfying the sum-shift equation, shifted by $\mathbf 1$, have a
  unique continuation holomorphic on $\mathop{\mathrm{Re}} b > -1$ and bounded on
  $\mathop{\mathrm{Re}} b \ge 0$, given by the measure solving the moment problem; the shift is
  necessary (the point mass at a vertex has no such continuation unshifted).

## A master theorem with simplex structure

For $\Phi$ the function of Ramanujan's master theorem (built from $\varphi$) and $g$ a kernel
on the simplex, $\Phi(\sum x)g(x/\sum x) = \sum_k\varphi(k)(-\sum x)^kg(x/\sum x)$ near the origin,
and
$$\int_{\mathbb R_+^{I}}x^{b - 1}\Phi\Bigl(\sum x\Bigr)g\Bigl(\frac{x}{\sum x}\Bigr)dx =
\frac{\pi}{\sin(\pi\sum b)}\,\varphi\Bigl(-\sum b\Bigr)\prod_i\Gamma(b_i)\,T_b[g]$$
for $\mathop{\mathrm{Re}} b_i > 0$, $\mathop{\mathrm{Re}}\sum b < \delta$. For $g = 1$ this is the
Mellin transform of a function of $\sum x$ alone.
