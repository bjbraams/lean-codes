# Synopsis: general analysis (`ToMathlib.Analysis`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. This library depends only on
Mathlib and the pinned TauCeti library. It collects real, complex, functional and harmonic
analysis that is independent of simplices, Dirichlet measures and Carlson's functions, stated
in the namespaces of the Mathlib APIs it extends. Target spaces are Banach spaces wherever the
argument allows it.

## Convexity and geometry

* **Shells and exteriors.** In a real normed space of dimension at least two, spherical shells
  and exteriors of closed balls (any centre and radii) are preconnected; nonempty annuli are
  path connected. Complex dimension at least two gives real dimension greater than one.
* **Convex-hull-admissible configurations.** If $D$ is path connected, the set of
  configurations $(z_i)_{i \in I}$ whose convex hull lies in $D$ is path connected, for an
  arbitrary (possibly empty or infinite) index set and any real topological vector space. No
  convexity of $D$ is required. This supplies the connected uniqueness domains for analytic
  continuation of Dirichlet averages.
* **Strict convexity tools.** Strict weighted Hölder interpolation for positive vectors unless
  they are proportional; strict decrease and strict log-convexity of $a + b/(x + k)$ for
  $a \ge 0$, $b > 0$; strict convexity of $x^{p}$, $p < 0$, on $(0, \infty)$; strict convexity
  and concavity of normalized sums $(x + y)/(\lambda + \mu)$ as convex combinations.
* **Mean weights.** For a function normalized along the diagonal, the derivatives at the
  all-one vector in coordinate directions sum to one.

## Calculus

* Iterated derivatives of a $C^n$ function of one variable on an open set behave as expected:
  $f^{(k)}$ is $C^{n-k}$, continuous for $k \le n$, with derivative $f^{(k+1)}$ for $k < n$.
* Second-order Taylor bounds for $C^2$ maps between real normed spaces (possibly infinite
  dimensional): the Peano little-$o$ remainder and a uniform local bound.
* **A minimum principle on the upper half-plane.** If $f$ is holomorphic on the upper
  half-plane, continuous on its closure, satisfies $\liminf \operatorname{Im} f \ge 0$ at infinity
  in the closed half-plane (for instance, a limit $L$ with $\operatorname{Im} L \ge 0$), and
  $\operatorname{Im} f \ge 0$ on the real axis, then $\operatorname{Im} f \ge 0$ throughout
  (maximum modulus applied to $e^{if}$ on large half-discs).

## Integration

* **Parametric integrals.** Fréchet differentiation under an integral over a compact set
  against a fixed integrable (possibly singular) scalar weight, when the kernel and its
  derivative are jointly continuous; parameters in any real or complex normed space.
* **Compact and half-line integrability.** An integrable scalar weight times a continuous
  Banach-valued function on a compact set is integrable (no countability assumptions); a
  continuous function vanishing beyond a radius is integrable on a half-line.
* **Reciprocal substitution.** $x = u^{-1}$ identifies integration on $(a, \infty)$ with
  integration against $u^{-2}\,du$ on $(0, a^{-1})$, for Bochner integrals and integrability.
* **Tails.** A family dominated on a half-line by one integrable function has uniformly
  vanishing tails, so finite-interval integrals converge uniformly; a power majorant $C x^{-p}$,
  $p > 1$, gives the tail bound $C R^{1-p}/(p-1)$.
* **Strict comparison.** An almost-everywhere strict inequality between integrable functions
  gives a strict inequality of integrals for a nonzero measure.
* **Two crossings.** A signed kernel that is positive between two points and negative outside,
  and annihilates constants and linear functions, has negative integral against every strictly
  convex function (the secant argument of Carlson–Tobey, 1968).
* **Products of singular powers.** For distinct real $x_i$, exponents $b_i < 1$ and
  $\sum b_i > 1$, $\sigma \mapsto \prod_i |\sigma - x_i|^{-b_i}$ is integrable on $\mathbb R$.
* **Coordinate splitting.** Lebesgue measure on $\mathbb R^{I}$ is the product of Lebesgue
  measure on one coordinate and on the others.
* **Endpoint deformation.** Let $\omega$ be holomorphic on a convex open $U \subseteq \mathbb C$,
  with values in a complex Banach space, and $\gamma_1, \gamma_2$ paths whose interiors lie in
  $U$; the endpoints may lie outside $U$, where $\omega$ may be singular, provided both path
  integrals exist. If the segments joining
  $\gamma_1(\varepsilon)$ and $\gamma_2(\varepsilon)$ near each end stay in $U$ and their lengths
  times a bound for $\omega$ on them tend to zero, the two path integrals are equal.

**Curve integrals** (Mathlib's curve integral of a one-form along a path, in real or complex
normed spaces):

* the fundamental theorem for exact forms with Banach-valued potentials along differentiable
  paths, integrability being automatic for continuous forms on $C^1$ paths;
* pullback of a one-form under a map differentiable along the path, as an identity of
  totalized curve integrals, and identification of finite-interval parametrizations;
* limits of finite integrals of exact forms are determined by the limits of the endpoint
  potential values (the endpoints need not converge), and integrable half-line pullbacks are
  limits of finite curve integrals;
* the estimate $\|\int_\gamma \omega\| \le \sup\|\omega\| \int\|\gamma'\|$, vanishing of
  integrals along families of connecting paths when form bound times speed tends to zero, and
  explicit rates for power decay faster than the reciprocal radius with at most linearly
  growing speeds.

**Cauchy boundary values (Plemelj).** For an integrable density on $\mathbb R$ with values in a
complex Banach space, continuous at $x_0$, the difference of its Cauchy integrals just above and
below $x_0$ tends to $-2\pi i$ times the density (approximate identity of the Poisson kernel). On a finite interval
with the regularized difference quotient integrable at an interior point (for instance when
the density is differentiable there), the separate upper and lower vertical limits exist and
equal the principal value $\mp \pi i$ times the density; the principal value is the limit of
symmetric real-axis truncations.

**Laplace asymptotics with complex phase.** For $\operatorname{Re} q \ge c > 0$,
$\|A(0)\| \le M$, $\|A(t) - A(0)\| \le L|t|$ and $\|q(t) - q(0)\| \le B|t|$ (measurable $A, q$),
$$\Bigl\|\sqrt n \int A(t)\, e^{-n t^2 q(t)}\, dt - A(0)\Bigl(\frac{\pi}{q(0)}\Bigr)^{1/2}\Bigr\|
\le \frac{L/c + M B/c^2}{\sqrt n},$$
with a finite-interval version ($L$ replaced by $L + M/\delta$), uniformity over parameter
families with common bounds, and the asymptotic equivalent when $A(0) \ne 0$.

## Spaces of holomorphic maps

* For $U$ open in a complex normed space and $F$ a Banach space, the holomorphic maps
  $U \to F$ form a subspace $\mathcal O(U, F)$ of the continuous maps with the compact-open
  topology; convergence there is locally uniform convergence, and evaluation and restriction
  are continuous. For $U \subseteq \mathbb C$, $\mathcal O(U, F)$ is closed and complete
  (Weierstrass).
* **Montel and Vitali.** A family bounded on compact sets is equicontinuous; with
  finite-dimensional target it has compact closure, so every sequence has a locally uniformly
  convergent subsequence; a sequence bounded on compact sets and convergent on a uniqueness set
  (or on a set with an accumulation point in a preconnected domain) converges locally
  uniformly. Versions for finite-dimensional complex sources take closedness of
  $\mathcal O(U, F)$ as a hypothesis.
* **Polynomial approximation.** Partial sums of a convergent power series are explicit
  polynomials converging locally uniformly on the disc of convergence; a function holomorphic on
  a disc, or an entire function, is a locally uniform limit of polynomials there.
* **Open mapping.** A surjective continuous linear map from a complete metrizable topological
  vector space to a Hausdorff metrizable Baire space (over a nontrivially normed field) is open;
  the metrics need not come from norms.

## Fourier, Mellin and Carlson-type theorems

* **The multivariable Mellin transform.** $\operatorname{mvMellin} f(s) =
  \int_{x > 0} \prod_i x_i^{s_i - 1} f(x)\, dx$ on the open orthant of $\mathbb R^{I}$, with its
  convergence predicate. The substitution $x = e^{y}$ turns it into an integral over
  $\mathbb R^{I}$, and on a vertical plane $\operatorname{Re} s = c$ into a Fourier transform;
  separable functions give products of one-variable Mellin transforms, and
  $\operatorname{mvMellin}(e^{-\sum x_i})(s) = \prod_i \Gamma(s_i)$.
* **A double-exponential Schwartz function.** For $c_i > 0$,
  $y \mapsto \exp\sum_i (c_i y_i - e^{y_i})$ is a Schwartz function on $\mathbb R^{I}$ (bounds
  from Faà di Bruno's formula); it is the Mellin weight of $e^{-\sum x_i}$ in logarithmic
  coordinates.
* **Paley–Wiener on $\mathbb R^n$.** If $F$ is entire on $\mathbb C^{I}$ with
  $\|F(\zeta)\| \le C_N (1 + \|\zeta\|)^{-N} \exp(2\pi\sum_i \rho_i |\operatorname{Im}\zeta_i|)$
  for all $N$, then the inverse Fourier transform $f$ of $F|_{\mathbb R^{I}}$ is smooth,
  supported in the box $|x_i| \le \rho_i$, and $\hat f = F$ on $\mathbb R^{I}$. Conversely the
  Fourier–Laplace transform of a smooth function supported in the box satisfies these bounds,
  and a continuous compactly supported function whose transform vanishes on $\mathbb R^{I}$ is
  zero. Horizontal lines of integration can be shifted for entire functions decaying like
  $(1 + |x|)^{-2}$ in a strip.
* **Carlson's theorem (F. Carlson, 1914).** A function with values in a complex normed space,
  holomorphic on the open right half-plane and continuous on its closure, of exponential type
  there and of type less than $\pi$ on the imaginary axis, vanishing at every natural number,
  vanishes identically; the constant $\pi$ is sharp. The proof reduces to scalar functions,
  divides $z f(z)$ by $\sin \pi z$, multiplies by a damping factor
  $e^{-\alpha(z + 1)\log(z + 1)}$ and applies Phragmén–Lindelöf. The several-variable version
  (by induction on the coordinates) gives uniqueness of continuations of data on $\mathbb N^{I}$.
* **Mellin–Barnes tools.** Cauchy's theorem on a vertical strip, for vector-valued functions
  holomorphic in the open strip, continuous on its closure, integrable on the boundary lines and
  tending to zero as $|\operatorname{Im} s| \to \infty$ uniformly in the strip; crossing a
  simple pole with residue $r$ changes a line integral by $2\pi r$; and the Mellin transform of
  an inverse Mellin transform.
* **Ramanujan's master theorem (Hardy's form).** Let $\varphi$ be holomorphic on
  $\operatorname{Re} z > -\delta$, $0 < \delta < 1$, with
  $|\varphi(z)| \le C e^{P \operatorname{Re} z + A|\operatorname{Im} z|}$, $A < \pi$. The
  Mellin–Barnes integral $F(x) = \frac{1}{2\pi i}\int_{(c)} \frac{\pi}{\sin \pi s}\varphi(-s)
  x^{-s}\, ds$, $0 < c < \delta$, equals $\sum_k \varphi(k)(-x)^k$ for $0 < x < e^{-P}$, and
  $\int_0^\infty x^{s-1} F(x)\,dx = \frac{\pi}{\sin \pi s}\varphi(-s)$ for
  $0 < \operatorname{Re} s < \delta$.

## Special functions

* **Gamma integral with a complex rate.** For $\operatorname{Re} a > 0$,
  $\operatorname{Re} w > 0$: $\int_0^\infty y^{a-1} e^{-yw}\, dy = w^{-a}\Gamma(a)$ with the
  principal power, together with kernel bounds, integrability and holomorphy in $w$.
* **Gamma bounds.** $|\Gamma(s)| \le \Gamma(\operatorname{Re} s)$ for
  $\operatorname{Re} s > 0$; $\Gamma(x) \le \Gamma(y)$ for $1 \le x \le y$, $2 \le y$;
  $x \mapsto \Gamma(x + r)/\Gamma(x)$ is nondecreasing for $r \ge 0$; $(x)_n \le (x + n)^n$;
  $|\Gamma(\tfrac12 + iy)|^2 = \pi/\cosh \pi y$ and $\Gamma(x)/|\Gamma(x + iy)| \le
  \sqrt{\cosh \pi y}$ for $x \ge \tfrac12$.
* **Bessel functions and ${}_0F_1$.** The regularized ${}_0F_1(c; z)$ is the sum of its
  series, bounded by $e^{|z|}/n!$ for $c = n + 1$, with termwise derivatives
  $\frac{d^n}{dz^n}\tilde F(c; z) = \tilde F(c + n; z)$, the contiguous relation, the formula
  $\frac{d^n}{dz^n}[z^{c-1}\tilde F(c; z)] = z^{c - n - 1}\tilde F(c - n; z)$ and the reflection
  $\tilde F(1 - n; z) = z^{n}\tilde F(1 + n; z)$, $n \in \mathbb Z$. Consequently
  $|J_m(x)| \le e^{|x|^2/4}(|x|/2)^{|m|}/|m|!$ for integer $m$. The modified Bessel function
  $I_a$ is defined, with $J_m(ix) = i^m I_m(x)$ and $I_{-m} = I_m$.
* **The Laplace transform of $(1 - \cos t)^n$.** $\sum_{j \le N}(-1)^j\binom Nj/(y + j) =
  N!/\prod_{j \le N}(y + j)$, and $\int_{2m\pi}^\infty e^{-xt}(1 - \cos t)^n dt =
  2^{-n}(2n)!\, e^{-2m\pi x}/(x(x^2 + 1)\cdots(x^2 + n^2))$.
* **Beta laws and concentration.** Real integrability, mass and mean of beta densities; the
  kernel $u^a(1 - u)^b$ ($a, b > 0$) increases up to $a/(a + b)$ and decreases afterwards;
  scaling both beta parameters by a common factor greater than one strictly decreases the
  expectation of every strictly convex function. For $0 < w < 1$ the ratio
  $(cw)_n/(c)_n$ is decreasing and log-convex in $c > 0$, strictly for $n \ge 2$.
* **Elementary power facts**: a power between two others is bounded by their sum; positive real
  bases to complex powers as exponentials; $\operatorname{Re}(1 - v) > 0$ for $|v| < 1$.

## Sequences satisfying a binomial theorem (Carlson 1970)

Carlson's class $A_k$ consists of sequences $(p_n)$ of functions on $R^k$ satisfying
$p_n(z + \lambda\mathbf 1) = \sum_m \binom nm \lambda^{n - m} p_m(z)$; for $k = 1$ these are
Appell sequences. Proved, without any polynomiality assumption unless stated: the
characterization by $\sum_i \partial_i p_n = n p_{n-1}$ (Theorem 1); closure under affine maps and
differentiation; the correspondence with data on a slice transverse to the diagonal (Theorem 2
and Corollary 2); Appell sequences correspond to sequences of constants, with the exponential
generating relation; the formal-series theorems (Theorem 3, its converse, Corollary 4); the
reindexing theorem (Theorem 4); the coefficient relation for polynomial sequences; the
composition (umbral) theorem (Theorem 5); and Carlson's Example 20. The binomial-theorem
algebra (closure properties, slice theorems, the one-variable correspondence and umbral
evaluation) holds for functions over any commutative ring; Theorem 1 and the composition theorem
hold over $\mathbb R$ or $\mathbb C$; the generating relations hold over any field of
characteristic zero.
