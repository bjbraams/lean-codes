# Mathematical synopsis, part III: Dirichlet averages and Carlson's functions

This is the third part of the mathematical synopsis; see [Part I](SYNOPSIS.md) for conventions
and the supporting libraries and [Part II](SYNOPSIS_SCV.md) for several complex variables. It
covers the two libraries `Dirichlet` and `Carlson`, which formalize B. C. Carlson's theory of
special functions as Dirichlet averages, following

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (chapters 5, 6 and 8);
* [Carl87] B. C. Carlson, *Dirichlet averages of $x^t\log x$*, SIAM J. Math. Anal. 18 (1987);
* [Carl69] B. C. Carlson, *A connection between elementary functions and higher transcendental
  functions*, SIAM J. Appl. Math. 17 (1969), for the contour representations.

Mathlib, at the pinned version, has the Gamma and Beta functions, the one-variable beta and
gamma probability distributions, and nothing else in this part: no Dirichlet distribution, no
multivariate beta function, no Dirichlet averages and none of Carlson's $R$, $L$, $S$ or $T$
functions. Everything below is new relative to Mathlib unless stated otherwise.

Throughout, $I$ is a finite index set (possibly empty), $E_I = \{u \in \mathbb R^I_{\ge 0} :
\sum_i u_i = 1\}$ is the standard simplex with the hyperplane measure $\sigma$ of Part I.5, and
$b \in \mathbb C^I$ are the *Dirichlet parameters*. The *convergence region* is
$\{b : \operatorname{Re} b_i > 0 \ \forall i\}$.

## III.1 Multivariate beta functions and the Dirichlet distribution

**The multivariate beta function.** $B(b) = \prod_i \Gamma(b_i)/\Gamma(\sum_i b_i)$, defined
for complex $b$ (with Mathlib's totalized $\Gamma$) and separately for positive real $b$;
symmetry, nonvanishing on the convergence region, and the recursion under integer translates
of parameters. Its solid-simplex integral representations (DLMF 5.14.1 and 5.14.2)
$$\int_{\Delta_n} \prod_{i=1}^n x_i^{b_i - 1}\Bigl(1 - \sum_i x_i\Bigr)^{b_0 - 1} dx = B(b_0, \dots, b_n),
\qquad \int_{\Delta_n} \prod_{i=1}^n x_i^{b_i - 1} dx = \frac{\prod_i \Gamma(b_i)}{\Gamma(1 + \sum_i b_i)},$$
are proved by slicing off one coordinate at a time; and, in the hyperplane picture,
$\int_{E_I} \prod_i u_i^{b_i - 1} d\sigma(u) = B(b)$ for real and complex parameters with
positive real parts, with the corresponding monomial and logarithmic-moment integrability
statements as majorants.

**The Dirichlet distribution.** For $b$ with all $b_i > 0$ the density $u \mapsto B(b)^{-1}
\prod_i u_i^{b_i - 1}$ on the interior of $E_I$ defines a probability measure
$\operatorname{Dir}(b)$ on $\mathbb R^I$ carried by the simplex, with the uniform distribution at
$b = 1$; permutation invariance; integration of vector-valued functions. Proved: the moment
formulas
$$\mathbb E\Bigl[\prod_i u_i^{m_i}\Bigr] = \frac{\prod_i (b_i)_{m_i}}{(\sum_i b_i)_{\sum_i m_i}},\qquad
\mathbb E[u_i] = \frac{b_i}{\Sigma},\qquad \operatorname{Var}(u_i) = \frac{b_i(\Sigma - b_i)}{\Sigma^2(\Sigma + 1)},\qquad
\operatorname{Cov}(u_i, u_j) = \frac{-b_i b_j}{\Sigma^2(\Sigma+1)}$$
with $\Sigma = \sum_i b_i$, also for real power products; the *aggregation theorem*: for a
surjection $f : I \to K$, the pushforward of $\operatorname{Dir}(b)$ under
$u \mapsto (\sum_{f(i) = k} u_i)_k$ is $\operatorname{Dir}((\sum_{f(i)=k} b_i)_k)$, proved by
identifying moments and using moment determination on the compact simplex; the *beta
marginal*: for $I = \{0, 1\}$ the first coordinate has Mathlib's beta distribution
$\operatorname{Beta}(b_0, b_1)$; and the *Gamma construction*: if $X_i$ are independent with
$X_i \sim \Gamma(b_i, r)$ for a common rate $r > 0$ and nonempty $I$, then $\sum_i X_i \sim
\Gamma(\sum_i b_i, r)$, the normalized vector $(X_i/\sum_j X_j)_i \sim \operatorname{Dir}(b)$,
and the sum is independent of the normalized vector. The last is obtained from the radial
integration formula of Part I.5 and uses no analytic continuation.

## III.2 Regularized complex Dirichlet integrals

**Densities and integrals.** For $b \in \mathbb C^I$ the *regularized Dirichlet density* is
$$\rho_b(u) = \mathbf 1_{E_I}(u)\prod_i \frac{u_i^{b_i - 1}}{\Gamma(b_i)},$$
entire in $b$ pointwise, and for a function $f$ on $\mathbb R^I$ the *regularized Dirichlet
integral* is $\mathcal D_b[f] = \int_{E_I} \rho_b(u) f(u)\, d\sigma(u)$; the *normalized*
integral is $\Gamma(\sum_i b_i)\,\mathcal D_b[f]$, which on positive real parameters is the
expectation under $\operatorname{Dir}(b)$ (the real–complex bridge). The density is integrable
on the convergence region and $\mathcal D_b[1] = 1/\Gamma(\sum_i b_i)$. On the convergence
region $b \mapsto \mathcal D_b[f]$ is analytic for bounded measurable $f$, and jointly analytic
in $b$ and in auxiliary holomorphic parameters of a kernel that is holomorphic on a complex
neighborhood of the simplex.

**Parameter shifts and integration by parts.** With $b + e_i$ the parameter vector raised by
one in coordinate $i$: $u_i \rho_b(u) = b_i\, \rho_{b + e_i}(u)$, hence
$\mathcal D_b[u_i f] = b_i\, \mathcal D_{b + e_i}[f]$ and, summing over the partition of unity
$\sum_i u_i = 1$, $\mathcal D_b[f] = \sum_i b_i\, \mathcal D_{b + e_i}[f]$. Tangential
integration by parts: for $f$ differentiable near the simplex and $\operatorname{Re} b_k > 2$,
$$\mathcal D_b\bigl[\partial_{e_j - e_i} f\bigr] = \mathcal D_{b - e_i}[f] - \mathcal D_{b - e_j}[f],$$
without boundary terms, proved through a chart density whose one-sided powers
$x_+^{a - 1}/\Gamma(a)$ have derivative $x_+^{a-2}/\Gamma(a - 1)$ including at zero.

**Polynomial transforms.** For a monomial, $\mathcal D_b[u^m] = \prod_i (b_i)_{m_i} /
\Gamma(\sum_i (b_i + m_i))$, which is entire in $b$; the transform of a multivariate
polynomial is the corresponding finite sum and is entire.

## III.3 The regularized Dirichlet transform

For a kernel $g$ on the simplex, an *entire regularized Dirichlet transform* is an entire
function $F$ on $\mathbb C^I$ agreeing with $b \mapsto \mathcal D_b[g]$ on the convergence
region. By the identity principle on the connected convergence region such an $F$ is unique
when it exists, is determined by its values at positive real parameters, does not see changes
of $g$ off the closed simplex, and is linear in $g$.

**Existence theorem (finite smoothness).** If $g$ is $C^{(|I| - 1)N}$ on a neighborhood of the
closed simplex, then $b \mapsto \mathcal D_b[g]$ continues analytically to the region
$\{b : \operatorname{Re} b_i > -N \ \forall i\}$. If $g$ is $C^\infty$ near the closed simplex
the continuation is entire. The proof iterates the parameter-shift identity backwards: on a
region where all but one coordinate have large real part the tangential integration by parts
expresses $\mathcal D_b[g]$ through integrals of tangential derivatives at shifted parameters,
and the pieces are glued by uniqueness. The parametric version keeps auxiliary holomorphic
parameters throughout, by complexifying the simplex coordinates so that tangential
differentiation commutes with holomorphic dependence, and yields joint analyticity in
parameters and auxiliaries.

**Structural laws of the continued transform.** Coordinate multiplication ($F_{u_i g}(b) = b_i
F_g(b + e_i)$), the partition-of-unity sum ($F_g(b) = \sum_i b_i F_g(b + e_i)$), tangential
differentiation ($F_{\partial_{e_j - e_i} g}(b) = F_g(b - e_i) - F_g(b - e_j)$, now for all
$b$), permutation of coordinates, monomial multiplication, and aggregation: if $g$ is a kernel
on the simplex of a quotient index set $K$ and $q : I \to K$ is surjective, then the transform
of $g \circ (\text{block sums})$ at $b$ is the transform of $g$ at the block-summed parameters.
Series: a uniformly summable family of kernels on the simplex can be transformed termwise on
the convergence region, and a locally uniformly summable family of continuations is a
continuation of the sum.

**Weighted Euler integrals.** The doubly Gamma-regularized Euler integral
$$\mathcal E_{a, a'}[f] = \frac{1}{\Gamma(a)\Gamma(a')}\int_0^1 u^{a - 1}(1 - u)^{a' - 1} f(u)\, du$$
is the two-coordinate Dirichlet transform; hence for a kernel $H(p, u)$ holomorphic in $(p, u)$
on a neighborhood of $U \times [0, 1]$ there is a function of $(a, a', p)$, entire in $(a, a')$
and holomorphic in $p \in U$, that equals $\mathcal E_{a, a'}[H(p, \cdot)]$ whenever
$\operatorname{Re} a, \operatorname{Re} a' > 0$. This is the engine behind the explicit
$R$-function of III.6.

## III.4 Carlson's Dirichlet averages

For nodes $z \in \mathbb C^I$ the *affine form* is $\langle u, z\rangle = \sum_i u_i z_i$, which
maps the simplex onto the convex hull of the nodes. The *regularized Dirichlet average* of a
scalar function $f$ is
$$\mathcal R_b(z; f) = \mathcal D_b\bigl[u \mapsto f(\langle u, z\rangle)\bigr],\qquad
\text{and } R(b; z; f) = \Gamma\bigl(\textstyle\sum_i b_i\bigr)\,\mathcal R_b(z; f)$$
is Carlson's average. On positive real parameters it is $\mathbb E_{\operatorname{Dir}(b)}
f(\langle u, z\rangle)$. Elementary properties: symmetry under simultaneous permutation of
parameters and nodes, the constant-node value $\mathcal R_b(c\mathbf 1; f) = f(c)/\Gamma(\sum b)$,
behaviour under affine substitutions of $f$, linearity, and termwise averaging of uniformly
dominated series (Carlson's 5.7-2).

**Analyticity in the nodes (Theorem 5.3-3).** If $f$ is holomorphic on a convex open $\Omega$
and $b$ is in the convergence region, then $z \mapsto \mathcal R_b(z; f)$ is holomorphic on
$\{z : z_i \in \Omega\ \forall i\}$, and jointly holomorphic in $(b, z)$ (Hartogs' theorem, Part
II.2, from separate analyticity plus local boundedness).

**Derivatives and the Euler–Poisson system.** Differentiation under the integral in a node:
$$\partial_{z_i}\mathcal R_b(z; f) = b_i\,\mathcal R_{b + e_i}(z; f'),$$
with iterated versions (Carlson's 5.3-2, 5.6-1(5)); the sum rule $\mathcal R_b(z; f) = \sum_i
b_i\,\mathcal R_{b + e_i}(z; f)$ (5.6-1(4)); the tangential relation from integration by parts;
and the Euler–Poisson partial differential equations: with
$$\mathcal P_{ij}[G] = (z_i - z_j)\,\partial_i\partial_j G + b_i\,\partial_j G - b_j\,\partial_i G,$$
one has $\mathcal P_{ij}[\mathcal R_b(\cdot; f)] = 0$ for all $i, j$, proved for large real parts
by tangential integration by parts and extended over the convergence region by analyticity.

**Divided differences (Section 5.5).** For $b = \mathbf 1$ and nodes $z_0, \dots, z_n$ the
unweighted average of $f^{(n)}$ is $n!$ times the divided difference $f[z_0, \dots, z_n]$
(Hermite–Genocchi, Part I.5), with symmetry, the recursion, and Carlson's Newton–Taylor
formula with integral remainder on convex domains: $f(x) = \sum_{k < p} f[z_0, \dots, z_{k}]
\prod_{l < k}(x - z_l) + f[z_0, \dots, z_{p-1}, x]\prod_{l < p}(x - z_l)$.

**Cauchy representation (Section 5.11).** For $f$ holomorphic on a disc $B(c, R)$ containing the
nodes and continuous on its closure, with $b$ in the convergence region and every $n$,
$$\mathcal R_b\bigl(z; f^{(n)}\bigr) = \frac{n!}{2\pi i}\oint_{|s - c| = R} \mathcal R_b\bigl(z; (s - \cdot)^{-n-1}\bigr) f(s)\, ds,$$
where the *regularized resolvent* $\mathcal R_b(z; (s - \cdot)^{-n-1})$ is analytic in $s$ off
the convex hull of the nodes and analytic in the nodes. The interchange of the circle and the
simplex integrals is justified by a product-integrability estimate.

## III.5 Analytic continuation of Dirichlet averages

**The continuation predicate.** For fixed $f$ and nodes $z$, a function $G$ on $\mathbb C^I$ is
*the regularized Carlson continuation* of $\mathcal R_\cdot(z; f)$ if it is entire and agrees
with $\mathcal R_b(z; f)$ on the convergence region; it is unique, recognized by agreement at
positive real parameters, and exists whenever $f$ is holomorphic on a convex open set
containing the nodes (III.3 applied to the composite kernel).

**Joint continuation (Theorem 6.3-6).** If $f$ is holomorphic on a convex open $\Omega$, there
is a function $G(b, z)$, holomorphic on $\mathbb C^I \times \Omega^I$, which for every
$z \in \Omega^I$ is the regularized continuation of $\mathcal R_\cdot(z; f)$; the same for the
averages of every derivative of $f$. The proof uses the parametric integration-by-parts
construction of III.3, not Carlson's contour argument. Every relation of III.4 persists on the
whole parameter space: the sum rule, the tangential relation
$(z_i - z_j)\,\mathcal R_{b}(z; f') = \mathcal R_{b - e_j}(z; f) - \mathcal R_{b - e_i}(z; f)$
in continued form, the *three-node relation*
$$(z_i - z_j)\, G(b - e_k) + (z_j - z_k)\, G(b - e_i) + (z_k - z_i)\, G(b - e_j) = 0,$$
the multiplication-by-argument rule and the associated (derivative) relations; also equal-node
aggregation and the deletion of a zero parameter.

**Domain-aware continuation.** On a possibly nonconvex open $D \subseteq \mathbb C$ the node
tuples whose convex hull lies in $D$ form an open set, connected if $D$ is; a *joint
continuation on $D$* is holomorphic on $\{z : z_i \in D\}$ and agrees with the native average
whenever the convex hull of the nodes lies in $D$. Such continuations are unique on connected
$D$, exist on convex $D$ and on the integral node domain of any open $D$, and glue along
increasing unions of connected domains. This isolates the gluing step of Carlson (1969),
Theorem 8; the local contour constructions on nonconvex Jordan domains are not formalized.

**Continued Cauchy representation and resolvent.** The regularized integer resolvent
$(b, z, s) \mapsto \mathcal R_b(z; (s - \cdot)^{-n-1})$ continues to a function jointly
holomorphic in all Dirichlet parameters, the nodes and the exterior point $s$, on the set
where $s$ is off the convex hull of the nodes (Carlson (1969), §5, Lemma 1, convex-hull part).
Consequently the circle version of Carlson (1969), Theorem 3 holds for all complex parameters:
the contour expression $\frac{n!}{2\pi i}\oint \tilde{\mathcal R}_b(z; s)\, f(s)\, ds$ is jointly
holomorphic in parameters and interior nodes even for merely continuous boundary data, and for
$f$ holomorphic in the disc it is the unique regularized continuation of the average of
$f^{(n)}$.

## III.6 Carlson's $R$-function

**$R$-polynomials (Sections 5.7, 6.2, 6.4–6.6).** For $n \in \mathbb N$ the regularized
polynomial $\mathcal R_n(b, z) = \mathcal D_b[\langle u, z\rangle^n]$ is entire in $b$ and
polynomial in $z$, with the explicit multinomial-Pochhammer form
$$\Gamma\Bigl(n + \textstyle\sum_i b_i\Bigr)\,\mathcal R_n(b, z) = \sum_{|m| = n}\binom{n}{m}\prod_i (b_i)_{m_i} z_i^{m_i}.$$
Proved: homogeneity, the diagonal value, termination when a parameter vanishes, the binomial
theorem $\mathcal R_n(b, z + a\mathbf 1) = \sum_m \binom nm a^{n - m}\mathcal R_m(b, z)$ for all
$b$, Carlson's linear transformation 6.5-3 (replacing $b_i$ by $1 - \sum_j b_j - n$ and $z_j$ by
$z_i - z_j$ introduces the sign $(-1)^n$), the generating function
$\sum_n N_n(b, z)\, t^n/n! = \prod_i (1 - t z_i)^{-b_i}$ for the Pochhammer numerators, node
derivatives, and the sharp estimate $|N_n(b, z)| \le (\sum_i |b_i|)_n \max_i |z_i|^n$ (6.2-7),
which preserves the full Taylor disc.

**Continued Taylor representation (Theorem 6.3-1).** If $f$ is holomorphic on $B(A, R)$ and
$\max_i |z_i - A| < R$, then $\sum_n \frac{f^{(n)}(A)}{n!}\,\mathcal R_n(b, z - A\mathbf 1)$
converges absolutely and locally uniformly in $(b, z)$ and is the regularized continuation of
$\mathcal R_\cdot(z; f)$, jointly analytic in parameters and nodes.

**Native integrals.** For a complex exponent $t$, $\mathcal R^{\rm int}_t(b, z) = \mathcal R_b(z;
w \mapsto w^t)$ with the principal power, on the node domain $\{z : \operatorname{Re} z_i > 0\}$
where the affine form stays in the right half-plane; at natural exponents it is the
$R$-polynomial; it is analytic in the nodes (Theorem 5.9-2), entire in the exponent (no
convergence restriction), jointly analytic in exponent and parameters, satisfies the two
associated relations 5.9-3/5.9-5, the tangential relation, positive homogeneity
$\mathcal R_t(b, \lambda z) = \lambda^t \mathcal R_t(b, z)$ for $\lambda > 0$ (and for
$\operatorname{Re}\lambda > 0$ on suitable nodes), and the Laplace representation and confluence
below.

**Single-integral representation (Theorem 6.8-1).** With $a + a' = \sum_i b_i$,
$\operatorname{Re} a, \operatorname{Re} a' > 0$ and right-half-plane nodes,
$$\Gamma(a)\Gamma(a')\,\mathcal R_{-a'}(b, z) = \int_0^1 u^{a - 1}(1 - u)^{a' - 1}\prod_i (1 - u + u z_i)^{-b_i}\, du
= \int_0^\infty s^{a - 1}\prod_i (z_i + s)^{-b_i}\, ds,$$
proved through the $R$-polynomial series near the all-one node vector and continuation. The
unit-interval integral is analytic in the nodes on the whole *product slit plane*
$\{z : z_i \notin (-\infty, 0]\ \forall i\}$, since the segment from $1$ to each node stays off
the cut, and jointly analytic in endpoint exponents, parameters and slit-plane nodes.

**The explicit $R$-function (new construction).** The regularized $R$-function
$\mathcal R_t(b, z) = R_t(b, z)/\Gamma(\sum_i b_i)$ is *defined* for every $t \in \mathbb C$,
$b \in \mathbb C^I$ and $z$ in the product slit plane by a finite recursion in the style of
Mathlib's `Complex.Gamma`. In the strip $\operatorname{Re} t < 0 < \operatorname{Re}(\sum_i b_i
+ t)$ it is the doubly regularized Euler integral
$$\mathcal R_t(b, z) = \frac{1}{\Gamma(-t)\Gamma(\sum_i b_i + t)}\int_0^1 u^{-t-1}(1 - u)^{\sum_i b_i + t - 1}\prod_i (1 - u + u z_i)^{-b_i}\, du;$$
outside the strip it is reached by the two denominator-free relations
$$\mathcal R_t(b, z) = \sum_i b_i\,\mathcal R_t(b + e_i, z),\qquad
\mathcal R_t(b, z) = \sum_i b_i z_i\,\mathcal R_{t - 1}(b + e_i, z),$$
the first raising the total parameter, the second lowering the exponent; the number of steps is
computed from $\operatorname{Re} t$ and $\operatorname{Re}(\sum_i b_i + t)$ and the value is
independent of it by the identity theorem in the joint variables $(t, b, z)$ on a connected
joint domain. Proved about this function:

* joint holomorphy in $(t, b, z)$ on $\mathbb C \times \mathbb C^I \times (\text{slit plane})^I$,
  and holomorphy under analytic substitutions of all three arguments;
* the two relations above and the third associated relation
  $\mathcal R_t(b, z) = (\sum_j b_j + t)\,\mathcal R_t(b + e_i, z) - t z_i\,\mathcal R_{t-1}(b + e_i, z)$
  hold everywhere, together with parameter lowering and the tangential relations
  $(z_i - z_j)\, t\,\mathcal R_{t-1}(b + e_i + e_j, z) = \mathcal R_t(b + e_i, z) - \mathcal R_t(b + e_j, z)$,
  all without dividing by $t$ or by $\sum b$;
* agreement with the native Dirichlet integral for parameters in the convergence region and
  right-half-plane nodes, at every exponent, and more generally whenever the convex hull of the
  nodes avoids the cut; hence $\mathcal R_t(b, \cdot)$ is the domain-aware continuation of the
  power kernel and has a continued circle-Cauchy representation;
* it is the unique entire continuation of the native integral in the parameters, and at
  natural exponents it is the $R$-polynomial;
* node derivatives $\partial_{z_i}\mathcal R_t(b, z) = t\, b_i\,\mathcal R_{t - 1}(b + e_i, z)$,
  the translation identity $\sum_i \partial_i \mathcal R_t = t\,\mathcal R_{t-1}$ with the
  corresponding Euler identity $\sum_i z_i\,\partial_i\mathcal R_t = t\,\mathcal R_t$, and the
  Euler–Poisson system $\mathcal P_{ij}[\mathcal R_t(b, \cdot)] = 0$ (6.4-2), all on the full
  slit domain;
* *Euler's transformation* (Theorem 6.8-3) on the full slit domain:
  $\mathcal R_t(b, z) = \prod_i z_i^{-b_i}\,\mathcal R_{-\sum_i b_i - t}(b, z^{-1})$;
* positive homogeneity, permutation symmetry, equal-node aggregation, and deletion of a zero
  parameter, for all exponents and parameters;
* the *homogeneity recurrence* (Relation 8.4-1): with $a + a' = \sum_i b_i$ and elementary
  symmetric polynomials $e_n(z)$,
  $$\sum_{n = 0}^{|I|} A_n(a, a', b, z)\, R_{-a-n}(b, z) = 0,\qquad
  A_n = \frac{(a)_n (a' - |I|)_{|I| - n}}{a\,(a' - |I|)}\Bigl((a + n) e_n(z) - \sum_i b_i z_i\, \partial_i e_n(z)\Bigr),$$
  first on the native strip by integration by parts in the positive-ray integral, then in a
  division-free polynomial form valid for all $t$, $b$ and slit-plane nodes, with coefficients
  that are genuine polynomials in $(a, b, z)$;
* Carlson's Lemma 8.4-2 and Theorem 8.4-3: the functions $\mathcal R_{t + k}(b, z)$, $k \in
  \mathbb Z$, span a module of rank at most $|I|$ over the rational functions of the nodes, and
  any $|I| + 1$ *associated* functions $\mathcal R_{t + k_j}(b + m_j, z)$ ($k_j \in \mathbb Z$,
  $m_j \in \mathbb Z^I$) satisfy a nontrivial linear relation with polynomial coefficients in
  the nodes, on the whole slit domain (coefficients chosen for fixed $t, b$);
* integer parameters (Section 8.5): a parameter $b_{i_0} = -N$ can be eliminated, $\mathcal R_t(b, z)
  = \sum_{j \le N} p_j(z_{i_0})\,\mathcal R_{t - j}(b', z')$ with polynomials $p_j$; the
  division-free lowering relation $(a - 1)(z_i - z_j)\,\mathcal R_{-a}(b, z) = \mathcal R_{1-a}(b - e_i, z)
  - \mathcal R_{1-a}(b - e_j, z)$; and the terminating case $t = -\sum_i b_i - N$ as an
  explicit rational expression;
* the *small-variable limit* (Section 8.3): with $a + a' = \sum b$ and positive real parts of
  $a$, $a'$ and $a' - b_i$, as $z_i \to 0$ through the right half-plane,
  $\mathcal R_{-a}(b, z) \to \frac{\Gamma(a' - b_i)}{\Gamma(a')}\,\mathcal R_{-a}(b^{\hat\imath}, z^{\hat\imath})$
  with the $i$-th coordinate deleted, plus the double-shift recurrence 8.3(5);
* *confluence* (Section 5.10): $R_n(b, \mathbf 1 + z/n) \to S(b, z)$ as $n \to \infty$, and the
  inverse *Laplace representation* (Theorem 5.10-2)
  $\mathcal R_{-a}(b, z) = \Gamma(a)^{-1}\int_0^\infty y^{a - 1}\,\mathcal S(b, -yz)\, dy$ for
  $\operatorname{Re} a > 0$;
* *integral evaluations* (Section 8.1): Euler-type integrals $\int_0^1 u^{a-1}(1 - u)^{a'-1}
  \prod_i ((1 - u)p_i + u q_i)^{-b_i} du$ along segments and rays with compatible logarithm
  branches are Gamma multiples of $R$-values, and the Mellin transform of the ray product
  $\prod_i (z_i + s)^{-b_i}$ is an $R$-function;
* two exponent–parameter identities in two variables: the Gauss-series symmetry
  $\mathcal R_t((u, v); (x, y)) = x^t\,\mathcal R_{-v}((u + v + t, -t); (1, y/x))$ and its
  slit-plane form;
* compactified *exterior-path kernels* (Carlson 1969, §5): the regularized exterior-path
  integrand for the integer resolvent is an Euler-type kernel whose Gamma regularization is an
  instance of III.3, so it admits joint analytic continuation given an admissible path and
  logarithm branches; the straight path recovers $\mathcal R$. Path independence and path
  construction on general Jordan domains are not formalized.

## III.7 Carlson's $L$-function

The 1987 paper studies the Dirichlet average of $w^t\log w$. Here the regularized
$L$-function is *defined* as the exponent derivative
$$\mathcal L_t(b, z) = \frac{\partial}{\partial t}\,\mathcal R_t(b, z),\qquad L_t(b, z) = \Gamma\Bigl(\textstyle\sum_i b_i\Bigr)\,\mathcal L_t(b, z),$$
so it inherits joint holomorphy in $(t, b, z)$ on the full domain of III.6 (Carlson (1987),
(2.1)). Proved: agreement with the native average $\mathcal R_b(z; w^t\log w)$ on the
convergence region for right-half-plane nodes and whenever the node hull avoids the cut, so
$\mathcal L$ is the unique entire continuation in the parameters; symmetry, aggregation,
positive scaling $\mathcal L_t(b, \lambda z) = \lambda^t(\mathcal L_t(b, z) + \log\lambda\,
\mathcal R_t(b, z))$, coincident-node and singleton values, and deletion of a zero parameter
((2.2)–(2.5)); Euler inversion (2.6), $\mathcal L_t(b, z) = -\prod_i z_i^{-b_i}\,
\mathcal L_{-\sum b - t}(b, z^{-1})$; the node derivative (3.5), $\partial_{z_i}\mathcal L_t(b, z)
= b_i\bigl(t\,\mathcal L_{t-1}(b + e_i, z) + \mathcal R_{t-1}(b + e_i, z)\bigr)$, the
translation and Euler differential identities (2.8)–(2.10) with their inhomogeneous $R$-terms,
and the full Euler–Poisson system (2.7) on the slit domain; the parameter-raising relations
(3.1), (3.2), (3.4) obtained by differentiating the $R$-relations, e.g.
$$\mathcal L_t(b, z) = \Bigl(\textstyle\sum_j b_j + t\Bigr)\mathcal L_t(b + e_i, z) - t z_i\,\mathcal L_{t-1}(b + e_i, z)
+ \mathcal R_t(b + e_i, z) - z_i\,\mathcal R_{t-1}(b + e_i, z),$$
the three-node relation (3.3), the backward shift (3.7) and the tangent relations, all
regularized and without exceptional parameter hyperplanes; the general principle that a
polynomial $R$-relation valid as the exponent varies differentiates to an inhomogeneous
$L$-relation whose correction coefficients are the formal derivatives of the coefficient
polynomials (a concrete instance of Theorem 3.1), applied to the homogeneity recurrence; the
$R$-polynomial expansion $\mathcal L_t(b, z) = \sum_n \ell_n(t)\,\mathcal R_n(b, z - \mathbf 1)$
for $\max_i |z_i - 1| < 1$ with $\ell_n(t) = \frac{1}{n!}\frac{d^n}{dw^n}(w^t \log w)|_{w = 1}$,
absolutely convergent for all parameters, and at $t = 0$ the logarithmic series (5.8) with
$\ell_n(0) = -(-1)^n/n$.

## III.8 The $S$- and $T$-functions

**$S$ (Sections 5.8, 6.3).** The average of the exponential, $\mathcal S(b, z) = \mathcal D_b[\exp
\langle u, z\rangle]$, with node derivatives $\partial_{z_i}\mathcal S(b, z) = b_i\,\mathcal S(b +
e_i, z)$ and Theorem 5.8-2 for iterated derivatives; the exponential series
$$\mathcal S(b, z) = \sum_{n \ge 0}\frac{\mathcal R_n(b, z)}{n!}$$
converges absolutely for all $b \in \mathbb C^I$ and all $z \in \mathbb C^I$, locally uniformly
in $(b, z)$, and defines the unique entire continuation of $\mathcal S$ in the parameters,
jointly entire in parameters and nodes with termwise mixed derivatives; symmetry, the
translation law $\mathcal S(b, z + a\mathbf 1) = e^a\,\mathcal S(b, z)$, the value at $z = 0$,
aggregation and zero-parameter deletion.

**$T$ (Section 5.12).** The average of $w \mapsto e^{1/w}$ on the node domain where the convex
hull of the nodes avoids zero (weaker than Carlson's common half-plane hypothesis); symmetry and
existence and uniqueness of the entire continuation in the parameters.

## III.9 Two-variable theory

For $I = \{0, 1\}$ with nodes $(x, y)$ and parameters $(b_0, b_1)$:

* the explicit $R$-polynomial numerator $\sum_k \binom nk (b_0)_k (b_1)_{n-k} x^k y^{n-k}$,
  its symmetry and parity (odd-degree equal-parameter polynomials vanish at opposite nodes),
  division-free node derivatives and contiguous relations valid at every parameter;
* elementary values: $\mathcal R_{-1}((1, 1); (x, y)) = \dfrac{\log y - \log x}{y - x}$ and
  $\mathcal L_{-1}((1, 1); (x, y)) = \dfrac{\log^2 x - \log^2 y}{2(x - y)}$ for
  $x \ne y$ in the right half-plane, with diagonal values, in undivided form including
  coincident nodes (Carlson's 8.5 and (8.8));
* the three-term recurrence on the full slit domain,
  $(u + v + t)\,\mathcal R_{t+1} - ((u + t)x + (v + t)y)\,\mathcal R_t + t x y\,\mathcal R_{t-1} = 0$
  for $\mathcal R_s = \mathcal R_s((u, v); (x, y))$, contiguous relations, the mixed node
  derivative, and the $L$-analogue (3.10) in factored and mixed-derivative forms;
* *inversion* on the full slit domain,
  $\mathcal R_t((u, v); (x, y)) = x^{t + v} y^{t + u}\,\mathcal R_{-u - v - t}((v, u); (x, y))$,
  with the $L$-version carrying the correction $\log x + \log y$;
* the *quadratic transformations* 6.9-3 and 6.10-1, first for native integrals by comparing
  $R$-polynomial coefficients about equal nodes,
  $$R_{2t}(\beta, \beta; x, y) = R_t\Bigl(\beta + t, \tfrac12 - t; \bigl(\tfrac{x + y}{2}\bigr)^2, xy\Bigr),\qquad
  R_t(\beta, \beta; x^2, y^2) = R_t\Bigl(2\beta + t, \tfrac12 - \beta - t; \bigl(\tfrac{x+y}{2}\bigr)^2, xy\Bigr),$$
  on branch-safe node domains where all integrals converge; then as entire identities in
  $(t, \beta)$ for the regularized functions, in which the ratio $\Gamma(\beta + \frac12)/\Gamma(2\beta)$
  produced by Legendre duplication is replaced by its entire extension
  $\gamma(\beta) = 2^{1 - 2\beta}\sqrt\pi/\Gamma(\beta)$, so that
  $\mathcal R_{2t}((\beta, \beta); (x, y)) = \gamma(\beta)\,\mathcal R_t((\beta + t, \tfrac12 - t); ((\tfrac{x+y}2)^2, xy))$
  holds at the Gamma poles as well; then with transformed nodes anywhere in the slit plane
  whenever $x, y$ have positive real parts. The double series of Section 6.10 is handled by
  absolute convergence;
* the *equal-parameter regularization*: the natural normalization of $R_t(\beta, \beta; x, y)$
  divides by $\Gamma(\beta + \frac12)$ rather than $\Gamma(2\beta)$; that continuation is
  constructed uniquely (via square roots and the second quadratic identity), both quadratic
  transformations identify it, and its exponent derivative gives the equal-parameter
  $L$-regularization with the differentiated quadratic transformations (6.4), (6.5) and, at
  $t = 0$, (6.8); the parameter-transfer identity (2.12) identifies the correction term from the
  moving parameters with the transformed $L$-term;
* the parameter–exponent interchange of III.6 and the two-node specializations of the $S$- and
  $T$-functions, including confluence of $R$ to $S$.

## III.10 What is not formalized

The module documentation records the open items explicitly, and they are not asserted anywhere:
Carlson's general rectifiable Jordan-curve representations and the nonconvex simply connected
extension (Carlson (1969), Theorems 4, 5 and 8), path independence of the exterior-path
kernels, Theorem 6.8-4's additional equal-parameter regularization for general $|I|$, the
removal of the positivity assumptions in the small-variable limit, the complete classification
of integer and half-integer parameter configurations by elementary functions, and the explicit
Pochhammer–digamma coefficients (5.3)–(5.7) of the $L$-series at general exponents.
