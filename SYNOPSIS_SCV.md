# Synopsis: several complex variables (`SeveralComplexVariables`)

Part of the [mathematical synopsis](SYNOPSIS.md) of the project. The modules in
`SeveralComplexVariables/` are the part of the separate library `lean-SCV` that the Dirichlet and
Carlson developments use; each is an exact copy of the `lean-SCV` module of the same name. The
library depends on Mathlib, the pinned TauCeti library, `ToMathlib` and the one-variable
library ([CA](SYNOPSIS_CA.md)).

Finite coordinate spaces $\mathbb C^{I}$ carry the supremum norm, so balls are polydiscs. Target
spaces are complex Banach spaces. The central results are that holomorphy and analyticity
coincide in finite dimension and Hartogs' theorem on separate analyticity; the Dirichlet and
Carlson libraries use them constantly to pass from separate to joint analytic dependence on
Dirichlet parameters, exponents and nodes.

## Polydiscs and Reinhardt domains

Open and closed polydiscs with a radius in each coordinate, their distinguished boundary (the
torus), and the identification of equal-radius polydiscs with sup-norm balls and of the closure
of an open polydisc. *Reinhardt* sets (invariant under independent coordinate rotations),
*complete* Reinhardt sets (invariant under shrinking moduli) and *logarithmically convex* sets
(convex logarithmic image) are defined as properties of sets: complete Reinhardt sets are
Reinhardt, nonempty ones are path connected, interiors preserve completeness and logarithmic
convexity, logarithmic images of open sets are open, and complete Reinhardt sets are
characterized by containing the closed polydisc determined by each of their points.

## Cauchy theory on polydiscs

* **Iterated Cauchy formula.** For $f$ continuous on a closed polydisc and holomorphic in each
  variable separately, $f(z) = (2\pi i)^{-n}\int_{T} \frac{f(\zeta)}{\prod_j(\zeta_j - z_j)}d\zeta$
  for $z$ in the open polydisc, with separate radii; the kernel is integrable on the torus.
* **Cauchy series.** Multi-index Cauchy coefficients with their estimates, packaged as a formal
  multilinear series that represents the function on the whole open polydisc; on the diagonal
  the coefficients are the iterated Fréchet derivatives.
* **Osgood's theorem.** Joint continuity together with holomorphy in each coordinate gives
  joint analyticity on open subsets of $\mathbb C^{I}$.
* **Locally bounded separate holomorphy.** Coordinate Cauchy estimates turn a local bound on a
  separately holomorphic map into a joint local Lipschitz bound, hence continuity, hence
  analyticity.
* **Holomorphy equals analyticity.** A complex Fréchet-differentiable map on an open subset of a
  finite-dimensional complex normed space is analytic; the coordinate version is proved first
  and transported along a linear equivalence.

## Hartogs' theorem

**Theorem (Hartogs).** On an open subset of $\mathbb C^{I}$, a function analytic in each
coordinate separately is jointly analytic; no continuity or local boundedness is assumed.

The proof is by induction on the number of coordinates, splitting off one fibre variable:

* *Baire step:* a separately continuous function on a product with compact second factor is
  bounded on an open cylinder, and locally bounded Osgood gives joint analyticity there.
* *Submean estimates:* averaging over unit complex rotations turns the circle submean inequality
  for $|f|^p$, $p > 0$, into a volume submean inequality on balls.
* *Hartogs' lemma:* under a common upper bound, pointwise eventual bounds on positive powers of
  norms of holomorphic functions become uniform near each point (the exponents may vary, as
  needed for roots of Taylor coefficients).
* *Fibre extension:* a function jointly analytic on a thin cylinder and analytic on a larger
  disc in each fibre is locally bounded on the larger cylinder, since the fibre Taylor
  coefficients are holomorphic in the base and Hartogs' lemma makes their root bounds uniform.

## Derivatives and limits

* Coordinate derivatives defined through one-variable slices, identified with Fréchet
  derivatives on coordinate vectors; mixed derivatives indexed by lists or multi-indices, with
  permutation invariance; the complex Jacobian; formal partial derivatives of multivariate
  polynomials agree with analytic coordinate derivatives.
* Cauchy estimates for coordinate derivatives on polydiscs and slices.
* **Weierstrass convergence in several variables.** Locally uniform limits (and locally uniformly
  summable series) of analytic maps on finite-dimensional complex domains are analytic, and all
  mixed coordinate and iterated Fréchet derivatives converge locally uniformly.

## Holomorphic dependence of integrals

* **Dominated parameter integrals.** An integral depending on parameters in a
  finite-dimensional complex space is analytic if locally its pointwise Fréchet derivatives
  have an integrable uniform bound; a locally integrable bound on a holomorphic integrand
  already suffices (it bounds the derivatives on smaller balls by the Schwarz estimate).
* **Compact contour integrals.** A jointly holomorphic Banach-valued kernel integrated over a
  fixed compact parameter set against a fixed integrable weight gives an analytic function of
  the remaining variables; in particular circle integrals of jointly analytic kernels against
  continuous boundary data are analytic.
* **Uniqueness from positive reals.** Entire functions of finitely many variables (with values
  in any complex normed space) agreeing on the positive real orthant are equal; the one-variable
  statement from a real germ on a connected domain is included.
