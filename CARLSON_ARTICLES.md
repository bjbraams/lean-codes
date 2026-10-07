# Carlson's articles in relation to *Special Functions of Applied Mathematics* (1977)

Review date: 30 September 2026.

## Scope and conventions

There are **38 journal articles** by Carlson or Carlson and co-authors in
`Carlson/References`, published between 1965 and 2011. All 38 are reviewed below,
in chronological order, covering theoretical papers, expositions, integral
tables, and a numerical-software article. The separate chapter PDFs, the
replacement page 93, and the closing material of the book are not counted as
articles. Supplements containing computer
programs are treated as part of their respective articles.

The comparison is with the mathematical treatment in the locally available book
chapters 2–9, including their notes and exercises and the solutions and bibliography
in the closing material. Section and equation numbers below refer to the **book**
unless explicitly identified as belonging to an article. This is a review of the
mathematics and its relation to the book, not an assertion that the corresponding
results have already been formalized in Lean.

Three distinctions recur:

- **Substantial incorporation:** the book develops the article's central ideas,
  sometimes with different proofs or notation.
- **Selective incorporation:** the book uses particular results or applications,
  while the article contains a more extensive theory.
- **Later extension or new direction:** a post-1977 paper develops the book's
  machinery further, or applies it to a subject not systematically treated there.

For orientation, the most relevant parts of the book are:

| Book location | Relevant content |
| --- | --- |
| [Chapter 2](Carlson/References/Carlson1977Ch2.pdf), especially §2.6 | Hypergeometric series; arithmetic, geometric, and logarithmic means |
| [Chapter 3](Carlson/References/Carlson1977Ch3.pdf) and [Chapter 4](Carlson/References/Carlson1977Ch4.pdf), especially §4.4 | Gamma and beta functions; Dirichlet measure |
| [Chapter 5](Carlson/References/Carlson1977Ch5.pdf) | Dirichlet averages, Euler–Poisson equations, divided differences, associated functions, the exponential average \(S\), the power average \(R\), Laplace and Cauchy representations |
| [Chapter 6](Carlson/References/Carlson1977Ch6.pdf) | \(R\)-polynomials, analytic continuation, quadratic transformations, mean iterations, and Gegenbauer's product formula |
| [Chapter 7](Carlson/References/Carlson1977Ch7.pdf) | Jacobi and related polynomials, addition theorems, expansions, and asymptotics |
| [Chapter 8](Carlson/References/Carlson1977Ch8.pdf) | Hypergeometric integration, conformal mapping and elliptic functions, limiting cases, and reduction through associated functions |
| [Chapter 9](Carlson/References/Carlson1977Ch9.pdf) | Symmetric elliptic integrals, reduction formulas, applications, Landen and duplication transformations, addition, and quartic reduction |
| [Closing material](Carlson/References/Carlson1977ClosingMaterial.pdf) | Exercise solutions, bibliography, and index |

Two notation cautions are useful. Carlson's \(R_t\) is the Dirichlet average of
\(x^t\); a conventional hypergeometric parameter \(a\) often corresponds to
\(t=-a\). Also, the book's elliptic basis uses \(R_F,R_G,R_H\), whereas later
computational papers favor \(R_F,R_D,R_J\), with the elementary auxiliary
\(R_C\). In the later notation,
\(R_D(x,y,z)=R_J(x,y,z,z)\) and \(R_C(x,y)=R_F(x,y,y)\).
The later second- and third-kind formulas must therefore be compared with the
book through their definitions, rather than by matching subscripts alone.

## Articles published before or during 1977

### 1. Carlson (1965), *A Hypergeometric Mean Value*

**Source:** B. C. Carlson, *Proceedings of the American Mathematical Society*
**16**, 759–766.
[Article PDF](Carlson/References/Carlson1965HypergeometricMeanValue-AMS.ProcAMS16.pdf).

**Content.** The paper introduces the hypergeometric mean
\(M(t,c;x,w)=R_t(cw;x)^{1/t}\), with its logarithmic limiting definition at
\(t=0\), for positive nodes and positive normalized weights. The extra parameter
\(c\) controls the concentration of the Dirichlet measure. As \(c\to0^+\), the
mean tends to the usual weighted power mean of order \(t\); as \(c\to\infty\),
it tends to the weighted arithmetic mean. The paper proves continuity and
monotonicity in the nodes and in the order, identifies special cases and limiting
values, and establishes analogues of Minkowski, Hölder, and
Beckenbach–Dresher inequalities. Euler's transformation gives useful inversion
relations. The arithmetic and geometric means occur as particular members of
the family.

**Relation to the book.** This is an early source for the interpretation of
\(R\)-functions as means. Chapters 4–5 supply the general Dirichlet-average
framework, and §6.2 discusses hypergeometric means alongside \(R\)-polynomials;
the Chapter 6 notes explicitly refer to this paper. The book incorporates the
construction and selected consequences, but the paper is the more focused source
for the two-parameter family and its collection of mean inequalities.

### 2. Carlson (1966), *Some Inequalities for Hypergeometric Functions*

**Source:** B. C. Carlson, *Proceedings of the American Mathematical Society*
**17**, 32–39.
[Article PDF](Carlson/References/Carlson1966SomeInequalitiesHypergeometricFunctions-AMS.ProcAMS17.pdf).

**Content.** The central problem is bounding hypergeometric means and
\(R\)-functions by simpler weighted means. The inequalities depend on the
position of the exponent relative to distinguished parameter values; Euler's
transformation transfers bounds between different ranges. Thus the paper gives
a coordinated family of upper and lower bounds, rather than a single universal
inequality. Applications include elementary logarithmic and inverse circular
functions, Gauss and confluent hypergeometric functions, Appell's \(F_1\), and
integrals arising in applications. Particularly concrete examples are bounds
for the surface area and electrostatic capacity of ellipsoids, including
higher-dimensional analogues.

**Relation to the book.** The Chapter 6 notes cite this paper in connection with
hypergeometric means. Chapter 9, especially §9.4, returns to the ellipsoid
applications and explicitly draws on the inequality work. Chapters 5 and 8
provide the integral representations that make the bounds possible. The book
therefore incorporates both the underlying viewpoint and some applications;
the paper remains a concentrated source for the parameter-dependent inequality
catalogue and its wider range of examples.

### 3. Carlson and Tobey (1968), *A Property of the Hypergeometric Mean Value*

**Source:** B. C. Carlson and M. D. Tobey, *Proceedings of the American
Mathematical Society* **19**, 255–262.
[Article PDF](Carlson/References/CarlsonTobey1968PropertyHypergeometricMeanValue-AMS.ProcAMS19.pdf).

**Content.** This paper studies dependence on the concentration parameter \(c\)
in the mean introduced in 1965. For nonconstant positive nodes,
\(M(t,c;x,w)\) increases strictly with \(c\) when \(t<1\), and decreases strictly
when \(t>1\); at \(t=1\) it is the arithmetic mean and is independent of \(c\).
The proof develops beta-integral comparisons and an aggregation argument that
passes from two nodes to more nodes. Further results describe convexity,
concavity, and log-convexity in \(c\) of the underlying power average.

The distinction between proved results and conjecture matters here: log-convexity
for negative order and for positive integral orders at least two is established,
but log-convexity for **every real order greater than one is only conjectured**
in this paper.

**Relation to the book.** The paper is explicitly included among the sources for
hypergeometric means in the Chapter 6 notes. It refines the mean interpretation
of §6.2, rather than introducing a different special-function family. Its main
added value over the book's treatment is the detailed dependence on concentration
and the associated shape properties.

### 4. Carlson (1969), *A Connection between Elementary Functions and Higher Transcendental Functions*

**Source:** B. C. Carlson, *SIAM Journal on Applied Mathematics* **17**, 116–148.
[Article PDF](Carlson/References/Carlson1969ConnectionBetweenElementaryFunctionsHigherTranscendentalFunctions-SIAM.JApplMath17.pdf).

**Content.** This is a foundational exposition of the Dirichlet-average method.
An ordinary function \(f\) is replaced by its average over convex combinations
of several nodes, with Dirichlet weights. Powers produce hypergeometric
functions, and exponentials produce confluent functions. The paper develops
differentiation formulas, Euler–Poisson equations, parameter relations,
polynomial analogues of monomials, series representations, and contour
representations based on an averaged Cauchy kernel.

Its final section is particularly significant: it studies analytic continuation
by deforming contours and tracking function elements. In a multiply connected
domain, continuation around a hole can make a collision of nodes singular even
when the initial branch was regular there. The paper therefore distinguishes
continuation away from the collision diagonals from the stronger situation in
a simply connected domain. This is substantive complex analysis, not merely a
formal replacement of ordinary powers by \(R\)-functions.

**Formalization status.** The simply connected case of Theorem 8 is proved in
`Dirichlet.Average.SimplyConnected`, for any number of nodes, by a convex chart from the
Riemann mapping theorem, the two-node merging identity (4.21) and induction, rather than by
Carlson's contour-adapted branches (Theorems 4–5). The multiply connected and
Riemann-surface cases are not formalized.

**Relation to the book.** Much of Chapter 5 is a systematic textbook development
of this program, notably §§5.2–5.7 and §5.11; Chapter 6 develops the polynomial
and analytic-continuation aspects further. This is a case of **substantial
incorporation**, but the article retains value for its detailed contour and
continuation arguments and its explicit discussion of branch obstructions. It
is consequently a natural companion to the book for the project's existing
work on analytic Dirichlet averages.

### 5. Carlson (1970), *Some Extensions of Lardner's Relations between 0F3 and Bessel Functions*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **1**, 232–242.
[Article PDF](Carlson/References/Carlson1970SomeExtensionsLardnerRelations0⁢F3BesselFunctions-SIAM.JMatrixAnal01.pdf).

The journal is *Mathematical Analysis*, despite the `JMatrixAnal` abbreviation
in the local filename.

**Content.** Separating a generalized hypergeometric series into its even and
odd terms expresses a \({}_pF_q\) function through two
\({}_{2p}F_{2q+1}\) functions with paired parameters. Conversely, these restricted
higher-order functions can be reduced to lower-order ones. The first examples
relate \({}_0F_3\) to Bessel and Kelvin functions; others involve generalized
Fresnel integrals and special values of \({}_4F_3\). The paper then extends the
decomposition to Meijer's \(G\)-function and to solutions of the corresponding
differential equations, including some cases with logarithmic solutions.
Pairing parameters whose differences are half odd integers gives a practical
reducibility criterion. Applications identify beam-vibration and shell-deformation
problems whose fourth-order equations reduce to Bessel or confluent
hypergeometric equations. The discussion records an exceptional case when
the lower-order equation already has an even or odd solution.

**Relation to the book.** The elementary series mechanism is incorporated in
**Exercise 2.4-8**, on pp. 28–29, which treats Kelvin functions and the even/odd
decomposition of \({}_0F_1\); the closing solutions explicitly recommend
separating the terms. The book also supplies the Pochhammer duplication identity
and the generalized hypergeometric notation. The systematic Meijer-\(G\)
decomposition, differential-equation reduction, and elasticity applications
go substantially beyond this selected textbook example.

### 6. Carlson (1970), *Hidden Symmetries of Special Functions*

**Source:** B. C. Carlson, *SIAM Review* **12**, 332–345.
[Article PDF](Carlson/References/Carlson1970HiddenSymmetriesSpecialFunctions-SIAM.Review12.pdf).

**Content.** This expository paper explains how familiar transformations become
simple permutations when special functions are written as homogeneous functions
of several variables. Examples include a Gauss hypergeometric transformation,
Kummer's transformation, Appell's \(F_1\), and changes of elliptic modulus.
The common explanation is the simultaneous permutation symmetry of the nodes
and parameters of a Dirichlet average. The paper argues for choosing standard
elliptic integrals that display this symmetry explicitly.

The computational application is substantial: it generalizes Borchardt's
two-variable iteration to a symmetric three-variable iteration built from
arithmetic and geometric means. For admissible nonnegative starting values,
the variables approach a common limit whose reciprocal is
\(R_F(x_0^2,y_0^2,z_0^2)\). The proof uses Jacobian bisection formulas, and the
paper explains the relation to duplication and the ultimately linear rate of
convergence. Equal starting variables recover the elementary Borchardt case.

**Relation to the book.** The Chapter 5 notes explicitly cite this paper for
the symmetry viewpoint. Its ideas permeate the definitions of \(R\) and \(S\),
the transformations in Chapter 6, and the choice of elliptic standards in
Chapter 9. Sections 6.10 and 9.6 develop the iterative consequences. This is
substantially incorporated material, presented here as a particularly clear
explanation of why the book's notation and averaging method are useful. It
also anticipates the Jacobian permutation theory developed in the 2004 paper.

### 7. Carlson (1971), *Algorithms Involving Arithmetic and Geometric Means*

**Source:** B. C. Carlson, *The American Mathematical Monthly* **78**, 496–505.
[Article PDF](Carlson/References/Carlson1971AlgorithmsInvolvingArithmeticGeometricMeans-MAA.AmerMathMonthly78.pdf).

**Content.** The paper classifies iterations whose two new coordinates are
chosen from the arithmetic mean \(A=(x+y)/2\), the geometric mean
\(G=\sqrt{xy}\), and \(\sqrt{Ax},\sqrt{Ay}\). There are sixteen ordered choices,
of which twelve are nontrivial. For positive initial coordinates, all converge
to a common limit. An integral invariant identifies that limit in each case
as a power of an \(R\)-function, usually an elliptic integral or an elementary
degeneration. Gauss's arithmetic–geometric mean and Borchardt's iteration are
particular cases. The paper compares their convergence and explains why Gauss's
case is exceptional in having quadratic convergence within this family.

A lemniscatic case gives an iterative way to measure arcs of Bernoulli's
lemniscate and a proof of Fagnano's duplication theorem. The historical
discussion connects these algorithms with the development of elliptic
functions, but the core result is the complete table of invariant means for
the specified set of iterations.

**Relation to the book.** Section 6.10 treats the Gauss and Borchardt algorithms
through quadratic transformations, and its chapter notes explicitly refer to
this paper for the larger class. Chapter 9 develops elliptic evaluation and
duplication. The book contains the most important individual examples; the
article adds their unified classification and the fuller lemniscatic discussion.
It is distinct from the 1971 paper on mixed subset means.

### 8. Carlson (1971), *Appell Functions and Multiple Averages*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **2**, 420–430.
[Article PDF](Carlson/References/Carlson1971AppellFunctionsMultipleAverages-SIAM.JMathAnal02.pdf).

**Content.** The paper extends a single Dirichlet average to multiple averages.
A central construction averages \(f(u^T Z v)\), where the nodes form a matrix
and independent Dirichlet measures are attached to its rows and columns.
Permuting rows or columns, or transposing the matrix together with its
parameters, produces transformation identities. Appell's \(F_1,F_2,F_3\) and
several Lauricella families fit into this framework. A second construction
averages a function of several arguments separately. Series, differential
equations, integral representations, and Cauchy-type formulas develop these
constructions beyond a list of identifications with named functions.

**Relation to the book.** The book concentrates on single averages. It explicitly
points to this article in §6.11 to explain the double-average origin of a
bilateral generating relation used for Gegenbauer's product formula. It also
contains individual Appell-function examples and exercises. The systematic
matrix formulation and the broader multiple-average theory are not developed
there to the same extent.

**Qualification from a later paper.** The 1976 article below expressly states
that the unrestricted continuation in the matrix entries asserted on p. 421 of
this paper had not been established. That claim should not be imported as an
unqualified theorem.

### 9. Carlson, Meany, and Nelson (1971), *Mixed Arithmetic and Geometric Means*

**Source:** B. C. Carlson, R. K. Meany, and S. A. Nelson, *Pacific Journal of
Mathematics* **38**, 343–349.
[Article PDF](Carlson/References/CarlsonMeanyNelson1971MixedArithmeticGeometricMeans-PacificJMath38.pdf).

**Content.** Starting with nonnegative numbers, the authors take arithmetic or
geometric means over all subsets of a fixed size, and then apply the other mean
to the resulting collection. The geometric mean of the subset arithmetic means
increases with subset size; the arithmetic mean of the subset geometric means
decreases. A further comparison relates the two constructions when their subset
sizes have sum greater than the number of original variables. The paper gives
more general mixed-power-mean inequalities, treats equality, and compares the
results with the classical inequalities for elementary symmetric means.

It also proposes a stronger comparison with elementary symmetric means as a
**conjecture**, so not every inequality discussed is proved.

**Relation to the book.** The closest background is §2.6 on means, §6.2 on
symmetric polynomials and hypergeometric means, and the inequalities used in
ellipsoid applications. This finite combinatorial theory is nevertheless a
distinct subject and is not systematically developed in the book. In particular,
these mixed means should not be confused with the arithmetic–geometric mean
iteration used for elliptic integrals in §6.10.

### 10. Carlson (1972), *The Logarithmic Mean*

**Source:** B. C. Carlson, *The American Mathematical Monthly* **79**, 615–618.
[Article PDF](Carlson/References/Carlson1972LogarithmicMean-MAA.AmMathMonthly79.pdf).

**Content.** This short paper studies
\(L(x,y)=(x-y)/(\log x-\log y)\), extended continuously by \(L(x,x)=x\), for
positive arguments. It places the logarithmic mean between the geometric and
arithmetic means, sharpens the comparison, and introduces a parameterized family
of bounds. Repeated square roots lead to product and iterative descriptions,
with accelerated approximations obtained by suitable combinations of upper and
lower quantities. The paper connects elementary inequalities with practical
evaluation rather than treating the mean only as a named expression.

**Relation to the book.** The most direct connection is **§2.6**, not only the
later hypergeometric chapters. That section proves geometric/logarithmic/arithmetic
comparisons, quantitative bounds, and a complex-variable analogue; its notes
cite this paper. The book uses those estimates in its discussion of Stirling's
formula and the gamma function. Section 6.10 supplies a related broader setting
for iterative evaluation of elementary functions, but the separate Carlson
1972 paper cited there on computing logarithms and arctangents is a different
article. This paper's central inequality theme is substantially incorporated;
its particular mean constructions and computational presentation remain useful
supplements.

### 11. Rognlie and Carlson (1973), *Averaged Integral Transforms*

**Source:** D. M. Rognlie and B. C. Carlson, *SIAM Journal on Mathematical
Analysis* **4**, 393–407.
[Article PDF](Carlson/References/RognlieCarlson1973AveragedIntegralTransforms-SIAM.JMathAnal04.pdf).

**Content.** The authors ask when averaging a transform in its transform
variable is equivalent to replacing its kernel by a Dirichlet average. They
treat Fourier, Laplace, and Stieltjes transforms, and inverse Fourier, Laplace,
and Mellin transforms. One approach interchanges the transform integral with
the simplex integral; another uses contour representations and can work under
different, weaker hypotheses. Examples evaluate transforms involving products
of confluent hypergeometric functions and integrals involving elliptic and
other hypergeometric functions.

The operational discussion is especially useful. Linearity, simultaneous
translation of the nodes, and certain differentiation identities survive
averaging. Multiplication and the usual convolution-to-product rule generally
do not: the average of a product is not the product of the averages. The paper
gives an appropriate convolution identity with an averaged kernel instead.

**Relation to the book.** Section 5.10 develops the Laplace-transform relation
between the \(S\)- and \(R\)-functions and explicitly points to this paper for
averaged transforms; §5.11 supplies the contour machinery. The book contains a
central example of the theory, while the article is the source for the broader
transform catalogue, precise interchange hypotheses, and operational
limitations.

### 12. Carlson (1974), *Analytic Continuation of the Euler Transform*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **5**, 252–255.
[Article PDF](Carlson/References/Carlson1974AnalyticContinuationEulerTransform-SIAM.JMathAnal05.pdf).

**Content.** For a function holomorphic near \([0,1]\), the gamma-normalized
Euler integral initially defines a function of two parameters with positive
real parts. Carlson continues it to an entire function of those parameters
using a single contour surrounding the interval. The kernel is a regularized
Gauss hypergeometric function. Unlike the usual Pochhammer double-loop formula,
this representation does not fail at positive integral parameter values.

The proof identifies the kernel's jump across the interval and controls the
small circles at its endpoints when the contour is collapsed. An application
gives a representation of regularized Appell \(F_1\) for all parameter values
and all argument values in its principal cut-plane domain, followed by the
corresponding Lauricella/\(R\)-function representation. The gamma normalization
is essential to the entire-parameter claim; it should not be dropped at
exceptional denominator parameters.

**Relation to the book.** This work is directly incorporated into **§6.8**.
The contour representation and joint continuation of the \(R\)-function use
the same mechanism, and p. 156 explicitly sends the reader to this paper for
details of the contour-collapse argument. Chapter 4 supplies the beta/Euler
integrals, while §5.11 provides the averaged Cauchy-kernel viewpoint. The
article is a focused source for analytic details condensed in the book.

### 13. Carlson (1974), *Expansion of Analytic Functions in Jacobi Series*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **5**, 797–808.
[Article PDF](Carlson/References/Carlson1974ExpansionAnalyticFunctionsJacobiSeries-SIAM.JMathAnal05.pdf).

**Content.** A function holomorphic inside an ellipse with arbitrary complex
foci has a Jacobi expansion for complex indices \(\alpha,\beta\), provided
\(\alpha+\beta\notin\{-2,-3,-4,\ldots\}\). Orthogonality and real indices are
unnecessary. The coefficients are Dirichlet averages of derivatives, and the
series converges absolutely in the ellipse and uniformly on compact subsets.
When the foci coincide, the same notation gives the Taylor series directly.

The proof first expands the Cauchy kernel, using a finite remainder identity
and bounds for the Jacobi function of the second kind. Cauchy's formula then
gives the general expansion. The paper proves coefficient bounds analogous to
Cauchy's inequalities and uniqueness on an open domain. A jump formula across
the interfocal segment and contour biorthogonality support the uniqueness
argument. Special expansions illustrate the theorem; Laguerre and Hermite
limits are noted without a full treatment of their expansion theories.

**Relation to the book.** This is a principal article source for the program
of **§§7.1–7.2 and 7.5–7.8**, especially Theorem 7.6-2. The Chapter 7 notes
explicitly cite it for a different proof of the Cauchy-kernel expansion in
Lemma 7.6-1. The book substantially incorporates and reorganizes the theory,
adding its own asymptotic route and further polynomial developments. The paper
is especially useful for the finite-remainder, boundary-jump, and uniqueness
arguments underlying that treatment.

### 14. Carlson (1975), *Invariance of an Integral Average of a Logarithm*

**Source:** B. C. Carlson, *The American Mathematical Monthly* **82**, 379–382.
[Article PDF](Carlson/References/Carlson1975InvarianceIntegralAverageLogarithm-MAA.AmerMathMonthly82.pdf).

**Content.** The paper studies the arcsine-weighted logarithmic average
\(A(x,y)=(2/\pi)\int_0^{\pi/2}\log(x\sin^2\theta+y\cos^2\theta)\,d\theta\).
For nonnegative \(x,y\), not both zero, a change of variable proves
\(A(x,y)=\tfrac12 A(((x+y)/2)^2,xy)\). Iterating this identity evaluates the
integral as \(2\log((\sqrt{x}+\sqrt{y})/2)\). Thus the paper supplies a
logarithmic analogue of the invariance underlying Gauss's arithmetic–geometric
mean method, although its iteration and scaling are different.

The generalization replaces the arcsine weight by a beta weight. It transforms
the equal-parameter average \(L(\beta,\beta;x,y)\) into an average with
parameters \((\beta,1/2)\) at the transformed arguments. The final discussion
extends the identities into complex domains by analytic continuation, with
the branch and parameter restrictions made explicit.

**Relation to the book.** Exercise 5.9-12 introduces logarithmic Dirichlet
averages, and §§6.9–6.10 develop the quadratic-transformation and iterative
background. The article gives a specialized logarithmic invariance and
evaluation beyond the identities requested in that exercise. It is an early
precursor of the systematic 1987 \(L_t\) paper, where logarithmic averages and
their transformations become part of a general-order theory.

### 15. Carlson (1975), *Appell's Function F4 as a Double Average*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **6**, 960–965.
[Article PDF](Carlson/References/Carlson1975AppellFunctionF4DoubleAverage-SIAM.JMathAnal06.pdf).

**Content.** The 1971 multiple-average paper did not represent general Appell
\(F_4\). This paper fills that gap: unrestricted parameters admit a double
Dirichlet-average representation with a matrix having two rows and three
columns. Six parameter restrictions reduce the construction to two rows and
two columns. Along the way, a quadratic transformation takes \(F_4\) with equal
denominator parameters to a double series of order three. This illustrates why
classifying double hypergeometric series solely by the degrees of their
coefficient-ratio functions does not necessarily classify their transformation
theory well. Jacobi and Gegenbauer polynomial expansions are the bridge to the
double-average formulas.

**Relation to the book.** There is a more specific connection than a general
appeal to Chapters 5–6: **Exercise 7.1-13**, on p. 223, expresses \(F_4\) as a
series of Jacobi polynomials and treats the equal-denominator case as a
Dirichlet average of a Gauss series. That captures an important part of the
paper's mechanism. The full two-by-three representation and the six restricted
matrix cases go beyond the exercise and the book's predominantly single-average
treatment.

### 16. Carlson (1976), *Quadratic Transformations of Appell Functions*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **7**, 291–304.
[Article PDF](Carlson/References/Carlson1976QuadraticTransformationsAppellFunctions-SIAM.JMathAnal07.pdf).

**Content.** A two-by-two double average admits eight quadratic transformations,
each with two free parameters and two independent variables. Specializations
connect Appell functions with one another and with other double series;
several transformations cross the conventional boundary between series of
orders two and three. Applications give a direct proof of the Gegenbauer
addition theorem and related polynomial identities. Elliptic specializations
include Landen transformations for incomplete integrals of the first and second
kinds and Bartky's transformation for the complete third kind.

**Relation to the book.** Sections 6.9–6.10 develop quadratic transformations,
§6.11 supplies Gegenbauer's product formula, §7.3 proves the addition theorem,
and §9.5 treats Landen transformations. Thus several prominent consequences
belong to the book, but the eight-transformation organization through double
averages is considerably broader than its presentation.

**Domain qualification.** The introduction corrects the 1971 assertion about
arbitrary positions of matrix entries relative to the branch cut. The formulas
are taken in the right half-plane, or in a larger domain to which continuation
has actually been justified. This restriction is important when extracting
formal theorem statements from either article.

### 17. Carlson (1976), *The Need for a New Classification of Double Hypergeometric Series*

**Source:** B. C. Carlson, *Proceedings of the American Mathematical Society*
**56**, 221–224.
[Article PDF](Carlson/References/Carlson1976NeedNewClassificationDoubleHypergeometricSeries-AMS.ProcAMS56.pdf).

**Content.** Horn's order of a multiple hypergeometric series is determined by
the degrees of the rational functions relating neighboring coefficients.
Carlson gives an elementary example in which a **linear** change of variables
transforms Appell's \(F_1\), of order two, into a series of order three.
The proof uses absolute convergence, regrouping by total degree, the binomial
theorem, and Vandermonde's identity. Additional numerator and denominator
parameters give examples connecting orders \(M\) and \(M+1\), and the method
extends to more than two variables.

The point is sharper than the quadratic examples in the 1975 \(F_4\) and 1976
Appell-transformation papers: even a linear coordinate change can alter the
classification by order. The paper establishes this defect and argues for a
different foundation; it does **not** construct a complete replacement
classification.

**Relation to the book.** Chapter 2 supplies the Pochhammer and Vandermonde
identities, while Chapters 5–6 illustrate the alternative emphasis on averages,
homogeneity, and permutation symmetry. The paper is listed in the book's
bibliography as Carlson (1976b). Its classification argument is a methodological
supplement rather than a major additional chapter of function identities, and
helps explain why multiple averages can be more informative than a catalogue
organized only by double-series order.

### 18. Carlson (1977), *Elliptic Integrals of the First Kind*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **8**, 231–242.
[Article PDF](Carlson/References/Carlson1977EllipticIntegralsFirstKind-SIAM.JMathAnal08.pdf).

**Content.** The paper reduces integrals of the reciprocal square root of a real
polynomial of degree at most four, with known roots, to the symmetric standard
integral \(R_F\). The quadratic reduction preserves symmetry in the roots.
When at least one root is real, an interval with neither endpoint at a root can
be handled by a single standard integral instead of a difference of two. Cubic
and lower-degree cases appear as degenerations. Separate treatments cover real
roots, a conjugate pair, and two conjugate pairs. In the last case a distinguished
point on the real line affects the formula, so the single-integral assertion
must not be extended without qualification to every root configuration.

**Relation to the book.** This is directly incorporated into **§9.8**, whose
quartic-reduction theorem and discussion explicitly refer to the paper.
Section 9.7 supplies the addition theorem used to combine intervals. The paper
is valuable for its fuller collection of root configurations and explicit
formulas; it is not a wholly post-book advance merely because its publication
year is also 1977. It provides the starting point for the later second- and
third-kind tables.

## Articles published after 1977

### 19. Carlson (1979), *Computing Elliptic Integrals by Duplication*

**Source:** B. C. Carlson, *Numerische Mathematik* **33**, 1–16.
[Article PDF](Carlson/References/Carlson1979ComputingEllipticIntegralsDuplication-NumerMath33.pdf).

**Content.** This paper turns duplication identities into a coordinated
computational method for \(R_F,R_D,R_J\), and \(R_C\). Repeated duplication
brings the arguments close together; a short expansion about equal arguments
then gives an accurate value. The paper supplies explicit correction
polynomials, truncation-error bounds, precision criteria, and numerical
examples. Transformations also address real principal-value cases for the
functions with a pole parameter. An appendix develops the \(R\)-polynomial and
symmetric-polynomial expansions behind the error analysis.

The stated algorithms focus on real arguments in the specified admissible
ranges. Possible complex use should not be confused with the fully developed
real computational treatment in the paper.

**Relation to the book.** Duplication itself is already in §9.6, including a
Taylor-accelerated approximation such as (9.6-12); §§6.2 and 6.6 supply polynomial
background. The advance is a practical, quantitatively controlled algorithmic
treatment of the whole later standard family, particularly the second and
third kinds. The shift from the book's \(R_G,R_H\) basis to \(R_D,R_J\) is part
of that development. This is a major computational extension of Chapter 9,
rather than the first appearance of duplication.

### 20. Carlson and Notis (1981), *Algorithm 577: Algorithms for Incomplete Elliptic Integrals*

**Source:** B. C. Carlson and Elaine M. Notis, *ACM Transactions on Mathematical
Software* **7**, 398–403.
[Article PDF](Carlson/References/CarlsonNotis1981Algorithm577AlgorithmsIncompleteEllipticIntegralsS21-ACM.TransMathSoftware07.pdf).

**Content.** This software article implements the 1979 duplication algorithms
for \(R_F,R_D,R_J\), and \(R_C\) in Fortran. It explains admissible real argument
ranges, the use of homogeneity to rescale inputs, and machine-dependent bounds
chosen to avoid overflow and underflow. A tolerance parameter controls the
degree-five Taylor truncation after duplication; error returns and consistency
checks support practical use. Complete integrals are included as admissible
zero-argument cases despite the title's emphasis on incomplete integrals.

The paper discusses rearrangements that reduce underflow risk and reports
tests against independent values and implementations. Its tolerance concerns
truncation error, not a complete proof of floating-point roundoff behavior.
The local printed article contains the listing for \(R_C\); it explicitly
states that the complete listing of the algorithms was distributed separately.
The printed real-domain programs should not be conflated with the later
principal-value and complex-domain versions.

**Relation to the book.** Section 9.6 provides the mathematical duplication
background, but the book does not supply this portable program interface,
machine-range analysis, and test material. The immediate mathematical source
is the 1979 paper. Together they distinguish the analytic algorithm from the
engineering required for a usable numerical implementation; the 1987–1988
supplements and the 1995 paper continue that development.

### 21. Carlson and Gustafson (1983), *Total Positivity of Mean Values and Hypergeometric Functions*

**Source:** B. C. Carlson and John L. Gustafson, *SIAM Journal on Mathematical
Analysis* **14**, 389–395.
[Article PDF](Carlson/References/CarlsonGustafson1983TotalPositivityMeanValuesHypergeometricFunctions-SIAM.JMathAnal14.pdf).

**Content.** The subject is positivity of determinants of sampled kernels,
including strict total positivity of all orders. Negative-order power means
and reciprocals of positive-order power means provide initial examples.
Reciprocals of the logarithmic, arithmetic–geometric, and Schwab–Borchardt means
are also strictly totally positive. Integral representations yield analogous
results for hypergeometric kernels and for \(R_F,R_D,R_J\), considered as
functions of two arguments with the remaining arguments fixed and positive.

The paper carefully distinguishes total positivity from positivity only through
order two. Counterexamples show that plausible extensions to reciprocals of
general hypergeometric means fail already for determinants of order three.
A final section relates the kernels to Pólya frequency functions, using
bilateral Laplace transforms and obtaining a convolution representation.

**Relation to the book.** The functions, means, and integral representations
come directly from Chapters 5–6, §8.3, and Chapter 9. What is new is the
determinantal theory imposed on them. The book's ordinary inequalities and
positivity statements do not amount to this theory. This is a new direction
built on the book, with both positive results and useful limits on possible
generalization.

### 22. Carlson and Shaffer (1984), *Starlike and Prestarlike Hypergeometric Functions*

**Source:** B. C. Carlson and Dorothy B. Shaffer, *SIAM Journal on Mathematical
Analysis* **15**, 737–745.
[Article PDF](Carlson/References/CarlsonShaffer1984StarlikePrestarlikeHypergeometricFunctions-SIAM.JMathAnal15.pdf).

**Content.** The paper studies normalized analytic functions in the unit disk
through Hadamard products, meaning coefficientwise products of power series.
A hypergeometric convolution operator multiplies coefficients by a ratio of
Pochhammer symbols. Its algebraic properties and integral representations allow
the authors to study starlike, convex, and prestarlike classes, including
classes of a prescribed order. Hypergeometric functions and Dirichlet averages
give integral representations and families approximating functions in these
classes. The paper thus connects hypergeometric coefficient transformations
with geometric properties of analytic functions.

**Relation to the book.** Chapter 5 supplies the averaging and coefficient
machinery, and §8.2 discusses special conformal mappings through
Schwarz–Christoffel integrals. The article goes into a different, much more
systematic theory of univalence and convolution operators on the disk. Neither
the book's mapping examples nor its power-series identities include this
starlike/prestarlike theory. It is a substantial additional complex-analysis
application, rather than a missing computational formula from Chapter 9.

### 23. Carlson and Gustafson (1985), *Asymptotic Expansion of the First Elliptic Integral*

**Source:** B. C. Carlson and John L. Gustafson, *SIAM Journal on Mathematical
Analysis* **16**, 1072–1092.
[Article PDF](Carlson/References/CarlsonGustafson1985AsymptoticExpansionFirstEllipticIntegral-SIAM.JMathAnal16.pdf).

**Content.** This is a detailed treatment of the logarithmic singularity of the
first elliptic integral. It begins with a four-factor integral and derives
expansions valid when two arguments are small relative to the other two.
The coefficients involve Legendre polynomials and derivatives with respect
to their degree, equivalently particular power-log averages. The \(R_F\)
expansion follows as a limiting case. Mellin-transform methods produce the
series; explicit remainder formulas and Chebyshev's integral inequality produce
useful absolute and relative error bounds. Uniform convergence is established
in stated separated-argument ranges. The appendix develops a general
Mellin-convolution remainder theorem, not just an elliptic special case.

**Relation to the book.** Equation **(9.2-10)** already gives leading logarithmic
behavior, and §8.3 provides related hypergeometric limiting formulas. The paper
adds a full expansion, convergence information, and controlled remainders. Its
asymptotic regime is different from the large-degree polynomial asymptotics of
§7.4. It also explains an important motivation for the 1987 power-log paper:
the latter develops systematically the coefficient functions needed here.

### 24. Brenner and Carlson (1987), *Homogeneous Mean Values: Weights and Asymptotics*

**Source:** J. L. Brenner and B. C. Carlson, *Journal of Mathematical Analysis
and Applications* **123**, 265–280.
[Article PDF](Carlson/References/BrennerCarlson1987HomogeneousMeanValuesWeightsAsymptotics-JMathAnalAppl123.pdf).

**Content.** This paper places many types of means in a common homogeneous
framework. For a differentiable normalized mean, derivatives at the all-ones
vector define its weights. With sufficient smoothness, translating all inputs
far in the same direction gives
\(M(x+a_1,\ldots,x+a_n)=x+\sum_i w_i a_i+O(x^{-1})\).
Examples include power means, mixed means, and hypergeometric means.

A second part studies asymptotics of Dirichlet averages as the number of nodes
and the total parameter mass grow. If positive nodes remain bounded above and
away from zero, the parameter mass tends to infinity, and the weighted arithmetic
means converge, the corresponding hypergeometric means converge to the same
limit. The logarithmic case is included. This is more general than sending the
concentration to infinity for a fixed finite set of nodes.

**Relation to the book.** Homogeneity, differentiation of averages, and
hypergeometric means are available in Chapters 5–6. The paper adds a unified
local description of weights and a growing-family asymptotic theory. The
fixed-dimensional concentration limit recalls the 1965 paper; the general
asymptotic framework and varying-number-of-nodes results extend the book.

### 25. Carlson (1987), *Dirichlet Averages of x^t log x*

**Source:** B. C. Carlson, *SIAM Journal on Mathematical Analysis* **18**, 550–565.
[Article PDF](Carlson/References/Carlson1987DirichletAveragesPowerLog-SIAMJMathAnal18.pdf).

**Content.** The paper develops the family
\(L_t(b,z)=\partial R_t(b,z)/\partial t\), the Dirichlet average of
\(x^t\log x\). It gives general identities, differentiation formulas,
Euler–Poisson equations, associated-function relations, zero-argument limits,
series expansions, quadratic transformations, and inequalities. Several
relations become inhomogeneous: differentiating a power identity introduces
\(R\)-terms alongside \(L\)-terms. Likewise, scaling introduces a logarithmic
correction rather than ordinary homogeneity. Digamma functions naturally occur
in parameter derivatives and series coefficients.

Examples connect the family with generalized hypergeometric functions,
dilogarithms, degree derivatives of Legendre functions, boundary-value problems,
means, and logarithmic elliptic-integral expansions. These applications show
why the family is useful in its own right rather than merely as a notation for
a derivative.

**Relation to the book.** The paper explicitly identifies the book's earlier
treatment as the special case **\(t=0\), Exercise 5.9-12 and its solution on
p. 305**. Chapters 5–6 provide the \(R\)-function theory from which many proofs
start, but they do not contain this systematic general-order \(L_t\) theory.
This is one of the most direct extensions of the book's central program and
remains a principal article reference for the project's power-log development.

### 26. Carlson (1987), *A Table of Elliptic Integrals of the Second Kind*

**Source:** B. C. Carlson, *Mathematics of Computation* **49**, 595–606, with a
supplement included in the local PDF.
[Article PDF](Carlson/References/Carlson1987TableEllipticIntegralsSecondKind-AMS.MathComput49.pdf).

**Content.** The paper supplies a compact table for integrals with real
branch points, expressed in symmetric \(R_F\) and \(R_D\) notation. There are
thirteen basic entries: nine quartic and four additional cubic cases. Permutation
symmetry and a uniform notation consolidate many traditional table entries.
The integration endpoints need not be branch points. Addition and reduction
identities avoid unnecessarily expressing a definite integral as the difference
of two standard integrals, and recurrence relations produce further cases.
The supplement contains Fortran routines for \(R_F\) and \(R_D\).

**Relation to the book.** Section 9.3 gives a smaller reduction table, while
§§9.7–9.8 provide the addition and quartic-reduction foundations. This paper
extends the first-kind reduction program of 1977 to a much more extensive and
practically organized second-kind table, using the later \(R_D\) basis. It adds
explicit coverage and computational implementation, not just another proof of
the abstract fact that elliptic integrals reduce to a finite standard family.
Its real-branch-point setting also distinguishes it from the 1992 paper.

### 27. Carlson (1988), *A Table of Elliptic Integrals of the Third Kind*

**Source:** B. C. Carlson, *Mathematics of Computation* **51**, 267–280, with a
supplement included in the local PDF.
[Article PDF](Carlson/References/Carlson1988TableEllipticIntegralsThirdKind-AMS.MathComput51.pdf).

**Content.** Continuing the table program, this paper gives thirty-one integrals
of the third kind and includes ten first- and second-kind cases in compatible
notation. The branch points are real, and arbitrary admissible endpoints are
allowed. The formulas use \(R_J\), together with \(R_F,R_D\), and the elementary
function \(R_C\). Recurrences and addition formulas organize the reduction;
principal values are addressed when a pole lies on the interval. The included
supplement supplies Fortran routines for \(R_C\) and \(R_J\), including the
relevant real principal-value transformations.

**Relation to the book.** Section 8.5 explains the role of integral parameters
and their elimination, and Chapter 9 supplies the original third-kind standard
integral and reduction framework. The article greatly expands the explicit
table, develops formulas in the later \(R_J\) normalization, and connects the
symbolic reductions with numerical evaluation. As with the second-kind paper,
the addition is a detailed usable reduction system, not merely the existence
of associated-function relations already known from the book.

### 28. Carlson (1989), *A Table of Elliptic Integrals: Cubic Cases*

**Source:** B. C. Carlson, *Mathematics of Computation* **53**, 327–333.
[Article PDF](Carlson/References/Carlson1989TableEllipticIntegralsCubicCases-MathComp53.pdf).

**Content.** The table covers forty-one integrands that are rational apart
from a square root of a cubic with known real zeros: one first-kind case,
twenty-six second-kind cases, and fourteen third-kind cases. Arbitrary
admissible endpoints are allowed. Three basic integrals, together with
algebraic endpoint terms, organize the formulas in \(R_F,R_D,R_J,R_C\)
notation. Recurrences generate most entries from earlier formulas, and the
paper reports numerical checks of every entry.

Cubic formulas can often be obtained by specializing quartic ones, but keeping
the quartic machinery gives unnecessarily complicated expressions. This paper
provides the simpler cubic forms explicitly. It also distinguishes combinations
appropriate for infinite endpoints, avoiding separate divergent quantities
whose cancellation would otherwise be required. Real principal-value cases
are treated through the stated conventions for the pole parameters.

**Relation to the book.** Sections 9.3 and 9.8 contain the general reduction
setting and the relation between cubic and quartic cases. The 1987–1988 papers
expand that setting mainly through quartic tables; this paper supplies the
corresponding systematic cubic table. It adds explicit coverage and carefully
chosen computational forms beyond the book's shorter table, while remaining
within the real-root setting.

### 29. Carlson (1991), *A Table of Elliptic Integrals: One Quadratic Factor*

**Source:** B. C. Carlson, *Mathematics of Computation* **56**, 267–280.
[Article PDF](Carlson/References/Carlson1991TableEllipticIntegralsOneQuadraticFactor-MathComp56.pdf).

**Content.** The integrands are rational except for a square root of a cubic
or quartic with exactly one pair of conjugate complex zeros. The table gives
thirty-three explicit cases—eighteen quartic and fifteen cubic—and formulas
that put forty-five further cases from the earlier tables into real form.
The conjugate linear factors are combined into a positive irreducible real
quadratic. Landen transformations of \(R_F\) and \(R_J\) then remove complex
arguments from the basic integral formulas; recurrences produce the remaining
entries. Neither endpoint need be a singular point, and appropriate
principal-value cases are included. Proofs and numerical checks accompany the
tables.

**Relation to the book.** Section 9.8 already treats the role of complex
conjugate roots in first-kind reduction, and §9.5 provides Landen transformations.
The article extends those foundations to a large table covering all three
kinds and organized for evaluation with real quantities. It connects the
real-root tables of 1987–1989 with the two-quadratic-factor table of 1992.
Those papers together address the distinct real root configurations; the
book's general quartic-reduction theorem does not by itself supply this
collection of real computational formulas.

### 30. Carlson (1991), *B-Splines, Hypergeometric Functions, and Dirichlet Averages*

**Source:** B. C. Carlson, *Journal of Approximation Theory* **67**, 311–325.
[Article PDF](Carlson/References/Carlson1991BSplinesHypergeometricFunctionsDirichletAverages-JApproxTheory67.pdf).

**Content.** The paper identifies B-splines with densities, or more generally
distributions, obtained by projecting Dirichlet measure through the affine
combination of knots. Repeated knots correspond to integer Dirichlet parameters.
A univariate spline is recovered from a boundary jump of an \(R_{-1}\)
function; its moments and transforms are described by \(R\)- and \(S\)-functions.
This connects splines with Cauchy transforms, divided differences, and
hypergeometric functions.

The second half extends Dirichlet averages to vector-valued nodes and develops
multivariate splines. It obtains support in the convex hull of the knots,
recurrences, differentiation formulas, and Euler–Poisson equations for the
dependence on knots. The distributional viewpoint matters: degenerate knot
configurations can produce a Dirac mass rather than an ordinary continuous
density.

**Relation to the book.** This is a particularly direct application of §4.4,
§5.4, the divided-difference formulas of §5.5, the power and exponential averages
of §§5.8–5.9, and the Cauchy viewpoint of §5.11. The book provides much of the
scalar machinery but does not develop this spline theory or its multivariate
distributional formulation. The paper opens a new application area while also
making several of the book's identities concrete in approximation theory.

### 31. Carlson (1992), *A Table of Elliptic Integrals: Two Quadratic Factors*

**Source:** B. C. Carlson, *Mathematics of Computation* **59**, 165–180.
[Article PDF](Carlson/References/Carlson1992TableEllipticIntegralsTwoQuadraticFactors-AMS.MathComput59.pdf).

**Content.** This table treats integrands containing the square root of the
product of two irreducible real quadratic factors: the quartic has two pairs
of conjugate complex roots. Thirteen cases cover integrals of all three kinds,
with additional linear factors where appropriate. The formulas are arranged
for computation using real arguments of symmetric elliptic integrals, despite
the complex roots of the quartic. They accommodate arbitrary real intervals
where the integral or specified principal value exists.

Landen and duplication transformations remove restrictions that appear in
earlier formulas for this root configuration. The appendices handle a complex
pole parameter in a particular \(R_J\) reduction and express complex \(R_C\)
quantities through real ones, including cancellation issues.

**Relation to the book.** Section 9.8 and the 1977 first-kind article already
encounter quartics with no real roots, but with more restricted formulas. The
1992 paper provides a substantially more complete real computational treatment
and extends it to the second and third kinds. It complements the real-root
tables of 1987–1989 and the one-quadratic-factor table of 1991. Together these
papers cover the three root configurations: all roots real, one conjugate
pair, and two conjugate pairs.

### 32. Carlson and Gustafson (1994), *Asymptotic Approximations for Symmetric Elliptic Integrals*

**Source:** B. C. Carlson and J. L. Gustafson, *SIAM Journal on Mathematical
Analysis* **25**, 288–303.
[Article PDF](Carlson/References/CarlsonGustafson1994AsymptoticApproximationsSymmetricEllipticIntegrals-SIAM.JMathAnal25).

**Content.** This paper systematically studies symmetric elliptic integrals
when some real nonnegative arguments are much larger than others. It gives
approximations with explicit error bounds for \(R_F,R_D,R_J,R_G\), and the
elementary \(R_C\), including complete limiting cases and several separated-scale
regimes for the third kind. Most proofs construct a uniform approximation to
the integrand by combining inner and outer approximations and subtracting their
overlap. Elementary inequalities then bound the integrated remainder; an
appendix develops the inequalities used.

An application proves that \(R_F,R_D,R_J\), and \((xyz)^{-1/2}\) are linearly
independent over rational functions of their arguments. The proof separates
logarithmic and algebraic asymptotic behaviors. Independence over **algebraic**
coefficient functions is explicitly left open in the paper.

**Relation to the book.** Sections 8.3 and 9.2 contain limiting formulas and
the independence of the book's \(R_F,R_G,R_H\) basis. The article greatly
expands the bounded approximations and supplies a direct independence proof
for the later \(R_F,R_D,R_J\) basis, rather than simply transferring the old
basis theorem. Compared with the 1985 paper's full logarithmic expansion for
the first kind, it treats a broader family and more asymptotic regimes,
usually through explicit low-order approximations with remainders.

### 33. Carlson (1995), *Numerical Computation of Real or Complex Elliptic Integrals*

**Source:** B. C. Carlson, *Numerical Algorithms* **10**, 13–26.
[Article PDF](Carlson/References/Carlson1995NumericalComputationRealComplexEllipticIntegrals-NumerAlgorithms10.pdf).

**Content.** The duplication algorithms are extended to complex arguments and
reorganized to reduce arithmetic and underflow risk. A requested fractional
error determines stopping, and the repeated \(R_C\) calculations used by
\(R_J\) are accelerated with a degree-seven expansion. A separate
arithmetic–geometric mean algorithm handles complete first- and second-kind
integrals efficiently. The paper provides numerical values, consistency
identities, and conversions to Legendre's and Bulirsch's integrals.

The domain and error qualifications are important. The \(R_J\) algorithm has
sufficient restrictions beyond the natural definition domain to keep its
transformed pole parameter from reaching zero. The author explicitly notes
that cancellation makes the stated complex relative-error bound nonrigorous
for \(R_J\), and repeats that qualification for \(R_D\). Roundoff is assumed
negligible, and a full complex proof of the bounds is deferred. The real
principal-value transformation is not claimed valid for arbitrary complex
remaining arguments. Thus the paper supplies algorithms and checks, but not
a complete certified complex floating-point analysis.

**Relation to the book.** Sections 9.5–9.6 supply Landen, mean, and duplication
foundations. The paper advances the 1979 methods and 1981 implementation into
complex computation and improves their real versions as well. It complements
the 1991–1992 tables: direct complex evaluation can sometimes avoid the
additional transformations those tables use to obtain exclusively real
arguments. This is a substantial computational extension of Chapter 9.

### 34. Carlson (1999), *Toward Symbolic Integration of Elliptic Integrals*

**Source:** B. C. Carlson, *Journal of Symbolic Computation* **28**, 739–753.
[Article PDF](Carlson/References/Carlson1999TowardSymbolicIntegrationEllipticIntegrals-JSymbolComput28.pdf).

**Content.** The paper organizes reduction into an explicit procedure suitable
for symbolic computation. Starting from a factored integrand with specified
exponents, partial fractions reduce the rational part; systematic recurrence
relations reduce the remaining integrals to a basic family; quadratic
reductions express that family through \(R_F,R_D,R_J,R_C\) and elementary
terms. A worked example illustrates the stages. The aim is to eliminate the
human choice previously needed when applying recurrence relations to construct
tables. Both endpoints are retained in the formulas.

Complex factors require explicit square-root and domain conditions in the
reduction theorems. The paper discusses modifications needed outside those
conditions and reports an implementation by James FitzSimons in Derive. It
assumes the requisite factorization; it is not a general-purpose algorithm for
factoring arbitrary input expressions.

**Relation to the book.** Sections 8.1, 8.4–8.5, 9.3, and 9.8 supply the
recognition, associated-function, and reduction background. The article turns
that structural theory, together with the intervening table work, into a
more explicit computational procedure. For formalization, this distinction is
material: proving that a finite basis exists is weaker than specifying and
verifying the reduction steps of an algorithm.

### 35. Carlson (2004), *Symmetry in c, d, n of Jacobian Elliptic Functions*

**Source:** B. C. Carlson, *Journal of Mathematical Analysis and Applications*
**299**, 242–253.
[Article PDF](Carlson/References/Carlson2004SymmetryJacobianEllipticFunctions-JMathAnalAppl299.pdf).

**Content.** The twelve Jacobian elliptic functions are organized so that
permutations of the letters \(c,d,n\) generate families of identities. The
functions ending in \(s\) are linked to \(R_F\) through an inverse-integral
relation. Differences of their squares are constants, encoded by a compact
\(\Delta\)-notation. From these facts the paper derives derivative formulas,
bisection, duplication, addition, and transformations of the modulus. Several
classically separate Landen, Gauss, and complex transformations become members
of common families. The treatment works directly from the symmetric integral,
without making theta or Weierstrass functions the foundation.

**Relation to the book.** Section 8.2 introduces elliptic functions by inversion,
including Jacobian functions on pp. 237–240; §§9.5–9.7 develop transformations
of the integrals. The paper builds a much more extensive and systematic calculus
for all twelve inverse and quotient functions. It therefore extends the
book's elliptic-function coverage substantially. The inverse-integral identities
must retain their branch/domain conditions; they are not global single-valued
inverse statements for periodic functions.

### 36. Carlson (2005), *Jacobian Elliptic Functions as Inverses of an Integral*

**Source:** B. C. Carlson, *Journal of Computational and Applied Mathematics*
**174**, 355–359.
[Article PDF](Carlson/References/Carlson2005JacobianEllipticFunctionsInversesIntegral-JComputApplMath174.pdf).

**Content.** This short paper gives a uniform inversion procedure for an
integral with denominator
\(\sqrt{(a_1+b_1t^2)(a_2+b_2t^2)}\), under real interval conditions that make
the integrand positive. Four choices of a distinguished endpoint are treated.
Ordering the three quantities \(0,a_1b_2,a_2b_1\) determines the scaling and
elliptic modulus. The resulting classification gives twenty-four inversions:
twelve Jacobian elliptic, six circular, and six hyperbolic. Degenerations are
therefore built into the same procedure as the genuinely elliptic cases.
The proof uses reduction to \(R_F\).

**Relation to the book.** The ingredients belong to §8.2 on inversion and
elliptic functions, §9.4 on applications, and §9.8 on reduction. The added value
is a concise, explicit classification that converts a given real quartic
integral into the appropriate inverse function. It complements the broad
symmetry theory of the 2004 paper by giving a practical recognition and
inversion rule.

### 37. Carlson (2006), *Some Reformulated Properties of Jacobian Elliptic Functions*

**Source:** B. C. Carlson, *Journal of Mathematical Analysis and Applications*
**323**, 522–529.
[Article PDF](Carlson/References/Carlson2006SomeReformulatedPropertiesJacobianEllipticFunctions-JMathAnalAppl323.pdf).

**Content.** Continuing the 2004 treatment, this paper rewrites algebraic
relations, differential equations, and integration formulas in the symmetric
notation for the twelve Jacobian functions. Sixteen familiar squared-function
relations are organized through five basic relations. First-order equations
involving quartic polynomials and second-order equations involving cubic
polynomials take uniform forms. Integrals of first and third powers are
expressed through the elementary \(R_C\) function, and recurrences reduce higher
powers. Even-power reductions require elliptic base integrals, unlike the
elementary odd-power starting cases.

**Relation to the book.** The book contains the initial Jacobian-function
setting in §8.2 and the elementary/elliptic integral distinction in Chapters
8–9, with \(R_C\) already available in Chapter 6. It does not provide this
coordinated set of formulas for all twelve functions. The article is chiefly a
structural reorganization and extension of that calculus. For precise use,
indefinite-integral identities are understood on appropriate domains and up
to constants of integration.

### 38. Carlson (2011), *Permutation Symmetry for Theta Functions*

**Source:** B. C. Carlson, *Journal of Mathematical Analysis and Applications*
**378**, 42–48.
[Article PDF](Carlson/References/Carlson2011PermutationSymmetryThetaFunctions-JMathAnalAppl378.pdf).

**Content.** The four theta functions are normalized using their values, or
the derivative of the odd theta function, at zero. Ratios of these normalized
functions provide twelve functions parallel to the twelve Jacobian functions.
Differences of suitable squared ratios are constants expressible through theta
constants. An \(R_F\) identity then connects this construction with the earlier
Jacobian symmetry theory. The paper gives derivative and differential-equation
formulas, bisection and duplication formulas, and addition formulas; it presents
some of the latter as apparently new. It also illustrates pseudoaddition
identities.

**Relation to the book.** The bridge begins with the elliptic functions of
§8.2 and the symmetric integral and transformations of Chapter 9. The theta
normalization and permutation theory are a new direction beyond the book's
systematic coverage. This is not a general account of all theta-function
theory: the emphasis is on identities in the argument, with the nome fixed,
and their relation to the symmetric elliptic-integral approach.

## Overall relation of the collection to the book

The collection makes the development before and after 1977 particularly clear.

1. **The central Dirichlet-average program is already largely present in the
   book.** The 1969 *Connection* and 1970 *Hidden Symmetries* papers supply
   foundations and motivation for Chapter 5. The 1974 Euler-transform paper
   supplies analytic details for §6.8, and the 1974 Jacobi-series paper is a
   principal source for Chapter 7. The early mean papers feed into Chapters
   2 and 6, and the 1977 first-kind reduction is directly represented in §9.8.
   These articles often supply more detailed proofs, hypotheses, or examples
   rather than entirely missing subjects.

2. **Multiple averages are a larger pre-book theory than the book develops.**
   The 1971, 1975, and 1976 Appell papers form a connected sequence: a matrix
   averaging framework, its extension to general \(F_4\), and a family of
   quadratic transformations. The book selects polynomial identities,
   generating relations, and elliptic consequences from this broader theory.
   The 1976 classification paper explains why even linear transformations
   undermine classification solely by series order. The separate 1976 domain
   correction in the Appell-transformation paper is essential when reading
   this sequence.

3. **The computational papers carry the mean and duplication methods into
   numerical practice.** The 1971 algorithms paper classifies a larger family
   than the examples developed in §6.10. The 1979 paper provides quantitative
   duplication algorithms; the 1981 paper addresses implementation and machine
   range; the 1995 paper improves the formulas and extends computation to
   complex arguments. Analytic truncation bounds, complex cancellation, and
   floating-point errors are distinct issues, and the articles do not claim
   to settle all three uniformly.

4. **The later elliptic tables and asymptotic papers substantially extend
   Chapter 9.** The 1987–1989 tables organize real-root quartic and cubic
   integrals, the 1991 table handles one conjugate pair, and the 1992 table
   handles two pairs. The 1999 paper turns reduction into a symbolic procedure.
   The 1985 and 1994 papers add, respectively, a detailed first-kind expansion
   and a broad collection of bounded asymptotic approximations; the latter
   also proves rational-coefficient independence for the later elliptic basis.
   These contributions go well beyond the book's general reduction and
   transformation theorems.

5. **Power-log averages are a direct enlargement of the book's main function
   family.** The 1975 logarithmic-invariance paper and the book's
   logarithmic-average exercise precede the systematic \(L_t\) theory of 1987.
   Its connection with the 1985 elliptic
   asymptotics is particularly useful: the two papers develop complementary
   parts of the same calculation.

6. **Several papers open distinct applications or theories.** The 1970
   Lardner-relations paper develops differential-equation reductions and
   elasticity applications beyond the book's even/odd series exercise. Mixed means,
   total positivity, starlike and prestarlike functions, growing-family mean
   asymptotics, and splines use the book's ingredients but cannot be recovered
   simply by filling in a few omitted textbook proofs. The spline paper is
   especially close to the Dirichlet-measure and Cauchy-transform foundations.

7. **The 2004–2011 papers expand elliptic-function coverage.** They proceed from
   symmetric integrals to a unified calculus of the twelve Jacobian functions
   and then to normalized theta-function ratios. The brief introduction to
   inverse elliptic functions in Chapter 8 is the starting point, not the
   full extent of this later program.

For using this collection alongside the formalization, a useful distinction is
therefore between completing the **1977 book**, strengthening its results with
**later bounds and explicit algorithms**, and adding **new mathematical areas**.
All three are worthwhile, but they represent different scopes of coverage.
