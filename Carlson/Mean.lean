/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Basic
public import Carlson.Mean.Weights
public import Carlson.Mean.Real
public import Carlson.Mean.Inequalities
public import Carlson.Mean.Order
public import Carlson.Mean.Properties
public import Carlson.Mean.Euler
public import Carlson.Mean.StrictOrder
public import Carlson.Mean.Minkowski
public import Carlson.Mean.LogConvex
public import Carlson.Mean.Ratio
public import Carlson.Mean.Holder
public import Carlson.Mean.Dresher
public import Carlson.Mean.Bounds
public import Carlson.Mean.Concentration
public import Carlson.Mean.ConcentrationQuadratic
public import Carlson.Mean.ConcentrationTwo
public import Carlson.Mean.OrderLimits

/-!
# Hypergeometric means

The complex mean, ratio mean, and power-transformed mean are built from the
continued R- and L-functions, with explicit branch hypotheses for analyticity.
Their derivative-defined weights are the normalized complex parameters. The
real probability-integral definitions agree with these complex functions on
positive nodes and parameters, for every real order.

The real theory includes continuity and strict order monotonicity for nonconstant
nodes, strict node monotonicity, normalization, positive homogeneity, bounds between node
extrema, arithmetic and power-mean comparisons, and Euler inversion. Equality in
order, arithmetic, and geometric comparisons is characterized by constant nodes.
Minkowski and reverse Minkowski hold with equality exactly at order one or for
proportional vectors; they also give convexity and concavity in the nodes. Constant
vectors and singleton index types are included.

Further results include strict log-convexity of R in the order, Hölder and reversed
Hölder with exact equality conditions, and Beckenbach–Dresher for ratio means.
The five strict bound chains of Carlson (1966) hold throughout their respective
order ranges, with explicit exceptional values and refinements of the minima.
The limits at infinite positive and negative order are the node extrema.

For fixed positive weights, R, L, and the mean are continuous in positive
concentration. At zero concentration the means tend to weighted power means
(geometric at order zero); at infinite concentration they tend to the arithmetic
mean. The zero-concentration limits of R and L also hold for complex orders,
normalized complex weights, and slit-plane nodes. Carlson–Tobey concentration
monotonicity is proved for two nodes at every real order. At quadratic order,
strict decrease and strict log-convexity hold for arbitrary finite nonconstant
real node sets, with an explicit strictly negative concentration derivative.
General finite-node concentration monotonicity and the remaining concentration
convexity results are still to be proved.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), 759–766.
* B. C. Carlson, *Some inequalities for hypergeometric functions*, Proc. AMS 17
  (1966), 32–39.
* B. C. Carlson and M. D. Tobey, *A property of the hypergeometric mean value*,
  Proc. AMS 19 (1968), 255–262.
* J. L. Brenner and B. C. Carlson, *Homogeneous mean values: weights and asymptotics*,
  J. Math. Anal. Appl. 123 (1987), 265–280.
-/
