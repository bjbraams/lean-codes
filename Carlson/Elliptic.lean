/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Elliptic.Addition
public import Carlson.Elliptic.CompleteK
public import Carlson.Elliptic.Asymptotic
public import Carlson.Elliptic.Inversion
public import Carlson.Elliptic.Landen
public import Carlson.Elliptic.LandenAlgorithm
public import Carlson.Elliptic.LegendreThird
public import Carlson.Elliptic.Mapping
public import Carlson.Elliptic.Polygon
public import Carlson.Elliptic.RF
public import Carlson.Elliptic.SchwarzChristoffel
public import Carlson.Elliptic.Standard
public import Carlson.Elliptic.VertexLimits
public import Carlson.Elliptic.ZeroVariable
public import Carlson.Elliptic.QuarticReduction

/-!
# Elliptic integrals and elliptic functions in Carlson's Chapters 8 and 9

Umbrella module for the elliptic material of Carlson's Chapters 8 and 9. It covers:
- the symmetric integral `R_F` and the other symmetric standard functions, with Legendre's
  integrals;
- the Schwarz–Christoffel map, its boundary values, and Theorem 8.2-1;
- the Weierstrass and Jacobian elliptic functions obtained by inversion, with their half-periods
  as complete elliptic integrals;
- Landen's transformation, the duplication and addition theorems, and the associated algorithms.
- the leading logarithmic equivalents (8.3-16) and (9.2-10) along the positive real axis.

## Main results

* `Carlson.carlsonRF_eq_integral`, `Carlson.carlsonRF_self_right`: `R_F` as an integral (8.2-5)
  and its reduction to `R_C` (8.2-13).
* `Carlson.hasDerivAt_carlsonR_sub`, `Carlson.carlsonR_sub_eq_integral`: the Schwarz–Christoffel
  differential equation and integral (8.2-1)–(8.2-3).
* `Carlson.continuousOn_scMap`, `Carlson.tendsto_carlsonR_sub_nhdsWithin`: continuity up to the
  real axis and the vertices `w(xᵢ)`.
* `Carlson.bijOn_scMap`, `Carlson.differentiableOn_scMapInv`: Theorem 8.2-1 and the holomorphic
  inverse.
* `Carlson.bijOn_carlsonRF_sub`, `Carlson.sq_deriv_weierstrassInv`: Example 8.2-2.
* `Carlson.bijOn_snV`, `Carlson.sq_deriv_jacobiSn`: Example 8.2-3.
* `Carlson.carlsonRG`, `Carlson.carlsonRH`, `Carlson.legendreF_eq`: the standard functions of
  §9.2.
* `Carlson.legendrePi_eq_standard`, `Carlson.legendrePi_complete_eq_standard`: Legendre's
  third-kind integral reduced to `R_F`, `R_H` and to `R_K`, `R_L`, respectively.
* `Carlson.regCarlsonR_landen`, `Carlson.tendsto_ascLanden`, `Carlson.tendsto_descGauss`: §9.5.
* `Carlson.carlsonRF_duplication`, `Carlson.tendsto_dupSeq`: §9.6.
* `Carlson.carlsonRF_add_carlsonRF`: §9.7.
* `Carlson.carlsonRK_duplication`, `Carlson.carlsonRF_add_carlsonRF_zero`: the zero-variable cases
  of the duplication and addition theorems, (9.7-17).
* `Carlson.carlsonR_quartic_eq_carlsonRF`: Theorem 9.8-1,
  `R_{-1}(1/2, 1/2, 1/2, 1/2; A², B², C², D²) = 2 R_F(X², Y², Z²)`.
* `Carlson.isEquivalent_carlsonRF_atTop`, `Carlson.isEquivalent_carlsonRK_zero`:
  logarithmic equivalents (9.2-10), (8.3-16) for positive real variables.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapters 8 and 9.
-/
