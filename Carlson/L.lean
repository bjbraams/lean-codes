/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Carlson.L.Basic
public import Carlson.L.Continuation
public import Carlson.L.Relations
public import Carlson.L.Properties
public import Carlson.L.Deriv
public import Carlson.L.Series
public import Carlson.L.Associated
public import Carlson.L.SlitContinuation
public import Carlson.L.SlitIntegral
public import Carlson.L.SlitRelations
public import Carlson.L.SlitProperties
public import Carlson.L.SlitDeriv
public import Carlson.L.EulerPoisson
public import Carlson.L.JointRecurrence

/-!
# Carlson's Dirichlet averages of the power-logarithm kernel

The `regCarlsonLSlit` interface is jointly holomorphic in all complex exponents and
Dirichlet parameters and all slit-plane nodes. It extends the original right-half-plane
interface, which remains available. See `Carlson/L/Coverage.md` for the paper correspondence.
-/
