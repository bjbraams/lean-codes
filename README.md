# Carlson special functions

A Lean 4 formalization of B. C. Carlson's approach to special functions through integration over the standard simplex with respect to complex Dirichlet densities.
The foundational developments are intended as potential Mathlib contributions.

## Organization

There are five main directories.

- `Pochhammer/`.
Support codes. Simplex-independent Pochhammer, gamma/beta and complex-power operations.

- `SeveralComplexVariables/`.
Support codes and more for simplex-independent several-complex-variable analysis.

- `StdSimplexMeasure/`.
Coordinates, aggregation, measure, integration, smooth simplex functions, and moment determination.

- `Dirichlet/`.
Real and complex beta functions, Dirichlet measures and densities, moments, averages, and analytic continuation.

- `Carlson/`.
R-polynomials, R/L/S/T functions, and two-variable specializations.

Dependencies flow from the support libraries and simplex foundations to
`Dirichlet`, then to `Carlson`. The simplex foundation never imports either
application layer; `Dirichlet` never imports `Carlson`. The two support libraries
never import the simplex or application layers.

Each directory has a matching umbrella module. `Main.lean` imports all five.
See the [module structure guide](STRUCTURE.md) for the finer topic splits and import paths.

## References

Carlson, B. C. "Special Function of Applied Mathematics." Academic Press, 1977.

Carlson, B. C. "Dirichlet averages of $x^t\log x$."
SIAM Journal on Mathematical Analysis 18, no. 2 (1987): 550-565.
