  # Standard-simplex measure instructions

  - Keep this directory devoted to general standard-simplex geometry, measure,
    integration, and calculus. Do not import Dirichlet or Carlson, even indirectly.
  - Dirichlet-specific results belong in Dirichlet/; Carlson functions in Carlson/.
  - Prefer the dependency order:
    1. coordinate maps and invariance;
    2. volume and boundary-nullity;
    3. slicing and monomial integrals;
    4. general simplex calculus and moment determination.
  - Check normalization constants mathematically before attempting tactic-level
    proofs.
  - When proving a difficult change-of-variables result, first test its critical
    steps as small `example`s.
