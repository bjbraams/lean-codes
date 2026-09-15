# Palomar snapshot preparation

The registry-facing statement is [Statement.lean](Statement.lean). Its 21 selected
theorems represent all five mathematical libraries; it is not a complete index
of the repository's declarations. The exact public Git commit identifies the
whole submitted source snapshot, while [comparator.json](comparator.json)
identifies the particular formal claims to be compared.

## Statement and solution separation

Palomar accepts `Statement` as the Challenge module name. The conventional
name is `Challenge`, but it is not required.
The statement imports only Mathlib and spells out all project-specific notions
needed to read the claims. No project-specific imports are permitted, including
transitive imports. The statement is below the 300-line advisory
threshold and the 1,000-line / 100-KiB hard limits.

The intended 22 placeholders are confined to Statement: 21 advertised theorems
and the construction of `PalomarSnapshot.regR`. The latter is listed in
`definition_names`; joint holomorphy and native agreement characterize it on
the slit domain. Its solution is the existing `regCarlsonRSlit`, not an
arbitrary function satisfying only functional equations. The elementary measure,
density, and average definitions have explicit bodies in both modules.

[Solution.lean](Solution.lean) imports the five proof libraries, never Statement.
It repeats the same declarations and supplies their proofs. Keep these modules
separate: importing both would both duplicate names and undermine the intended
statement/proof separation. No mathematical library should import either wrapper.

The two wrappers are separate Lake library targets. Existing default targets
and the intentional local-disk `.lake` symlink are unchanged. Thus an ordinary
`lake build` checks the mathematical development; run the additional command
below to check the submission targets too.

## Selected results and proof locations

Names below are in the `PalomarSnapshot` namespace. The exact project theorem
names are visible in the short proofs in Solution.

| Selected declarations | Existing proof modules |
| --- | --- |
| gamma_shift, vandermonde | Pochhammer/Gamma.lean; Pochhammer/Vandermonde.lean |
| holomorphic_analytic, osgood, cauchy_derivatives | SeveralComplexVariables/Basic.lean; Osgood.lean; CauchyDerivatives.lean |
| simplex_chart_independent, simplex_monomial | StdSimplexMeasure/Measure/Basic.lean; Integral/Monomial.lean |
| complex_beta_integral | Dirichlet/Integral/Complex.lean |
| dirichlet_probability, dirichlet_moments, dirichlet_aggregation | Dirichlet/Real.lean; Real/Moments.lean; Real/Aggregation.lean |
| joint_average_continuation | Dirichlet/Average/JointContinuation.lean |
| r_joint, r_native | Carlson/R/SlitJointAnalytic.lean; SlitIntegral.lean |
| r_euler, r_euler_poisson | Carlson/R/EulerTransform.lean; EulerPoisson.lean |
| r_first_quadratic, r_second_quadratic | Carlson/TwoVariable/QuadraticSlit.lean |
| l_joint, l_native, l_exponent_derivative | Carlson/L/SlitContinuation.lean; SlitIntegral.lean |

The ordinary R and L normalizations at Gamma poles, unrestricted quadratic
branch components, general simply connected continuation of arbitrary averages,
Carlson's contour formula 6.8-7, and complete coverage of the L article are
not advertised. Neither are the wider S/T, recurrence, boundary-limit, or SCV
developments registered as separate compared claims in this selection.
They remain part of the source snapshot when committed.

## Local validation

From the project root:

```sh
lake build
lake build Statement Solution
lake env lean Statement.lean
lake env lean Solution.lean
git diff --check
rg -n '\bsorry\b' Statement.lean Solution.lean Pochhammer SeveralComplexVariables StdSimplexMeasure Dirichlet Carlson
```

Statement's placeholder warnings are expected. Solution and the five mathematical
libraries must have no admissions. The upstream metadata convention excludes
intentional Challenge placeholders from `status.sorry_count`.

The local preparation also checked the metadata against the official v0.4 JSON
Schema and audited all 21 solution theorems and the R construction: only
`propext`, `Quot.sound`, and `Classical.choice` occur. Local fingerprints of the
elaborated declaration types, universe parameters, and the fixed definition
bodies agree between the two environments. In particular, keep the explicit
`[Fintype ι]` binder on the R construction in both files: Lean otherwise drops
it from a placeholder whose body does not use it.

Local Lean checking and axiom audits are not a substitute for Comparator.
Comparator, lean4export, and NanoDa were not found on PATH during preparation;
no official Comparator or independent-kernel pass is claimed. Palomar's verifier
will perform its own checks on the selected immutable commit.

## Before submission

1. Review the selection and the provenance in [formalization.yaml](formalization.yaml).
   It now records responsible maintenance, classifications, source relationships,
   scope limitations, and the known automation/review history. Historical model
   versions and costs are not invented.
2. Include the root [LICENSE](LICENSE), containing the standard Apache License
   2.0 text from the Apache Software Foundation and matching the metadata's
   `Apache-2.0` declaration.
3. Review and commit the entire intended source snapshot, including the two new
   Lean files, Comparator configuration, metadata, Lakefile, and pinned manifest.
   No commit or push has been made by this preparation.
4. Push that commit to a public GitHub repository. Submit its full 40-character
   SHA and the root `comparator.json` to Palomar.
5. Complete the external verification and review before registering the result.

The reference-PDF directories and `.lake` are intentionally ignored by Git.
Do not force-add them merely to make a directory snapshot: the dependencies are
reconstructed from the manifest, and cited third-party publications are not
automatically covered by the project's licence. Coverage Markdown files other
than the public guides are also currently ignored; the submitted statement and
metadata include the limitations needed to read this selection without them.

## Requirements consulted

Checked on 2026-09-15:

- [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Submission guide](https://palomar-registry.org/how-to-submit)
- [Official Challenge/Solution template](https://github.com/PalomarRegistry/PalomarTemplate)
- [Comparator, including definition holes](https://github.com/leanprover/comparator)
- [formalization.yaml standard](https://github.com/mathlib-initiative/formalization.yaml)

The policy and tooling can change; recheck them before submitting.
