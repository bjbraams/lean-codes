# Palomar snapshot preparation

The registry-facing statement is [Statement.lean](Statement.lean).
[comparator.json](comparator.json) now selects 10 Carlson/Dirichlet-average
continuation theorems and one R-function construction. The two Lean wrappers
are unchanged and still contain 21 theorem declarations; the other 11 describe
supporting material and are not separately selected claims. The exact public
Git commit identifies the whole source snapshot, including all five mathematical
libraries. The [README](README.md#mathematical-scope-and-research-interest)
explains the selected mathematical subject, research audience, and provenance.

## Statement and solution separation

Palomar accepts `Statement` as the Challenge module name. The conventional
name is `Challenge`, but it is not required.
The statement imports only Mathlib and spells out all project-specific notions
needed to read the claims. No project-specific imports are permitted, including
transitive imports. The statement is below the 300-line advisory
threshold and the 1,000-line / 100-KiB hard limits.

The intended 22 placeholders are confined to Statement: 21 theorem declarations
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
| joint_average_continuation | Dirichlet/Average/JointContinuation.lean |
| r_joint, r_native | Carlson/R/SlitJointAnalytic.lean; SlitIntegral.lean |
| r_euler, r_euler_poisson | Carlson/R/EulerTransform.lean; EulerPoisson.lean |
| r_first_quadratic, r_second_quadratic | Carlson/TwoVariable/QuadraticSlit.lean |
| l_joint, l_native, l_exponent_derivative | Carlson/L/SlitContinuation.lean; SlitIntegral.lean |

The retained but unselected wrapper theorems are `gamma_shift`, `vandermonde`,
`holomorphic_analytic`, `osgood`, `cauchy_derivatives`,
`simplex_chart_independent`, `simplex_monomial`, `complex_beta_integral`,
`dirichlet_probability`, `dirichlet_moments`, and `dirichlet_aggregation`.
Their proofs and the supporting libraries have not been removed or replaced
by Mathlib imports. Foundational source credits, including Boas, remain in
[formalization.yaml](formalization.yaml).

The quadratic source relationship is explicitly `adapts`: the formulas use
Gamma regularization and all complex parameters on Carlson's stated
positive-real-part unsquared-variable domain. The slit-plane transformed nodes
are already part of Carlson 6.9-3 and 6.10-1, not a new extension beyond those
book statements. See the [detailed account](README.md#quadratic-transformations-precise-relationship-to-carlson).

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
The maintainer reports that the preceding submission passed Palomar mechanical
verification. Editorial review did not offer registration: it found inadequate
research-interest justification for separately selected foundational families
and an insufficient account of the quadratic adaptations. This revision changes
only Comparator selection and documentation, not Lean declarations or proofs.
The new immutable snapshot still requires external verification and editorial
review; the previous mechanical success is not a registration or an endorsement.

## Before submission

1. Review the selection and the provenance in [formalization.yaml](formalization.yaml).
   It now records responsible maintenance, classifications, source relationships,
   scope limitations, and the known automation/review history. Historical model
   versions and costs are not invented.
2. Include the root [LICENSE](LICENSE), containing the standard Apache License
   2.0 text from the Apache Software Foundation and matching the metadata's
   `Apache-2.0` declaration.
3. Review and commit the revised Comparator configuration, metadata, README,
   and this guide. Keep the existing Lean files, Lakefile, and pinned manifest.
   No commit or push is made by this revision.
4. Push that commit to a public GitHub repository. Submit its full 40-character
   SHA and the root `comparator.json` to Palomar. Leave the existing Palomar ID
   blank: the preceding submission was not registered.
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
