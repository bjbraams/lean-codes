# Project instructions — lean-codes

Before working, read and follow [the shared Lean instructions](AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-codes`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/carlson-build.log 2>&1`.
- Active work: StdSimplexMeasure/ or Dirichlet/ or SimplexMellin/ or Carlson/ or Pochhammer/

## Project

This is a collection of Lean 4 projects using Mathlib and written with the
intent to form a contribution to Mathlib.

## Dependencies and import layers

Mathlib and TauCeti are allowed in all eight project layers, including simplex,
Dirichlet, simplex Mellin and Carlson theory. Preserve the local import hierarchy:
`ToMathlib` imports no application or complex-analysis layer; `ComplexAnalysis` does
not import `SeveralComplexVariables`; neither complex-analysis layer imports the simplex
or application layers; simplex foundations do not import Dirichlet, SimplexMellin or Carlson;
Dirichlet does not import SimplexMellin or Carlson; and SimplexMellin and Carlson, which both
build on Dirichlet, do not import each other. Follow the master-copy rules below and validate
affected primary projects.

## Project-specific editing

- Supporting code lives in `ToMathlib/Analysis`, `ToMathlib/Topology`, and
  `ToMathlib/Algebra` (modules `ToMathlib.Analysis.*` and so on), in the namespaces of the
  Mathlib APIs they extend.
- `ComplexAnalysis/` and `SeveralComplexVariables/` hold only the modules transitively needed by this
  project's application and support code. Compute this subset from substantive imports,
  excluding the two inventory umbrellas as dependency roots. They are exact copies of files
  in the primary projects
  `../lean-CA/ComplexAnalysis` and `../lean-SCV/SeveralComplexVariables`; do not edit them here.
  Make changes in the primary project and copy the files back, and when a new dependency is
  needed, copy the module (with its imports) from the primary project. Remove modules that are
  no longer used. The root `ComplexAnalysis.lean` and `SeveralComplexVariables.lean` umbrellas
  describe this project's subset and are not copies of the primary-project umbrellas. Verify
  byte-for-byte equality of every retained implementation file. A `ToMathlib` file that also
  exists in lean-CA or lean-SCV must have
  identical content and path; the umbrella files `ToMathlib/Analysis.lean`,
  `ToMathlib/Topology.lean`, and `ToMathlib/Algebra.lean` are project-specific.

## Documentation files

Files README.md and STRUCTURE.md are intended as public documentation, with README.md as
the entry point for the reader and STRUCTURE.md for more detailed description.
