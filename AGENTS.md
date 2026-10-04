# Project instructions

## Build topology (do not change)

- Lake root is this directory: ~/lean-codes. This directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- That lake directory is shared with the companion projects (lean-SCV, lean-CA, lean-AAR,
  lean-LCS). They share `.lake/packages` (all pin the same Mathlib), but this project writes
  its own build outputs to `.lake/build-codes` (`buildDir` in `lakefile.toml`), because Lake's
  build traces include the package name and modules with equal names (`ComplexAnalysis.*`,
  `SeveralComplexVariables.*`, `ToMathlib.*`) would otherwise overwrite each other. Keep that
  `buildDir` setting; never write to or delete another project's build directory.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not repair it.
- After every Lean edit: `lake build` from the Lake root.
- For ordinary builds, use lake build > /tmp/carlson-build.log 2>&1; reuse this filename to preserve the existing command approval.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.
- Active work: StdSimplexMeasure/ or Dirichlet/ or Carlson/ or Pochhammer/

## Project

This is a collection of Lean 4 projects using Mathlib and written with the
intent to form a contribution to Mathlib.

## Proof requirements

- All proofs must be accepted by Lean.
- Do not introduce axioms.
- Do not replace `sorry` with `by exact Classical.choice ...` or other
  logically equivalent escape mechanisms.
- Search Mathlib first, then the pinned TauCeti modules, before developing substantial
  local theory. Follow the upstream reuse policy below.
- Additional lemmas are welcome when they clarify the mathematical structure.
- Preserve theorem statements unless they are false or require missing
  assumptions.
- If a statement appears false then mark the issue clearly before changing it.
- Pay particular attention to empty, singleton, and nontrivial index types.

## Upstream reuse policy

The order of preference is **Mathlib, then the pinned TauCeti, then local project code**.
Apply this policy to all seven project layers, including simplex, Dirichlet and Carlson theory.

- Use a suitable Mathlib result before a TauCeti or local version.
- Import the specific TauCeti module supplying a suitable result before developing a local
  proof. Prefer imports to copied upstream proofs; `import TauCeti` is not a library umbrella.
- Compare hypotheses and conclusions and check for namespace conflicts. Preserve generality:
  do not strengthen assumptions simply to fit an upstream theorem. Check empty and singleton
  index types, Banach-valued targets, complex parameters, and boundary cases.
- Remove redundant local proofs when adopting upstream results. Small adapters may preserve
  useful local interfaces without duplicating the mathematical proof.
- Credit imported results in module headers and at their point of use; record adoption in
  `CREDITS.md`. Resolve TauCeti prerequisites when preparing a Mathlib contribution.
- Keep TauCeti pinned to the compatible revision in `lakefile.toml`; preserve the common
  Mathlib pin and the toolchain unless an update is requested.

Mathlib and TauCeti are allowed external dependencies in every layer. Preserve the local
import hierarchy: `ToMathlib` imports no application or complex-analysis layer;
`ComplexAnalysis` does not import `SeveralComplexVariables`; neither complex-analysis layer
imports the simplex or application layers; simplex foundations do not import Dirichlet or
Carlson, and Dirichlet does not import Carlson.

The shared package checkout does not itself register a dependency in a companion project.
For copied sources, apply the master-copy rules below and validate affected primary projects.

## Editing

- Keep changes narrowly related to the requested theorem or proof cluster.
- Preserve unrelated user changes.
- Temporary experiments may go in `Scratch.lean`, but remove that file before
  finishing unless asked to retain it.
- Do not commit changes unless explicitly requested.
- If a new Lean file is created, provide it with a documentation header section.
- If a new Lean statement (definition, theorem, lemma or other) is introduced,
  provide it with a brief docstring.
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

## Validation

For any lean file `f.lean` that has been changed, run:

    lake env lean f.lean

Also run:

    git diff --check
    rg -n '\bsorry\b' ...

## Completion report

Report:

- which theorems were proved;
- which `sorry`s remain;
- validation commands and their results;
- any changed assumptions;
- any theorem found or suspected to be false.

## Documentation files

Do not create dedicated documentation files or any other Markdown files in subdirectories.
Such files should go into the main project directory at the top level.
This includes Markdown files that provide a review of project updates or that describe
planned work.

Files README.md and STRUCTURE.md are intended as public documentation, with README.md as
the entry point for the reader and STRUCTURE.md for more detailed description.

File REMINDERS.md is intended for private documentation for the owner or other editors.
