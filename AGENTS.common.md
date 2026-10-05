# Shared Lean project instructions

These instructions are shared by `lean-CA`, `lean-SCV`, `lean-LCS`, `lean-AAR`,
`lean-codes`, and `lean-PR`. Each project's root `AGENTS.md` explicitly directs the
agent to read this file. This file is maintained in `lean-codes`; edit it there
rather than copying its rules into the other projects.

Read the current project's `AGENTS.md` as well. Its specific rules and exceptions
take precedence over these shared defaults. “Project root” below always means the
root of the project being worked on, not the directory containing this shared file.
When moving to another project, read that project's local instructions too.

## Build topology (do not change)

- The project root is the Lake root and is on NFS. Run Lake commands from that root,
  never from a source subdirectory as if it were a package root.
- `.lake` must be a symlink to `/export/scratch1/braams/lean-codes-lake` on local disk.
  Never replace, delete, or retarget it, or copy Mathlib or `.lake` onto NFS (`$HOME`).
  If the link is missing or points elsewhere, stop and ask; do not repair it.
- The projects share `.lake/packages` but have separate build outputs. Keep the
  project's `buildDir` specified in its local `AGENTS.md` and `lakefile.toml`.
  Never write to or delete another project's build directory.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache directory unless asked.
- Do not change the Lean toolchain or dependency pins unless asked.
- After every Lean edit, run `lake build` from the project root. Use the exact
  ordinary build command in its local `AGENTS.md` to preserve command approvals.
- Without LSP/MCP, treat `lake build` output as the only proof-state evidence.
- `lake env lean f.lean` uses compiled imports. Rebuild changed upstream modules
  before checking their dependents; a direct file check alone is not a full build.

## Proof requirements and upstream reuse

- All completed proofs must be accepted by Lean. Do not introduce axioms or replace
  `sorry` with logical escape mechanisms such as `by exact Classical.choice ...`.
  Admitted statements are not completed proofs. Follow any local statement-acquisition policy.
- Preserve theorem statements unless they are false or require missing assumptions.
  Identify a false or suspected-false statement clearly before changing it.
- Pay particular attention to empty, singleton, and nontrivial index types, boundary
  cases, completeness hypotheses, and the generality of scalar and target spaces.
- Search Mathlib before developing substantial local theory. In projects permitting
  TauCeti, use the order **Mathlib → pinned TauCeti → local project code** throughout
  all layers. A local Mathlib-only rule, as in `lean-PR`, takes precedence.
- Prefer imports of specific upstream modules to copied proofs. `import TauCeti`
  is not a library umbrella. The shared checkout does not itself register a Lake
  dependency in another project or authorize changing that project's configuration.
- Compare definitions, hypotheses, conclusions and namespace conflicts before reuse.
  Preserve generality, complex branches, normalization, convergence regions and
  exceptional parameters; do not strengthen assumptions merely to fit an upstream result.
- Remove redundant local proofs and update callers when adopting upstream results.
  Small adapters may preserve useful interfaces without duplicating mathematics.
  Additional lemmas are welcome when they clarify mathematical structure.
- Credit imported or adapted work in module headers and at the point of use; record
  adoption in `CREDITS.md`. Retain any stricter project-specific attribution rules.
  Resolve TauCeti prerequisites when preparing a Mathlib contribution.
- Validate reuse with Lean. An upstream admission or roadmap entry is not a proved
  result. Check axiom dependencies before declaring an admission resolved.

## Editing and mathematical style

- Keep changes narrowly related to the task and preserve unrelated user changes.
- Do not commit changes unless explicitly requested.
- Temporary experiments may use `Scratch.lean`; remove it before finishing unless
  asked to retain it.
- Give each new Lean file a documentation header and each new declaration a brief
  docstring. Follow Mathlib naming, namespace and mathematical conventions, together
  with the current project's conventions and module-system requirements.
- Prefer suitable existing predicates, structures and general formulations. Treat
  references as mathematical guidance, subject to the project's scope and exclusions.
- Follow the local import hierarchy and rules for copying shared source files.
  When an authorized change affects a companion project, validate the affected projects.

## Validation and completion report

For each changed Lean file, run `lake env lean path/to/File.lean` from the project
root after building its imports. Also run `git diff --check` and scan affected Lean
sources with `rg -n '\bsorry\b' ...`. Retain local axiom-audit and entry-module checks.
For documentation-only edits, check the documentation and diff; no Lean build is needed.

Report which theorems were proved, which admissions remain, validation commands and
results, any changed assumptions, and any false or suspected-false theorem. Scale
this report to the task; documentation-only work does not require a theorem inventory.

## Documentation and maintenance

- Put new Markdown documentation at the project root, not in subdirectories.
- `README.md` is the public entry point. Follow the local file roles for detailed
  reviews, structure and mathematical summaries. `REMINDERS.md`, where used, is private
  documentation for the owner and editors.
- Put changes common to the six projects in this shared file; put project-specific
  settings, scope, mathematical conventions and exceptions in the local `AGENTS.md`.
- The sibling checkout of `lean-codes` is needed to read these shared instructions.
  For an isolated checkout, provide that file and update the local reading path.
  Do not assume a Markdown link is an automatic include or silently ignore a missing file.
