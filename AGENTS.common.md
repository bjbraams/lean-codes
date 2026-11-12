# Shared Lean project instructions

These instructions are shared by `lean-CA`, `lean-SCV`, `lean-LCS`, `lean-DLMF`
(formerly `lean-AAR`), `lean-codes`, and `lean-PR`. Each project's root `AGENTS.md`
explicitly directs the agent to read this file. This file is maintained in `lean-codes`;
edit it there rather than copying its rules into the other projects.

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
- Each `lakefile.toml` sets `autoImplicit = false` and `relaxedAutoImplicit = false` under
  `[leanOptions]` (the Mathlib convention), so undeclared names are errors rather than
  auto-bound implicits. Declare every variable explicitly.
- `lake build <Module>` is the authoritative check: it applies the package's `[leanOptions]`,
  including linter sets and `warningAsError`. `lake env lean` applies none of them. For a quick
  single-file check, pass the relevant options with `-D`, for example
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
  -Dlinter.unusedVariables.analyzeTactics=true -DwarningAsError=true f.lean`.
  Style linters (line length, file length, flexible tactics, `show`) are reliably caught
  only by `lake build`.
- When an upstream project changes its `[leanOptions]`, re-check every open branch against
  the new options, not just the branch being worked on.

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
- Credit imported or adapted work in module headers (the module docstring, not only the PR
  description) and at the point of use; record
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

## Code intended for Mathlib or TauCeti

These rules record what the Mathlib linters and the TauCeti review rubrics enforce. Apply them
to code meant for either library, including code being ported from these projects.

- **Unused names.** Delete unused hypotheses, and drop the `with h` from `set … with h` when
  `h` is never used. If a tactic needs a fact without naming it (`nlinarith`, `field_simp`),
  pass it explicitly (`nlinarith [h]`) rather than renaming it to `_h`.
- **Tactic hygiene.**
  - Do not restate goals with `show` or `change`; use `dsimp only`, `simp only [defs]` or
    `calc`, or comment on why the change is needed.
  - Do not leave a `ring` that only `ring_nf` closes (it prints "Try this", which CI rejects).
  - Do not follow a non-terminal `simp` with a flexible tactic; use `simp only [...]` or make
    the `simp` terminal.
- **Layout.** Lines of at most 100 characters, files of at most 1500 lines, and spaces around
  binary operators (`(a + n)`, not `(a+n)`).
- **Module system.**
  - Use `public import` only for what the statements need, and plain `import` for proof-only
    dependencies.
  - Do not put a blanket `@[expose]` on a section.
  - Give each definition a defining lemma (`_def` or an iff) plus introduction and
    elimination lemmas, so users never depend on unfolding it.
- **Generality.**
  - State results over the most general setting the proof allows: `[Field K] [CharZero K]`
    instead of `ℂ`, `[CommRing R] [IsDomain R]`, values in a normed space `E`.
  - Take the weakest natural hypotheses, for example "meromorphic at `p`" rather than
    "simple pole", or "off the poles" rather than `0 < re c`.
- **Placement and reuse.**
  - A helper whose statement does not mention the file's topic is not `private`. Export it
    from the lowest module it fits, such as `Gamma/Basic` or `Pochhammer`.
  - Before proving a bridge lemma, search Mathlib and the pinned TauCeti for it (for example
    Mathlib's `mellinInv_eq_fourierInv`).
  - Drop imports that come in transitively anyway, and do not add thin wrapper lemmas.
- **Naming.** Follow Mathlib: `natCast` in names, dot-notation namespaces such as
  `ContinuousOn.foo`, and no `_of_pos` copies of a lemma that already holds in general.
- **Documentation.** Every public declaration gets a docstring, and the module docstring
  lists the main results. A docstring must be accurate about degenerate cases.
- **Attribution.** Credit ported sources, such as lean-DLMF, in the module docstring itself,
  not only in the PR description.
- **Shared files across parallel PRs.** When two open PRs edit the same module, insert at
  different places in it. For an open PR, merge main into the branch instead of rebasing, so
  pushes stay fast-forward. Check with `git merge-tree --write-tree origin/main <branch>`
  before pushing.

## Validation and completion report

For each changed Lean file, run `lake build` on its module, which applies the package's
linter options, and run
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false path/to/File.lean` from the
project root after building its imports, adding `-D` flags for any further `[leanOptions]`
the package sets (see Build topology). Also run `git diff --check` and scan affected Lean
sources with `rg -n '\bsorry\b' ...`. Retain local axiom-audit and entry-module checks.
For documentation-only edits, check the documentation and diff; no Lean build is needed.

Report which theorems were proved, which admissions remain, validation commands and
results, any changed assumptions, and any false or suspected-false theorem. Scale
this report to the task; documentation-only work does not require a theorem inventory.

## Documentation and maintenance

- Put new Markdown documentation at the project root, not in subdirectories.
- Do not use Tables in Markdown files. If a tabular presentation is a candidate, use a
  list or an itemized list instead.
- Do not use the operatorname command in Markdown files; use \mathop{\mathrm{V}} instead.
- `README.md` is the public entry point. Follow the local file roles for detailed
  reviews, structure and mathematical summaries. `REMINDERS.md`, where used, is private
  documentation for the owner and editors.
- Put changes common to the several projects in this shared file; put project-specific
  settings, scope, mathematical conventions and exceptions in the local `AGENTS.md`.
- The sibling checkout of `lean-codes` is needed to read these shared instructions.
  For an isolated checkout, provide that file and update the local reading path.
  Do not assume a Markdown link is an automatic include or silently ignore a missing file.
