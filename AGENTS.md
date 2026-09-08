# Project instructions

## Build topology (do not change)

- Lake root is this directory: ~/lean-codes. This directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not repair it.
- After every Lean edit: `lake build` from the Lake root.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.
- Active work: StdSimplexMeasure/

## Project

This is a collection of Lean 4 projects using Mathlib and written with the
intent to form a contribution to Mathlib.

## Proof requirements

- All proofs must be accepted by Lean.
- Do not introduce axioms.
- Do not replace `sorry` with `by exact Classical.choice ...` or other
  logically equivalent escape mechanisms.
- Search Mathlib for existing results before recreating substantial theory.
- Additional lemmas are welcome when they clarify the mathematical structure.
- Preserve theorem statements unless they are false or require missing
  assumptions.
- If a statement appears false then mark the issue clearly before changing it.
- Pay particular attention to empty, singleton, and nontrivial index types.

## Editing

- Keep changes narrowly related to the requested theorem or proof cluster.
- Preserve unrelated user changes.
- Temporary experiments may go in `Scratch.lean`, but remove that file before
  finishing unless asked to retain it.
- Do not commit changes unless explicitly requested.

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
