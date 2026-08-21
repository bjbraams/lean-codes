# Project instructions

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
