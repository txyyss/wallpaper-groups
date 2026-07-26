# Instructions for Codex

Read `docs/ROADMAP.md`, `docs/ROADMAP_V2.md`, `docs/PROGRESS.md`, and
`docs/references/PAPER_GUIDE.md` before editing code.  `docs/ROADMAP.md` is the
completed Version 1 record; `docs/ROADMAP_V2.md` is the active normative plan.

The active task is the first unchecked milestone in `docs/PROGRESS.md`. Work
only on that milestone unless the user explicitly changes the scope.

Operational rules:

- Inspect the current repository and current mathlib APIs before defining foundational structures.
- Do not assume identifier names from the roadmap; verify them with compiling `#check` experiments and source search.
- Keep the branch buildable with `lake build`.
- Do not commit `sorry`, `admit`, new axioms, or opaque placeholders.
- Prefer thin wrappers over duplicated foundations.
- Keep public definitions stable and coordinate-free where practical; use `ℤ²` matrices internally for classification.
- Do not introduce general group cohomology into the critical path.
- Do not start the discrete/cocompact bridge before the 17-class theorem is complete.
- Add docstrings to exported declarations and update `docs/PROGRESS.md` when acceptance criteria are met.
- Use Conventional Commits for commit messages (for example, `feat:`, `docs:`, or `chore:`).
- Record material design changes in a short decision note.

For each task, first provide a concise patch plan. At completion, report:

1. files changed;
2. declarations added or modified;
3. commands run and their results;
4. remaining blockers;
5. the next unchecked acceptance item.
