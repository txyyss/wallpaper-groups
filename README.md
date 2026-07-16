# wallpaper-groups

A Lean 4 + mathlib formalization of the algebraic classification of plane wallpaper groups.

## Classification object

The formal object `PlaneGroup` is a subgroup of Euclidean motions whose full translation
subgroup is exactly a stored rank-two integer lattice and whose point group is finite.  This is
the strong algebraic definition used on the critical path of the classification; the separate
discrete-and-cocompact characterization is post-v1 work.

Two plane groups are equivalent when there is an abstract group isomorphism that maps the full
translation subgroup onto the full translation subgroup (`TranslationPreservingIso`).  The
classification is therefore **not** classification up to Euclidean conjugacy, affine isometry,
or preservation of the chosen lattice basis.

## The 17 types

`WallpaperType` has exactly the standard 17 constructors, grouped by the number of reflection
families in the point group:

- no reflections: `p1`, `p2`, `p3`, `p4`, `p6`;
- one reflection: `cm`, `pm`, `pg`;
- multiple reflections: `cmm`, `pmm`, `pmg`, `pgg`, `p3m1`, `p31m`, `p4m`, `p4g`, `p6m`.

The exported models have transparent finite-coset normal forms.  Their full translation
lattices and finite point groups are proved from those normal forms rather than inferred from
drawings or an unproved list of generators.

The main theorem is:

```lean
theorem classification (G : PlaneGroup) :
  ∃! w : WallpaperType,
    PlaneGroup.Equivalent G (WallpaperType.model w)
```

The quotient of `PlaneGroup` by this equivalence is also proved equivalent to `WallpaperType`,
and consequently has cardinality 17.  The three component classifications are the `5 + 3 + 9`
theorems in `Classification/NoReflections.lean`, `Classification/OneReflection.lean`, and
`Classification/MultipleReflectionInequivalence.lean`; the global theorem is in
`Classification/Wallpaper.lean`.

## Building

With the pinned Lean toolchain and mathlib dependency available, run:

```text
lake build
```

Milestone status, proof architecture decisions, and the final human-review checklist are in
`docs/PROGRESS.md`, `docs/FOUNDATION_DECISIONS.md`, and `docs/M7_REVIEW.md`.
