Review status: awaiting human approval

# M8c-b translation-lattice recovery review

M8c-b recovers the complete rank-two translation lattice of every geometric wallpaper group.
It uses the M8c-a finite point group and finite-index kernel results without changing them.
It does not construct a `PlaneGroup`, prove choice independence of that future construction, or
begin M8c-c.

## Production implementation

The new implementation is
`WallpaperGroups/Geometry/TranslationLatticeRecovery.lean`, imported by
`WallpaperGroups.lean`.

No Version 1 classification file, `PlaneGroup` definition, M8b geometric definition, or M8c-a
production declaration is modified.

## Translation cocompactness transfer

```lean
theorem MotionSubgroup.exists_compact_translation_representatives
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)]
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    ∃ K : Set Plane, IsCompact K ∧
      ∀ x : Plane,
        ∃ t : (translationVectors Γ).toIntSubmodule,
          (t : Plane) + x ∈ K
```

Starting from a compact set `K₀` meeting every `Γ`-orbit, the proof chooses one lift for each
element of the finite point group and takes the finite union of the inverse-lift images of
`K₀`.  If `γ` moves `x` into `K₀`, cancellation against the chosen lift of
`pointProjection Γ γ` leaves an element of the translation kernel.  The existing exact-sequence
API converts that kernel element into an actual translation vector.

The chosen lifts are eliminated inside this existence proof.  They are not exported and do not
define an invariant.

## Translation-module discreteness

```lean
theorem MotionSubgroup.translationModule_discreteTopology
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ) :
    DiscreteTopology (translationVectors Γ).toIntSubmodule
```

For every compact `K`, proper discontinuity makes finite the group elements that move `{0}` to
meet `K`.  The pure-translation map from the integer translation module to `Γ` is injective, so
the natural inclusion of that module into the plane has finite preimage on every compact set.
Mathlib's `tendsto_cofinite_cocompact_iff` and
`Continuous.discrete_of_tendsto_cofinite_cocompact` then give the induced discrete topology.

This theorem uses discreteness alone; it does not assume cocompactness or a pre-existing lattice.

## Full-span theorem

```lean
theorem MotionSubgroup.span_eq_top_of_compact_translation_representatives
    (L : Submodule ℤ Plane) (K : Set Plane)
    (hK : IsCompact K)
    (hrepresentatives :
      ∀ x : Plane, ∃ t : L, (t : Plane) + x ∈ K) :
    Submodule.span ℝ (L : Set Plane) = ⊤

theorem MotionSubgroup.translationModule_span_eq_top
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)]
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    Submodule.span ℝ
      ((translationVectors Γ).toIntSubmodule : Set Plane) = ⊤
```

The proof follows the approved orthogonal-complement route.  If the real span `W` were proper,
choose a nonzero vector in `Wᗮ` and normalize it to a unit vector `v`.  All lattice translations
have zero component along `v`.  A compact representative for `(R + 1) • v`, where `R` bounds
the norm on `K`, would therefore have inner product `R + 1` with `v` while having norm at most
`R`, a contradiction.  This single argument excludes both rank zero and rank one.

## Recovered rank-two lattice

```lean
noncomputable def MotionSubgroup.recoveredTranslationLattice
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    RankTwoLattice Plane

@[simp]
theorem MotionSubgroup.recoveredTranslationLattice_carrier
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    (MotionSubgroup.recoveredTranslationLattice Γ hdisc hcoc).carrier =
      (translationVectors Γ).toIntSubmodule

noncomputable def GeometricWallpaperGroup.translationLattice
    (X : GeometricWallpaperGroup) :
    RankTwoLattice Plane

@[simp]
theorem GeometricWallpaperGroup.translationLattice_carrier
    (X : GeometricWallpaperGroup) :
    X.translationLattice.carrier =
      (translationVectors X.carrier).toIntSubmodule
```

The discreteness and full-span theorems produce a mathlib `IsZLattice`; the approved
`RankTwoLattice.ofZLattice` adapter then supplies the project's framed lattice.  Its
`Classical.choose` basis is noncanonical construction data.  The public carrier theorems are
the stable conclusions and identify the recovered object with the complete translation
subgroup, not with a chosen pair of generators.

Bundled geometric-group wrappers also expose the discrete-topology and full-span results
directly.

## M8c-c work not started

M8c-c still must:

- construct the exact strong `PlaneGroup` from the unchanged motion carrier, the recovered
  translation lattice, and the M8c-a finite point group;
- prove that changing noncanonical basis data changes only framing, using
  `PlaneGroup.Equivalent` and then the M8a textbook equivalence;
- prove strong/geometric round-trip compatibility;
- derive the unique 17-class geometric classification theorem.

No recovered `PlaneGroup`, conversion function, round-trip theorem, or geometric classification
theorem is introduced in M8c-b.

## Items for human review

- The finite-point-group transfer has the correct multiplication direction and yields the full
  translation kernel rather than a selected finite-index sublattice.
- The compact-preimage argument proves the induced topology on the actual integer translation
  module is discrete.
- The orthogonal-complement contradiction uses exactly compact translation representatives and
  rules out every proper real span.
- Only carrier equality, not the basis selected by `RankTwoLattice.ofZLattice`, is presented as
  stable mathematical data.
- The implementation stops before M8c-c and leaves all approved Version 1 and M8b definitions
  unchanged.

## Validation

- `lake env lean WallpaperGroups/Geometry/TranslationLatticeRecovery.lean`: passed with no
  warnings.
- `lake build`: passed (`2879` jobs).
- `git diff --check`: passed.
- The project Lean-source scan found no `sorry`, `admit`, `axiom`, or `unsafe`.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged.
- `WallpaperGroups/Basic/PlaneGroup.lean`,
  `WallpaperGroups/Geometry/GeometricWallpaperGroup.lean`, the M8c-a production module, and all
  Version 1 classification files are unchanged.
