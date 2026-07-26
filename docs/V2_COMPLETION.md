# Version 2 M8 geometric bridge completion

## Status and scope

Version 2 milestone M8 is complete and has passed human specification review.
The `v2-complete` tag records the stable completion of the two-dimensional
geometric bridge.

This completion marker is deliberately scoped to M8.  The active
[`ROADMAP_V2.md`](ROADMAP_V2.md) also contains the future M9 extension-theory
program; M9 has not started.  Nothing here claims a classification of
higher-dimensional space groups, a general Bieberbach theorem, or a verified
space-group enumerator.

## Version 1 baseline

Version 1 classifies the strong algebraic objects:

```lean
structure PlaneGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  translationLattice : RankTwoLattice Plane
  translationLattice_carrier :
    translationLattice.carrier =
      (translationVectors carrier).toIntSubmodule
  pointGroup_finite : Finite (pointGroup carrier)
```

Its equivalence is an abstract group isomorphism carrying the complete
translation subgroup onto the complete translation subgroup:

```lean
def PlaneGroup.Equivalent (G H : PlaneGroup) : Prop :=
  Nonempty (TranslationPreservingIso G H)
```

The main Version 1 theorem is:

```lean
theorem classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.Equivalent G (WallpaperType.model w)
```

The quotient of `PlaneGroup` by this relation is equivalent to
`WallpaperType` and has cardinality 17.

## M8a: textbook motion-type equivalence

M8a defines exact predicates for translations, rotations, reflections, and
glide reflections, including the convention that the identity is the zero
translation and is not a rotation.

It defines an abstract isomorphism preserving all four motion types and proves:

```lean
theorem PlaneGroup.textbookEquivalent_iff_equivalent
    (G H : PlaneGroup) :
    PlaneGroup.TextbookEquivalent G H ↔
      PlaneGroup.Equivalent G H
```

Consequently the existing 17-class theorem also holds under the textbook
motion-type relation:

```lean
theorem textbook_classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.TextbookEquivalent G (WallpaperType.model w)
```

Neither relation is Euclidean conjugacy.  No ambient affine conjugating map or
metric-preservation condition is part of the classification.

## M8b: strong groups are geometric

The geometric object is:

```lean
structure GeometricWallpaperGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  isDiscrete : MotionSubgroup.IsDiscrete carrier
  isCocompact : MotionSubgroup.IsCocompact carrier
```

Here discreteness is `ProperlyDiscontinuousSMul` in its compact-set
finite-intersection form.  Cocompactness means that a compact subset of the
plane has translates covering the plane; this is also proved equivalent to
compactness of the orbit quotient.

M8b proves that every strong plane group satisfies these geometric conditions
and packages the result without changing its carrier:

```lean
def PlaneGroup.toGeometricWallpaperGroup
    (G : PlaneGroup) : GeometricWallpaperGroup
```

The proof uses the stored rank-two translation lattice, a compact fundamental
parallelogram, and finiteness of the point group.

## M8c: geometric groups are strong

M8c proves the converse from only proper discontinuity and cocompactness:

- the point group is finite;
- the full pure-translation subgroup is discrete;
- compact translation representatives force its real span to be the whole
  plane;
- the translation module therefore gives a complete `RankTwoLattice Plane`;
  and
- the original motion carrier can be packaged as a strong `PlaneGroup`.

The conversion is:

```lean
noncomputable def GeometricWallpaperGroup.toPlaneGroup
    (X : GeometricWallpaperGroup) : PlaneGroup
```

with exact carrier equality:

```lean
@[simp]
theorem GeometricWallpaperGroup.toPlaneGroup_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.carrier = X.carrier
```

The recovered integer basis is noncanonical construction data.  Choice
independence is stated only through the approved equivalence:

```lean
theorem GeometricWallpaperGroup.toPlaneGroup_choice_independent
    (X : GeometricWallpaperGroup) (G : PlaneGroup)
    (hcarrier : G.carrier = X.carrier) :
    PlaneGroup.Equivalent G X.toPlaneGroup
```

The strong and geometric round trips preserve the appropriate equivalence
classes rather than claiming equality of structures with chosen proof or basis
fields.

## Direct geometric classification

The final geometric relation is defined directly on geometric motion carriers:

```lean
def GeometricWallpaperGroup.TextbookEquivalent
    (X Y : GeometricWallpaperGroup) : Prop :=
  Nonempty
    (GeometricWallpaperGroup.MotionTypePreservingIso X Y)
```

The isomorphism explicitly preserves and reflects all four M8a motion
predicates.  It contains no recovered basis, compact-cover witness, ambient
conjugacy, or metric datum.

This direct relation agrees with the strong relation after conversion:

```lean
theorem GeometricWallpaperGroup.textbookEquivalent_iff_equivalent
    (X Y : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent X Y ↔
      PlaneGroup.Equivalent X.toPlaneGroup Y.toPlaneGroup
```

The geometric 17-class theorem is:

```lean
theorem geometric_classification (X : GeometricWallpaperGroup) :
    ∃! w : WallpaperType,
      GeometricWallpaperGroup.TextbookEquivalent
        X w.geometricModel
```

Its proof is a conversion-layer corollary of the Version 1/M8a classifier; it
does not repeat the `5 + 3 + 9` classification.  The quotient by direct
geometric textbook equivalence is also proved equivalent to `WallpaperType`
and has cardinality 17.

## Main implementation and review files

- M8a:
  [`WallpaperGroups/Geometry/MotionType.lean`](../WallpaperGroups/Geometry/MotionType.lean)
- M8b:
  [`WallpaperGroups/Geometry/GeometricWallpaperGroup.lean`](../WallpaperGroups/Geometry/GeometricWallpaperGroup.lean)
  and
  [`WallpaperGroups/Geometry/StrongToGeometric.lean`](../WallpaperGroups/Geometry/StrongToGeometric.lean)
- M8c:
  [`WallpaperGroups/Geometry/GeometricToStrong.lean`](../WallpaperGroups/Geometry/GeometricToStrong.lean),
  [`WallpaperGroups/Geometry/TranslationLatticeRecovery.lean`](../WallpaperGroups/Geometry/TranslationLatticeRecovery.lean),
  and
  [`WallpaperGroups/Geometry/GeometricClassification.lean`](../WallpaperGroups/Geometry/GeometricClassification.lean)
- Reviews:
  [`M8C_DESIGN_REVIEW.md`](M8C_DESIGN_REVIEW.md),
  [`M8C_A_REVIEW.md`](M8C_A_REVIEW.md),
  [`M8C_B_REVIEW.md`](M8C_B_REVIEW.md), and
  [`M8C_C_REVIEW.md`](M8C_C_REVIEW.md)

## Future M9 direction

M9 is a separate extension-theory track:

- M9a will interpret existing finite-coset factor sets and quotient-valued
  shift classes through normalized cocycles, coboundaries, section changes,
  and naturality.
- M9b may extract a dimension-independent explicit extension theory for a
  group acting on an abelian group, including twisted products and
  endpoint-preserving extension equivalence.

The intended future use is infrastructure for a possible verified
higher-dimensional space-group enumerator.  Such an enumerator would
additionally require integral point-group enumeration, lattice/action
certificates, orbit and normalizer algorithms, and dimension-specific
classification data.  None of those are implemented by the M8 geometric
bridge.
