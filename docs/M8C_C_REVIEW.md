Review status: awaiting human approval

# M8c-c strong reconstruction and geometric classification review

M8c-c completes the converse geometric bridge.  Every geometric wallpaper group is converted
to a strong `PlaneGroup` with exactly the same motion subgroup, and the existing M7/M8a
classification is transported to a direct textbook equivalence on geometric wallpaper groups.

The implementation is
`WallpaperGroups/Geometry/GeometricClassification.lean`, imported by
`WallpaperGroups.lean`.

No Version 1 classification file, `PlaneGroup` definition, M8b geometric definition, M8c-a
point-group implementation, or M8c-b lattice-recovery implementation is modified.

## Geometric-to-strong conversion

```lean
noncomputable def GeometricWallpaperGroup.toPlaneGroup
    (X : GeometricWallpaperGroup) : PlaneGroup
```

Its fields are exactly:

```lean
{
  carrier := X.carrier
  translationLattice := X.translationLattice
  translationLattice_carrier := X.translationLattice_carrier
  pointGroup_finite := X.pointGroupFinite
}
```

The stable carrier statements are:

```lean
@[simp]
theorem GeometricWallpaperGroup.toPlaneGroup_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.carrier = X.carrier

@[simp]
theorem GeometricWallpaperGroup.toPlaneGroup_translationLattice_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.translationLattice.carrier =
      (translationVectors X.carrier).toIntSubmodule
```

Thus the conversion uses the complete pure-translation subgroup proved rank two in M8c-b, not
a chosen finite-index sublattice.  Point-group finiteness is exactly the M8c-a theorem.

## Choice independence

```lean
theorem PlaneGroup.equivalent_of_carrier_eq
    {G H : PlaneGroup}
    (h : G.carrier = H.carrier) :
    PlaneGroup.Equivalent G H

theorem GeometricWallpaperGroup.toPlaneGroup_choice_independent
    (X : GeometricWallpaperGroup) (G : PlaneGroup)
    (hcarrier : G.carrier = X.carrier) :
    PlaneGroup.Equivalent G X.toPlaneGroup
```

The first theorem uses `MulEquiv.subgroupCongr h`; its underlying map leaves every ambient
motion unchanged and maps the full translation kernel onto itself.  The second theorem says
that any valid strong package on the original geometric carrier is equivalent to the recovered
one.  It quantifies over the complete `PlaneGroup`, so it eliminates differences in lattice
basis, translation-carrier equality proof, finite-point-group proof, and other stored proof
fields.

No theorem claims that a `Classical.choose` basis is canonical, and no equality of
`PlaneGroup` structures is exported.

## Direct geometric textbook equivalence

The classified relation is stated directly on geometric objects:

```lean
structure GeometricWallpaperGroup.MotionTypePreservingIso
    (X Y : GeometricWallpaperGroup) where
  toMulEquiv : X.carrier ≃* Y.carrier
  map_isTranslation_iff : ∀ g : X.carrier,
    PlaneMotion.IsTranslation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsTranslation
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isRotation_iff : ∀ g : X.carrier,
    PlaneMotion.IsRotation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsRotation
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isReflection_iff : ∀ g : X.carrier,
    PlaneMotion.IsReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsReflection
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)
  map_isGlideReflection_iff : ∀ g : X.carrier,
    PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsGlideReflection
        ((toMulEquiv g : Y.carrier) : EuclideanMotion Plane)

def GeometricWallpaperGroup.TextbookEquivalent
    (X Y : GeometricWallpaperGroup) : Prop :=
  Nonempty
    (GeometricWallpaperGroup.MotionTypePreservingIso X Y)
```

The relation contains no compact covering set, quotient-space witness, recovered basis,
ambient affine conjugacy, or metric-preservation assumption.  It uses the approved M8a
conventions, including the zero translation identity and the exclusion of all translations
from rotations.

Identity, inverse, and composition are implemented directly, giving:

```lean
theorem GeometricWallpaperGroup.textbookEquivalent_equivalence :
    Equivalence GeometricWallpaperGroup.TextbookEquivalent
```

The implementation also supplies the corresponding setoid and quotient.

## Comparison with M8a

The geometric and recovered-strong relations agree:

```lean
theorem GeometricWallpaperGroup.textbookEquivalent_iff_toPlaneGroup
    (X Y : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent X Y ↔
      PlaneGroup.TextbookEquivalent
        X.toPlaneGroup Y.toPlaneGroup

theorem GeometricWallpaperGroup.textbookEquivalent_iff_equivalent
    (X Y : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent X Y ↔
      PlaneGroup.Equivalent X.toPlaneGroup Y.toPlaneGroup
```

The first theorem uses explicit adapters between the new direct structure and M8a's
`MotionTypePreservingIso`.  The second is a corollary of M8a's
`PlaneGroup.textbookEquivalent_iff_equivalent`.

Specialized adapters between `X.toPlaneGroup` and an existing strong target allow the final
classification to use the original standard model directly.  They do not compare or expose
the recovered target basis.

## Round trips

The strong round trip is deliberately stated up to the approved strong equivalence:

```lean
theorem PlaneGroup.toGeometric_toPlaneGroup
    (G : PlaneGroup) :
    PlaneGroup.Equivalent
      G G.toGeometricWallpaperGroup.toPlaneGroup
```

The recovered basis need not equal `G.translationLattice.basis`, so structural equality would
be false as a specification.

The geometric round trip is stated using the new direct relation:

```lean
theorem GeometricWallpaperGroup.toPlaneGroup_toGeometric
    (X : GeometricWallpaperGroup) :
    GeometricWallpaperGroup.TextbookEquivalent
      X X.toPlaneGroup.toGeometricWallpaperGroup
```

It also has exact carrier equality:

```lean
@[simp]
theorem GeometricWallpaperGroup.toPlaneGroup_toGeometric_carrier
    (X : GeometricWallpaperGroup) :
    X.toPlaneGroup.toGeometricWallpaperGroup.carrier = X.carrier
```

## Standard geometric models and classification

```lean
def WallpaperType.geometricModel
    (w : WallpaperType) : GeometricWallpaperGroup :=
  w.model.toGeometricWallpaperGroup
```

The final unique geometric classification theorem is:

```lean
theorem geometric_classification
    (X : GeometricWallpaperGroup) :
    ∃! w : WallpaperType,
      GeometricWallpaperGroup.TextbookEquivalent
        X w.geometricModel
```

The proof applies the completed M8a theorem:

```lean
textbook_classification X.toPlaneGroup
```

and copies only its carrier-level isomorphism and four preservation fields through the
conversion adapters.  It performs no crystallographic restriction, reflection split, shift
classification, or `5 + 3 + 9` case analysis.

Pairwise uniqueness is also exposed as:

```lean
theorem WallpaperType.geometricModels_textbookEquivalent_iff
    (w v : WallpaperType) :
    GeometricWallpaperGroup.TextbookEquivalent
      w.geometricModel v.geometricModel ↔ w = v
```

## Quotient and cardinality

```lean
abbrev GeometricWallpaperGroup.EquivalenceClass :=
  Quotient GeometricWallpaperGroup.textbookEquivalentSetoid

def WallpaperType.geometricEquivalenceClassEquiv :
    WallpaperType ≃ GeometricWallpaperGroup.EquivalenceClass

@[simp]
theorem GeometricWallpaperGroup.equivalenceClass_card_eq_seventeen :
    Nat.card GeometricWallpaperGroup.EquivalenceClass = 17
```

The quotient uses the direct geometric relation, not a hidden quotient of selected recovered
strong structures.

## Mathematical route and assumptions

M8c-c adds no new Bieberbach-scale mathematics.  Its inputs are exactly:

- M8c-a: `Finite (pointGroup X.carrier)`;
- M8c-b: a `RankTwoLattice Plane` whose carrier is the full translation module;
- M8b: the strong-to-geometric conversion;
- M8a: equivalence of motion-type and translation-preserving isomorphisms;
- M7: the unique strong seventeen-class theorem.

There is no hidden lattice hypothesis, finite point-group hypothesis under another name,
additional properness/local-compactness assumption, or axiomatized theorem.

## Items for human review

- `toPlaneGroup` has definitionally unchanged carrier and uses the entire recovered translation
  module.
- `PlaneGroup.equivalent_of_carrier_eq` correctly transports the full translation kernel.
- Choice independence is stated only through `PlaneGroup.Equivalent`.
- The direct geometric equivalence has exactly the four approved M8a predicates and no stronger
  ambient or metric condition.
- Both round trips have the correct strength: geometric textbook equivalence in one direction,
  strong equivalence rather than equality in the other.
- `geometric_classification` classifies the geometric objects under the explicitly stated direct
  relation and reuses M7/M8a rather than duplicating classification.
- The quotient and cardinality theorem use that same direct relation.

## Validation

- `lake env lean WallpaperGroups/Geometry/GeometricClassification.lean`: passed with no
  warnings.
- `lake build`: passed with no warnings (`2880` jobs).
- `git diff --check`: passed.
- The project Lean-source scan found no `sorry`, `admit`, `axiom`, or `unsafe`.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged.
- `PlaneGroup`, `TranslationPreservingIso`, all Version 1 classification/model files, the M8a
  motion-type implementation, M8b geometric conversion and definitions, and the M8c-a/M8c-b
  production modules are unchanged.
