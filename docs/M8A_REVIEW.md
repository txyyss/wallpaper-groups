Review status: approved

# M8a specification review

## Motion predicates

The definitions in `WallpaperGroups/Geometry/MotionType.lean` apply to arbitrary ambient
Euclidean motions of the plane, not only to elements already bundled in a `PlaneGroup`:

```lean
def PlaneMotion.determinant (g : EuclideanMotion Plane) : ℝ :=
  LinearMap.det
    ((linearPart g).toLinearEquiv : Plane →ₗ[ℝ] Plane)

def PlaneMotion.HasFixedPoint (g : EuclideanMotion Plane) : Prop :=
  ∃ x : Plane, g x = x

def PlaneMotion.IsTranslation (g : EuclideanMotion Plane) : Prop :=
  linearPart g = 1

def PlaneMotion.IsRotation (g : EuclideanMotion Plane) : Prop :=
  0 < determinant g ∧ ¬ IsTranslation g

def PlaneMotion.IsReflection (g : EuclideanMotion Plane) : Prop :=
  determinant g < 0 ∧ HasFixedPoint g

def PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) : Prop :=
  determinant g < 0 ∧ ¬ HasFixedPoint g
```

Thus translations include the identity (translation by zero), while rotations explicitly exclude
all translations.  `PlaneMotion.identity_type` states that the identity is a translation and is
none of the other three types.  `PlaneMotion.isTranslation_iff_eq_translation` identifies the
translation predicate with the corresponding pure translation, and

```lean
theorem PlaneMotion.isRotation_hasFixedPoint {g : EuclideanMotion Plane}
    (hrot : IsRotation g) :
    HasFixedPoint g
```

proves that the positive-determinant/nontranslation definition really has a rotation center.  The
proof shows that `id - linearPart g` is injective, using the M3 fact that a positive plane isometry
fixing a nonzero vector is the identity, and then uses finite-dimensionality to solve the fixed
point equation.

The geometric fixed-point definitions of reflection and glide reflection have the proved
algebraic characterizations

```lean
theorem PlaneMotion.isReflection_iff {g : EuclideanMotion Plane} :
    IsReflection g ↔ determinant g < 0 ∧ g ^ 2 = 1

theorem PlaneMotion.isGlideReflection_iff {g : EuclideanMotion Plane} :
    IsGlideReflection g ↔ determinant g < 0 ∧ g ^ 2 ≠ 1
```

The key intermediate result is

```lean
theorem PlaneMotion.negative_hasFixedPoint_iff_sq_eq_one
    {g : EuclideanMotion Plane} (hneg : determinant g < 0) :
    HasFixedPoint g ↔ g ^ 2 = 1
```

Its forward direction uses the M3 result that a negative-determinant plane isometry has
involutive linear part.  Its reverse direction constructs the midpoint of the origin and its
image as a fixed point.

`PlaneMotion.decomposition` proves that every ambient plane motion belongs to at least one of the
four types.  The six theorems
`isTranslation_not_isRotation`, `isTranslation_not_isReflection`,
`isTranslation_not_isGlideReflection`, `isRotation_not_isReflection`,
`isRotation_not_isGlideReflection`, and `isReflection_not_isGlideReflection`
prove pairwise disjointness.

## Textbook-style equivalence

The textbook isomorphism is independent of the Version 1 structure:

```lean
structure MotionTypePreservingIso (G H : PlaneGroup) where
  toMulEquiv : G.carrier ≃* H.carrier
  map_isTranslation_iff : ∀ g : G.carrier,
    PlaneMotion.IsTranslation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsTranslation
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isRotation_iff : ∀ g : G.carrier,
    PlaneMotion.IsRotation (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsRotation
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isReflection_iff : ∀ g : G.carrier,
    PlaneMotion.IsReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsReflection
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)
  map_isGlideReflection_iff : ∀ g : G.carrier,
    PlaneMotion.IsGlideReflection (g : EuclideanMotion Plane) ↔
      PlaneMotion.IsGlideReflection
        ((toMulEquiv g : H.carrier) : EuclideanMotion Plane)

def PlaneGroup.TextbookEquivalent (G H : PlaneGroup) : Prop :=
  Nonempty (MotionTypePreservingIso G H)
```

Each of the four fields is an `↔`, so preservation is required in both directions.  The underlying
map is only an abstract group isomorphism.  The definition does not require an ambient affine
conjugacy, an isometry between the planes, preservation of lengths or angles, or preservation of
the chosen lattice bases.

The Version 1 relation remains:

```lean
def PlaneGroup.Equivalent (G H : PlaneGroup) : Prop :=
  Nonempty (TranslationPreservingIso G H)
```

## Bridge theorems

The two structure conversions are:

```lean
def TranslationPreservingIso.toMotionTypePreservingIso
    (e : TranslationPreservingIso G H) :
    MotionTypePreservingIso G H

def MotionTypePreservingIso.toTranslationPreservingIso
    (e : MotionTypePreservingIso G H) :
    TranslationPreservingIso G H
```

The first conversion uses:

- `map_isTranslation_iff`, from preservation of the full translation subgroup;
- `map_motion_determinant`, from the existing real-linear conjugacy of the two point actions and
  determinant invariance under conjugacy;
- `map_ambient_sq_eq_one_iff`, from preservation of multiplication and the injectivity of the
  abstract group isomorphism; and
- the fixed-point/square characterizations above for reflections and glide reflections.

The converse conversion uses only the translation field to prove equality of the full translation
subgroups.  The other three fields are therefore consequences of translation preservation rather
than hidden additional assumptions.

The main logical bridge is:

```lean
theorem PlaneGroup.textbookEquivalent_iff_equivalent (G H : PlaneGroup) :
    PlaneGroup.TextbookEquivalent G H ↔ PlaneGroup.Equivalent G H
```

`PlaneGroup.textbookEquivalent_equivalence` additionally verifies that the textbook relation is
an equivalence relation.

## Seventeen-class corollary

The final M8a theorem has the complete type:

```lean
theorem textbook_classification (G : PlaneGroup) :
    ∃! w : WallpaperType,
      PlaneGroup.TextbookEquivalent G (WallpaperType.model w)
```

Its proof is a direct rewrite of the existing Version 1 theorem `classification G` by
`PlaneGroup.textbookEquivalent_iff_equivalent`.  No model, component classifier, uniqueness proof,
or Version 1 declaration is changed or duplicated.

## Items requiring owner review

- Whether orientation-preserving nontranslations are the intended exact rotation convention.
- Whether the identity should, as here, belong only to the translation class.
- Whether the fixed-point definitions and the proved square characterizations express the intended
  reflection/glide-reflection distinction.
- Whether the four `↔` fields of `MotionTypePreservingIso` exactly match the textbook relation.
- Whether the bridge correctly avoids any metric, ambient-conjugacy, or chosen-basis assumption.
- Whether `textbook_classification` is at the intended strong-algebraic `PlaneGroup` level; the
  geometric discrete/cocompact bridge remains M8b/M8c.

The primary source declarations to inspect are all in
`WallpaperGroups/Geometry/MotionType.lean`: the six definitions in `PlaneMotion`, the fixed-point
characterizations (including `isRotation_hasFixedPoint`) and decomposition/disjointness theorems,
`TranslationPreservingIso.map_motion_determinant`,
the four motion-type transport theorems, `MotionTypePreservingIso`,
`PlaneGroup.textbookEquivalent_iff_equivalent`, and `textbook_classification`.

## Final validation

- `WallpaperGroups/Geometry/MotionType.lean` compiles directly.
- The dedicated Lake target builds without warnings: 2870 jobs.
- `lake build` succeeds without warnings: 2873 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan has zero `sorry`, `admit`, `axiom`, or `unsafe` matches.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged from the starting
  commit `c286e5e6b506592797e78b8052a85a93abc05d61`.
- No Version 1 source declaration was modified; the only existing production file changed is the
  top-level import aggregator `WallpaperGroups.lean`.
