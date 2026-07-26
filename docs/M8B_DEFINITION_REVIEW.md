Review status: awaiting human approval

# M8b definition review

This review fixes only the geometric definitions that M8b and M8c will use.  It does not prove
that a strong `PlaneGroup` satisfies them, construct a fundamental parallelogram, or begin the
reverse geometric bridge.

## Selected Lean definitions

Every subgroup of plane Euclidean motions receives the evaluation action

```lean
instance motionSubgroupMulAction (Γ : Subgroup (EuclideanMotion Plane)) :
    MulAction Γ Plane

instance motionSubgroupContinuousConstSMul
    (Γ : Subgroup (EuclideanMotion Plane)) :
    ContinuousConstSMul Γ Plane
```

The selected discreteness predicate is:

```lean
def MotionSubgroup.IsDiscrete
    (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ProperlyDiscontinuousSMul Γ Plane
```

Mathlib's `ProperlyDiscontinuousSMul` has the compact-set formulation exposed by:

```lean
theorem MotionSubgroup.isDiscrete_iff_compact_finite
    (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsDiscrete Γ ↔
      ∀ {K L : Set Plane}, IsCompact K → IsCompact L →
        {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}.Finite
```

Thus, for any two compact plane sets, only finitely many group elements move the first so that
it meets the second.

The selected cocompactness predicate is:

```lean
def MotionSubgroup.IsCocompact
    (Γ : Subgroup (EuclideanMotion Plane)) : Prop :=
  ∃ K : Set Plane,
    IsCompact K ∧
      ⋃ γ : Γ, (γ • ·) '' K = Set.univ
```

The resulting geometric object is:

```lean
structure GeometricWallpaperGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  isDiscrete : MotionSubgroup.IsDiscrete carrier
  isCocompact : MotionSubgroup.IsCocompact carrier
```

`MotionSubgroup.OrbitSpace Γ` abbreviates the quotient by the orbit relation.  The implemented
sanity theorem is the full equivalence:

```lean
theorem MotionSubgroup.isCocompact_iff_compact_orbitSpace
    (Γ : Subgroup (EuclideanMotion Plane)) :
    MotionSubgroup.IsCocompact Γ ↔
      CompactSpace (MotionSubgroup.OrbitSpace Γ)
```

The forward direction maps a compact covering set into the quotient.  For the reverse direction,
local compactness of the plane and openness of the orbit quotient map produce finitely many
compact local lifts of a finite quotient cover.  Thus choosing the compact-cover definition does
not strengthen or weaken the standard compact-orbit-space notion.

## Alternatives considered

### Discreteness

1. **Discrete topology on the subgroup subtype.**  This would require a topology on
   `EuclideanMotion Plane`, then a proof or instance that the induced subtype topology is
   discrete.  Current mathlib does not provide the needed topology on
   `AffineIsometryEquiv`, so this would force the project to introduce and maintain an ambient
   motion-group topology before it is otherwise needed.
2. **The carrier is a discrete subset of the ambient motion group.**  This has the same missing
   ambient-topology prerequisite.  It would also make later action lemmas depend on an additional
   bridge from subgroup discreteness to proper discontinuity.  Once an ambient topology is
   supplied, mathlib's `SetLike.isDiscrete_iff_discreteTopology` identifies alternatives 1 and 2;
   the real missing ingredient is the topology and its action bridge.
3. **A pointwise orbit-discreteness or free-action condition.**  Orbit discreteness alone is too
   weak for compact-set arguments, while freeness is too strong because wallpaper groups may
   have finite stabilizers at rotation centers or reflection axes.

The selected properly discontinuous action is the standard compact-set finiteness condition for
discrete isometry groups.  It permits finite stabilizers and is already supported by mathlib.
For faithful isometric actions on the proper Euclidean plane it corresponds to the usual
discrete-subgroup notion, without requiring that equivalence to be built into the definition.

### Cocompactness

1. **Compactness of the orbit quotient as the primary definition.**  This is concise, but the M8b
   proof naturally constructs a compact fundamental parallelogram and its translates.  The
   theorem `isCocompact_iff_compact_orbitSpace` proves that the two formulations are equivalent
   for the plane, so either has the same mathematical strength.
2. **Every orbit meets a compact set.**  This is equivalent to the chosen covering equation up to
   replacing group elements by inverses, but the union-of-translates form matches the intended
   fundamental-domain proof and mathlib's quotient preimage formula directly.

The compact-cover formulation is therefore primary because it supplies the witness needed by both
directions.  Orbit-quotient compactness is retained as a proved equivalent formulation, not as an
extra field.

## Current mathlib support

- `Mathlib.Topology.Algebra.ConstMulAction` supplies `ProperlyDiscontinuousSMul`,
  `properlyDiscontinuousSMul_iff`, the orbit quotient, and the quotient preimage formula used by
  the compactness equivalence.
- Every affine isometry equivalence already has a continuous underlying map, so the subgroup
  evaluation action has a direct `ContinuousConstSMul` instance.
- Mathlib includes finite-relative-index transfer lemmas for properly discontinuous actions.  M8b
  can use these after proving the translation subgroup acts properly discontinuously.
- Mathlib does not currently supply the ambient topology required by either rejected
  discrete-subgroup formulation.

## Expected M8b proof route

After this definition gate is approved, the main proof is expected to:

1. derive proper discontinuity of the rank-two translation lattice from its chosen integer basis;
2. use a closed fundamental parallelogram as the compact covering set for translations;
3. use the finite point group and existing exact-sequence data to pass both properties across the
   finitely many translation cosets; and
4. package the unchanged carrier of every strong `PlaneGroup` as a
   `GeometricWallpaperGroup`.

None of these proof steps is implemented in this snapshot.

## Effect on M8c

Proper discontinuity supplies compact-set finiteness and finite stabilizers in a form usable when
recovering a translation lattice and finite point group.  The compact covering witness gives M8c
an actual compact subset of the plane rather than only an abstract compact quotient.  These are
the two forms expected to support the difficult reverse direction.

The remaining M8c work is still substantial: it must derive the full rank-two translation
lattice, prove finiteness of the point group, and construct the strong `PlaneGroup` without
adding hidden hypotheses or importing an unproved Bieberbach theorem.

## Risks and questions for owner review

- Is action-level `ProperlyDiscontinuousSMul` accepted as the project's exact formal meaning of a
  discrete Euclidean-motion subgroup?
- Is the compact-cover equation the desired primary presentation of cocompactness, with compactness
  of the orbit quotient kept as a proved equivalent theorem?
- Should a later theorem prove equivalence with ambient subgroup discreteness if a satisfactory
  topological-group instance for `EuclideanMotion Plane` is introduced?
- The chosen definitions are designed for M8c, but they do not remove its Bieberbach-scale
  difficulty; in particular, no translation-lattice rank theorem has yet been proved.

The declarations to review are in
`WallpaperGroups/Geometry/GeometricWallpaperGroup.lean`:
`motionSubgroupMulAction`, `motionSubgroupContinuousConstSMul`,
`MotionSubgroup.IsDiscrete`, `MotionSubgroup.IsCocompact`,
`MotionSubgroup.isDiscrete_iff_compact_finite`,
`MotionSubgroup.isCocompact_iff_exists_compact_orbit_representatives`,
`MotionSubgroup.isCocompact_iff_compact_orbitSpace`, and
`GeometricWallpaperGroup`.

## Validation

- `WallpaperGroups/Geometry/GeometricWallpaperGroup.lean` compiles directly.
- The dedicated Lake target and full `lake build` succeed without warnings.
- `git diff --check` succeeds.
- The project Lean-source scan has no `sorry`, `admit`, `axiom`, or `unsafe` matches.
- No Version 1 declaration, M8a definition, toolchain file, or dependency file is changed.
