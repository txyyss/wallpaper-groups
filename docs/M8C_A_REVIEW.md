Review status: approved

# M8c-a point-group recovery review

M8c-a implements the local topology and finite-point-group stage approved in
`M8C_DESIGN_REVIEW.md`.  It does not recover a compact translation-domain witness, prove that
the translation module spans the plane, construct a `PlaneGroup`, or begin the geometric
classification.

## Completed scope

The production implementation is
`WallpaperGroups/Geometry/GeometricToStrong.lean`.  It adds:

- determinant and orientation-preserving point-group definitions for an arbitrary subgroup of
  plane Euclidean motions;
- compact-intersection and compact fixed-point finiteness helpers;
- finiteness of the positive point subgroup;
- finiteness of the full point group under the approved discrete and cocompact hypotheses;
- finite index of the pure-translation subgroup;
- a thin adapter from a mathlib full `ℤ`-lattice in the plane to the project's framed
  `RankTwoLattice`.

The new module is imported by `WallpaperGroups.lean`, so the default Lake target checks it.

## New declarations

### Subgroup-level determinant and orientation

```lean
def MotionSubgroup.pointGroupDet
    (Γ : Subgroup (EuclideanMotion Plane)) :
    pointGroup Γ →* ℝˣ

@[simp]
theorem MotionSubgroup.pointGroupDet_apply
    (Γ : Subgroup (EuclideanMotion Plane))
    (A : pointGroup Γ) :
    ((MotionSubgroup.pointGroupDet Γ A : ℝˣ) : ℝ) =
      LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv :
          Plane →ₗ[ℝ] Plane)

def MotionSubgroup.orientationPreservingPointGroup
    (Γ : Subgroup (EuclideanMotion Plane)) :
    Subgroup (pointGroup Γ)

@[simp]
theorem MotionSubgroup.mem_orientationPreservingPointGroup_iff
    (Γ : Subgroup (EuclideanMotion Plane))
    (A : pointGroup Γ) :
    A ∈ MotionSubgroup.orientationPreservingPointGroup Γ ↔
      0 < LinearMap.det
        ((A : Plane ≃ₗᵢ[ℝ] Plane).toLinearEquiv :
          Plane →ₗ[ℝ] Plane)
```

The new definitions agree definitionally with the approved M3 definitions whenever a strong
`PlaneGroup` is already available:

```lean
@[simp]
theorem MotionSubgroup.pointGroupDet_planeGroup (G : PlaneGroup) :
    MotionSubgroup.pointGroupDet G.carrier = pointGroupDet G

@[simp]
theorem MotionSubgroup.orientationPreservingPointGroup_planeGroup
    (G : PlaneGroup) :
    MotionSubgroup.orientationPreservingPointGroup G.carrier =
      orientationPreservingPointGroup G
```

The plane-isometry commutativity and conjugation calculations used internally are private
implementation lemmas, not an additional public orientation framework.

### Compact-set finiteness

```lean
theorem MotionSubgroup.compact_intersections_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    {K L : Set Plane}
    (hK : IsCompact K) (hL : IsCompact L) :
    {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}.Finite

theorem MotionSubgroup.fixedPoint_in_compact_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    {K : Set Plane} (hK : IsCompact K) :
    {γ : Γ | ∃ x ∈ K, γ • x = x}.Finite
```

The first theorem is a thin explicit-hypothesis wrapper around the approved
`ProperlyDiscontinuousSMul` compact-intersection condition.  The second is the form used by the
point-group proof.

### Point-group finiteness

```lean
theorem MotionSubgroup.orientationPreservingPointGroup_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    Finite (MotionSubgroup.orientationPreservingPointGroup Γ)

theorem MotionSubgroup.pointGroup_finite
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    Finite (pointGroup Γ)
```

For a bundled geometric wallpaper group the result is installed as:

```lean
instance GeometricWallpaperGroup.pointGroupFinite
    (X : GeometricWallpaperGroup) :
    Finite (pointGroup X.carrier)
```

The theorem assumes exactly the two approved geometric hypotheses.  It does not assume a
translation lattice, a nonzero translation, finite generation, point-group finiteness under
another name, or an unproved Bieberbach theorem.

### Finite-index translation subgroup

```lean
theorem MotionSubgroup.translationSubgroup_finiteIndex
    (Γ : Subgroup (EuclideanMotion Plane))
    [Finite (pointGroup Γ)] :
    (translationSubgroup Γ).FiniteIndex

theorem MotionSubgroup.translationSubgroup_finiteIndex_of_geometric
    (Γ : Subgroup (EuclideanMotion Plane))
    (hdisc : MotionSubgroup.IsDiscrete Γ)
    (hcoc : MotionSubgroup.IsCocompact Γ) :
    (translationSubgroup Γ).FiniteIndex

instance GeometricWallpaperGroup.translationSubgroupFiniteIndex
    (X : GeometricWallpaperGroup) :
    (translationSubgroup X.carrier).FiniteIndex
```

This is the existing kernel-range exact sequence plus point-group finiteness; it introduces no
choice of coset representatives.

### Adapter from `IsZLattice`

```lean
noncomputable def RankTwoLattice.ofZLattice
    (L : Submodule ℤ Plane)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    RankTwoLattice Plane

@[simp]
theorem RankTwoLattice.ofZLattice_carrier
    (L : Submodule ℤ Plane)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    (RankTwoLattice.ofZLattice L).carrier = L
```

The adapter assumes, rather than proves, that `L` is discrete and full rank.  Those facts for the
actual translation module belong to M8c-b.

## Point-group proof route

Let `K` be a compact set meeting every orbit.

1. Proper discontinuity makes the set of group elements fixing some point of `K` finite.
2. For a positive point-group element `A ≠ 1`, choose an existential lift `g`.
3. The lift is an orientation-preserving non-translation and hence a rotation.  Its fixed point
   can be moved into `K` by some `h : Γ`.
4. The conjugate `h * g * h⁻¹` fixes a point of `K`, so it belongs to the finite set from step 1.
5. In dimension two, conjugation by a positive linear isometry leaves `A` unchanged, while
   conjugation by a negative linear isometry sends `A` to `A⁻¹`.
6. Thus every positive point element lies in the identity together with a finite projected set
   and its inverse.
7. If a negative point element exists, left multiplication by one fixed negative element
   injects the negative part into the finite positive part.

This proves the entire point group finite before any nonzero translation or rank statement is
available.

## Mathlib and existing project API used

- `LinearEquiv.det` and the existing `linearIsometryToLinearEquiv`;
- `Orientation.exists_linearIsometryEquiv_eq_of_det_pos`;
- `PlaneMotion.isRotation_hasFixedPoint`;
- `negative_conjugates_positive_to_inverse`;
- `MotionSubgroup.isDiscrete_iff_compact_finite`;
- `MotionSubgroup.isCocompact_iff_exists_compact_orbit_representatives`;
- `pointGroup_exists_lift`, `pointProjection`, and `pointProjection_ker`;
- `Subgroup.finiteIndex_ker`;
- `ZLattice.module_finite`, `ZLattice.module_free`, and `ZLattice.rank`;
- `Module.Free.chooseBasis`, `Module.finrank_eq_card_chooseBasisIndex`,
  `Fintype.equivOfCardEq`, and `Module.Basis.ofZLatticeBasis`.

No new topology on `EuclideanMotion Plane`, general locally compact group, covering-space
argument, or general Bieberbach abstraction is introduced.

## Noncanonical-choice discipline

- A lift in the point-group proof is eliminated inside an existential proof.  No section or
  chosen-lift function is exported.
- `RankTwoLattice.ofZLattice` must choose an integer basis because the approved
  `RankTwoLattice` structure stores framing data.
- The only stable theorem exported about that choice is carrier equality.
- No theorem declares the selected basis canonical.
- `TranslationPreservingIso` and `PlaneGroup.Equivalent` observe the full translation subgroup,
  not the stored basis.  Existing `PlaneGroup.reframe_equivalent` already eliminates a change of
  frame.
- A later strong round trip must therefore be stated up to `PlaneGroup.Equivalent`, and then up
  to M8a textbook equivalence, never as judgmental or structure equality.

## Files for review

- `WallpaperGroups/Geometry/GeometricToStrong.lean`
- `WallpaperGroups.lean`
- `docs/M8C_DESIGN_REVIEW.md`
- `docs/M8C_A_REVIEW.md`

The declarations requiring the closest mathematical review are:

- `MotionSubgroup.orientationPreservingPointGroup_finite`;
- `MotionSubgroup.pointGroup_finite`;
- `RankTwoLattice.ofZLattice`.

## Remaining risks and deferred work

M8c-b has not started.  It must still:

- use finite point-group lifts to transfer a compact representative set to the translation
  kernel;
- prove the actual translation module has `DiscreteTopology`;
- exclude zero- and rank-one translation span;
- prove full real span and instantiate `IsZLattice`;
- apply `RankTwoLattice.ofZLattice` to the full translation module.

The finite-union compact-cover bookkeeping is expected to be medium risk.  The orthogonal
full-span argument remains the main mathematical risk.  M8c-c must later construct the
`PlaneGroup`, prove choice independence and round trips, and define the reviewed geometric
equivalence and classification theorem.

`docs/PROGRESS.md` is intentionally unchanged: its first M8c checkbox also requires recovery of
the full rank-two translation lattice, which belongs to M8c-b.

## Validation

- `WallpaperGroups/Geometry/GeometricToStrong.lean` compiles directly without warnings.
- The root `WallpaperGroups.lean` import and full `lake build` succeed without warnings.
- `git diff --check` succeeds.
- The project Lean-source scan has no `sorry`, `admit`, `axiom`, or `unsafe` matches.
- `PlaneGroup`, all Version 1 classification files, and the approved M8b geometric definitions
  are unchanged.
- M8c-b has not started.
