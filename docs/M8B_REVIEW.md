Review status: approved

# M8b proof review

M8b proves that every strong algebraic `PlaneGroup` is a geometric wallpaper group in the
approved sense.  It does not change the definitions in
`WallpaperGroups/Geometry/GeometricWallpaperGroup.lean`, add hypotheses to `PlaneGroup`, or begin
the converse construction of M8c.

## Completed direction

```text
strong PlaneGroup
  ⇒
discrete cocompact geometric wallpaper group
```

## Main theorem and exact assumptions

The canonical conversion is:

```lean
def PlaneGroup.toGeometricWallpaperGroup
    (G : PlaneGroup) : GeometricWallpaperGroup
```

Its carrier is definitionally the original motion subgroup:

```lean
@[simp]
theorem PlaneGroup.toGeometricWallpaperGroup_carrier
    (G : PlaneGroup) :
    G.toGeometricWallpaperGroup.carrier = G.carrier
```

The two fields are supplied by:

```lean
theorem PlaneGroup.motionGroup_isDiscrete (G : PlaneGroup) :
    MotionSubgroup.IsDiscrete G.carrier

theorem PlaneGroup.motionGroup_isCocompact (G : PlaneGroup) :
    MotionSubgroup.IsCocompact G.carrier
```

These theorems quantify only over `G : PlaneGroup`.  They use exactly its existing rank-two
translation lattice, equality with the full translation carrier, and finite point group.  They
introduce no additional lattice, freeness, discreteness, compactness, finite-index, or
faithfulness hypothesis.

Since the conversion is proved for every `PlaneGroup`, it applies directly and uniformly to all
17 existing values `WallpaperType.model w`; no standard model or Version 1 classification
declaration is modified.

## Lattice discreteness

The proof reuses the existing theorem

```lean
RankTwoLattice.carrier_eq_zspan_realBasis
```

which identifies the stored integer carrier with the integer span of the derived real basis.
Mathlib's `ZSpan` API then gives:

```lean
theorem RankTwoLattice.carrier_discreteTopology
    (L : RankTwoLattice Plane) :
    DiscreteTopology L.carrier

theorem RankTwoLattice.finite_inter_of_isBounded
    (L : RankTwoLattice Plane)
    {s : Set Plane} (hs : Bornology.IsBounded s) :
    (s ∩ (L.carrier : Set Plane)).Finite
```

For compact sets `K` and `M`, a pure translation whose image of `K` meets `M` is mapped to its
translation displacement.  This map is injective, and every such displacement lies in the
intersection of the lattice with the bounded difference set `M - K`.  Hence:

```lean
theorem PlaneGroup.translationSubgroup_isDiscrete
    (G : PlaneGroup) :
    ProperlyDiscontinuousSMul
      (EuclideanMotion.translationSubgroup G.carrier) Plane
```

The point projection has the translation subgroup as its kernel.  Finiteness of the stored point
group therefore gives:

```lean
theorem PlaneGroup.translationSubgroup_finiteIndex
    (G : PlaneGroup) :
    (EuclideanMotion.translationSubgroup G.carrier).FiniteIndex
```

`ProperlyDiscontinuousSMul.ofFiniteRelIndex` passes proper discontinuity from that kernel to the
full motion group.  The proof applies the theorem inside the environment group `G.carrier`, to
the inclusion of the translation subgroup into `⊤`; it does not introduce a topology on the
ambient type `EuclideanMotion Plane`.

## Compact covering set

The selected compact set is the closed parallelogram of the lattice's derived real basis:

```lean
def RankTwoLattice.compactParallelogram
    (L : RankTwoLattice Plane) : Set Plane :=
  parallelepiped L.realBasis

theorem RankTwoLattice.isCompact_compactParallelogram
    (L : RankTwoLattice Plane) :
    IsCompact L.compactParallelogram
```

Mathlib proves compactness of this closed parallelepiped.  For any point `x`, the proof takes the
negative integer-coordinate floor supplied by `ZSpan.floor`.  Its remainder
`ZSpan.fract L.realBasis x` lies in the half-open fundamental domain, which is contained in the
closed parallelogram.  This yields:

```lean
theorem RankTwoLattice.exists_lattice_add_mem_compactParallelogram
    (L : RankTwoLattice Plane) (x : Plane) :
    ∃ t : L.carrier,
      (t : Plane) + x ∈ L.compactParallelogram
```

For `G : PlaneGroup`, the full-translation-carrier equality turns `t` into an element of
`G.carrier`.  Thus every orbit meets the same compact parallelogram, which is equivalent to the
approved translate-cover definition of cocompactness.  The resulting quotient-level corollary is:

```lean
theorem PlaneGroup.motionGroup_compactOrbitSpace
    (G : PlaneGroup) :
    CompactSpace (MotionSubgroup.OrbitSpace G.carrier)
```

The cocompactness proof needs only the rank-two translation lattice.  Finiteness of the point
group is used specifically for extending proper discontinuity from translations to the full
group.

## Proof-design decisions

- Reuse mathlib's `ZSpan` discreteness, floor, fractional-part, and parallelepiped results instead
  of maintaining a second coordinate-bounding development.
- Use the closed parallelogram as the compact witness.  The half-open fundamental domain supplies
  the orbit representative but is not itself used as the compact set.
- Use the exact-sequence kernel and mathlib's finite-index transfer theorem instead of selecting
  and managing explicit coset representatives.
- Keep the conversion carrier definitionally equal to `G.carrier`; no copying, conjugating, or
  rebuilding of the motion subgroup occurs.
- Keep all reverse-direction questions out of M8b.  No geometric group is converted back to a
  `PlaneGroup`.

## Items requiring owner review

- Whether the bounded-displacement proof establishes the intended strength of proper
  discontinuity for the translation subgroup.
- Whether finite-index transfer through the point-projection kernel uses exactly, and only, the
  stored finite point-group hypothesis.
- Whether the closed parallelogram plus `ZSpan.floor` gives the desired explicit compact-cover
  witness.
- Whether `PlaneGroup.toGeometricWallpaperGroup`, with carrier equality by `rfl`, is the intended
  canonical forward conversion.
- Whether the general theorem over every `PlaneGroup` is sufficient evidence that all 17
  standard models are covered without model-specific corollaries.
- Whether the source remains cleanly inside M8b and adds no hidden premise needed for M8c.

The source declarations to inspect are all in
`WallpaperGroups/Geometry/StrongToGeometric.lean`.

## Validation

- `WallpaperGroups/Geometry/StrongToGeometric.lean` compiles directly without warnings.
- The dedicated Lake target succeeds without warnings: 2840 jobs.
- Full `lake build` succeeds without warnings: 2877 jobs.
- `git diff --check` succeeds.
- The project Lean-source scan has no `sorry`, `admit`, `axiom`, or `unsafe` matches.
- `PlaneGroup`, the approved geometric definitions, all Version 1 classification declarations,
  and the Lean/mathlib dependency configuration are unchanged.
- M8c has not started.
