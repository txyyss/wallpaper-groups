Review status: approved by project owner

# M2 specification review

This document is the owner-facing review packet for M2, “Plane groups and
translation-preserving equivalence.”  It records the exact structures now implemented, compares
them with the paper and roadmap, and identifies the declarations whose mathematical meaning
requires human approval.  It is not approval itself.

## A. Plane

The complete production definition in `WallpaperGroups/Basic/Plane.lean` is:

```lean
abbrev Plane := EuclideanSpace ℝ (Fin 2)
```

The dimension and coordinate-frame interface is:

```lean
@[simp] theorem Plane.finrank : Module.finrank ℝ Plane = 2

noncomputable def Plane.canonicalRealBasis :
  Module.Basis (Fin 2) ℝ Plane

@[simp] theorem Plane.canonicalRealBasis_apply (i : Fin 2) :
  Plane.canonicalRealBasis i = EuclideanSpace.single i 1
```

`EuclideanSpace ℝ (Fin 2)` was selected because it is mathlib's standard finite-dimensional
real inner-product space.  It supplies the norm, inner product, completeness, and canonical
orthonormal coordinate basis that M3 will need.  Public group definitions still use vectors and
linear isometries rather than coordinate pairs.  The M0 test type `Fin 2 → ℝ` was rejected as the
formal plane because it does not itself expose the intended Euclidean-space abstraction.

## B. RankTwoLattice

The complete structure in `WallpaperGroups/Basic/RankTwoLattice.lean` is:

```lean
structure RankTwoLattice (E : Type*) [AddCommGroup E] [Module ℝ E] where
  carrier : Submodule ℤ E
  basis : Module.Basis (Fin 2) ℤ carrier
  basis_real_linearIndependent :
    LinearIndependent ℝ (fun i => (basis i : E))
```

The carrier is exactly a `Submodule ℤ E`.  The basis is exactly a two-element integer basis of
the carrier subtype.  The last field says that its two ambient vectors remain independent after
passing from integer to real scalars.

Mathematical structure versus computational frame:

- `carrier` and the existence of a real-linearly independent rank-two integer basis express the
  lattice mathematics used by the paper.
- the particular value stored in `basis` is a selected computational frame.  It supplies unique
  coordinates and matrices, but `TranslationPreservingIso` neither contains nor preserves it.
- `PlaneGroup.reframe_equivalent` formally proves that replacing only this selected frame does not
  change the classification equivalence class.

Coordinate and carrier API:

- `RankTwoLattice.coordinates`
- `RankTwoLattice.ofCoordinates`
- `coordinates_ofCoordinates`
- `ofCoordinates_coordinates`
- `coordinates_basis`
- `ofCoordinates_apply`
- `basis_expansion`
- `toAddSubgroup`, `mem_toAddSubgroup`, and `coe_toAddSubgroup`
- `carrier_ext`, `carrierEquivOfEq`, and `equivOfAddEquiv`
- `standardCarrier`, `standardBasis`, and `standardLattice`

Plane-specific real API:

- `RankTwoLattice.realBasis`
- `RankTwoLattice.realBasis_apply`
- `RankTwoLattice.real_span_eq_top`

The real basis is derived from `basis_real_linearIndependent` and `Plane.finrank`; it is not an
additional field.  `real_span_eq_top` proves that the integer carrier spans the entire plane over
`ℝ`.

The structure intentionally does not contain `DiscreteTopology`, `IsZLattice`, shortest-vector
data, a metric normal form, or a chosen orientation.  Those can be derived or introduced only in
the milestones where they are actually used.

## C. PlaneGroup

The complete structure in `WallpaperGroups/Basic/PlaneGroup.lean` is:

```lean
structure PlaneGroup where
  carrier : Subgroup (EuclideanMotion Plane)
  translationLattice : RankTwoLattice Plane
  translationLattice_carrier :
    translationLattice.carrier =
      (translationVectors carrier).toIntSubmodule
  pointGroup_finite : Finite (pointGroup carrier)
```

Field meanings:

- `carrier` is the actual subgroup of affine Euclidean isometries.
- `translationLattice` records the rank-two translation carrier and a selected frame.
- `translationLattice_carrier` says that its carrier is exactly all pure-translation vectors in
  `carrier`.  It is not containment and not a finite-index sublattice.
- `pointGroup_finite` stores typeclass-based finiteness of the image of the linear-part map.

Derived interfaces include:

- `PlaneGroup.motionGroup`
- `translationLattice_carrier_eq`
- `translationLattice_toAddSubgroup_eq`
- `latticeTranslationEquiv` and its forward/inverse ambient-coercion lemmas
- `mem_translationLattice_iff` and `mem_translationLattice_iff_translation_mem`
- the `PlaneGroup.pointGroupFinite` instance
- `chosenBasis`, `realBasis`, and `translation_real_span_eq_top`
- `PlaneGroup.reframe`

The exact carrier equality is the central strong-definition check.  It prevents the stored
lattice from omitting additional translations.  `Finite`, rather than `Fintype`, is stored; code
that truly enumerates the point group must install `Fintype.ofFinite` locally.

No discreteness or cocompactness condition is included.  No orientation, rotation/reflection,
shortest-vector, shift, norm-map, or wallpaper-label field is included.

## D. TranslationPreservingIso

The complete structure in `WallpaperGroups/Basic/Equivalence.lean` is:

```lean
structure TranslationPreservingIso (G H : PlaneGroup) where
  toMulEquiv : G.carrier ≃* H.carrier
  map_translationSubgroup :
    (translationSubgroup G.carrier).map
        toMulEquiv.toMonoidHom =
      translationSubgroup H.carrier
```

`map_translationSubgroup` is equality of the forward image with the entire target translation
subgroup.  This is the exact Lean expression of “maps the subgroup `T` onto `T'`.”  It yields the
membership iff theorem `map_mem_translationSubgroup_iff`, the inverse map equality
`map_translationSubgroup_symm`, the comap theorem `comap_translationSubgroup`, and the restriction
`translationSubgroupEquiv`.

The constructors are:

- `TranslationPreservingIso.refl`
- `TranslationPreservingIso.symm`
- `TranslationPreservingIso.trans`

Their map fields use `Subgroup.map_id`, `Subgroup.map_symm_eq_iff_map_eq`, and
`Subgroup.map_map`, respectively.  The file proves double inverse, left/right identity, inverse,
and associativity laws.

This structure is deliberately:

- an abstract group isomorphism between the two motion subgroups;
- not an ambient Euclidean conjugacy;
- not required to arise from an affine map;
- not required to preserve norm, distance, inner product, length, or angle;
- not required to preserve the selected lattice basis;
- not supplied with an arbitrary point-group map.

The point-group map and general real-linear plane map are derived canonically below.

## E. PlaneGroup.Equivalent

The complete definition is:

```lean
def PlaneGroup.Equivalent (G H : PlaneGroup) : Prop :=
  Nonempty (TranslationPreservingIso G H)
```

The relation laws are:

- `PlaneGroup.Equivalent.refl`
- `PlaneGroup.Equivalent.symm`
- `PlaneGroup.Equivalent.trans`
- bundled theorem `PlaneGroup.equivalent_equivalence`

The project also installs `PlaneGroup.equivalentSetoid`.  M2 does not construct the quotient or
give it a finite type; quotient-level classification remains M7 work.

## F. Induced structures and action transport

### Translation and lattice maps

- `TranslationPreservingIso.translationSubgroupEquiv` is the restricted `MulEquiv` between the
  M1 kernel subgroups.
- `translationVectorMulEquiv` and `translationVectorEquiv` identify the full pure-translation
  vector groups.  Their definition reuses M1's `translationEquiv` on both endpoints.
- `translationLatticeEquiv` transports that additive equivalence through the exact stored-carrier
  adapters and promotes it canonically to a `ℤ`-linear equivalence.
- `map_translationElement` and `map_pureTranslation` are the pure-translation commuting formulas.
- zero, addition, negation, inverse, identity, and composition compatibility lemmas are exported
  for the vector and stored-lattice maps.

### Point-group map

- `PlaneGroup.pointQuotientEquiv` is
  `QuotientGroup.quotientKerEquivRange (restrictedLinearPart G.carrier)`.
- `TranslationPreservingIso.quotientEquiv` transports translation quotients with
  `QuotientGroup.congr`.
- `TranslationPreservingIso.pointGroupEquiv` sandwiches the quotient map between the two canonical
  kernel/range equivalences.
- `pointGroupEquiv_pointProjection` is the canonical projection-commutation theorem.
- `pointProjection_commutes` is its bundled homomorphism equality.
- `pointGroupEquiv_refl`, `pointGroupEquiv_symm`,
  `pointGroupEquiv_symm_pointProjection`, and `pointGroupEquiv_trans` give the expected laws.
- `pointGroup_natCard_eq` and `pointGroup_finite_transport` record cardinality/finiteness transport.

No public point-group map depends on a selected lift.

### Faithful integral action

`WallpaperGroups/Invariants/IntegralAction.lean` exports:

- `PlaneGroup.latticeActionAddEquiv`
- `PlaneGroup.latticeAction`
- `latticeAction_one`, `latticeAction_mul`, and `latticeAction_inv`
- bundled `latticeActionHom`
- faithful theorem `latticeActionHom_injective`
- `latticeActionMatrix`
- `integralRepresentation : pointGroup G.carrier →*
    Matrix.GeneralLinearGroup (Fin 2) ℤ`
- `latticeActionMatrix_injective`
- `integralRepresentation_injective`

The faithfulness proof is mathematical: equality on the lattice action fixes the two selected
lattice basis vectors; those vectors form `G.realBasis`; basis extensionality therefore gives
equality of the ambient real linear isometries and hence of the point-group subtype elements.

### Matrix and basis-change API

`WallpaperGroups/Basic/RankTwoLattice.lean` exports:

- `equivMatrix` and `equivMatrix_apply_coordinates`
- identity, composition, inverse, and mutual-inverse matrix theorems
- `equivGL` and `equivGL_injective`
- `matrix_intertwining`
- `matrix_intertwining_of_apply`
- `matrix_commutation`
- `matrix_conjugacy`
- `basisChangeMatrix` and `basisChangeGL`
- `matrix_conjugacy_reframe`

For `f ∘ A = B ∘ f`, the compiled mathlib convention gives:

```text
P * A = B * P
B = P * A * P⁻¹
```

The raw matrix is therefore basis-dependent; its `GL₂(ℤ)` conjugacy class represents the
coordinate-free action across frame changes.

### Equivalence action and real extension

`WallpaperGroups/Invariants/EquivalenceAction.lean` exports:

- `translationVector_pointAction`
- `translationLattice_pointAction`
- `latticeAction_intertwining` and `latticeAction_conjugacy`
- `realLinearEquiv`
- `realLinearEquiv_agrees`
- `realLinearEquiv_symm`, `realLinearEquiv_refl`, and `realLinearEquiv_trans`
- `realLinearEquiv_pointAction`
- `ambientAction_intertwining`
- `integralMatrix_intertwining`
- `integralMatrix_conjugacy`
- `integralRepresentation_conjugacy`

`realLinearEquiv` is built by casting the matrix of `translationLatticeEquiv` and its inverse from
`ℤ` to `ℝ`, then applying `Matrix.toLinOfInv` between the two real lattice bases.  The theorem
`realLinearEquiv_agrees` proves that this map extends the lattice map on every lattice element.
It is an ordinary `LinearEquiv`, not a `LinearIsometryEquiv`; no metric-preservation claim is made.

### Selected-frame independence

- `RankTwoLattice.reframe` changes only the chosen integer basis.
- `PlaneGroup.reframe` changes only the lattice frame of a plane group.
- `PlaneGroup.reframeIso` is the identity abstract group isomorphism with translation preservation.
- `PlaneGroup.reframe_equivalent` proves the original and reframed values are `Equivalent`.
- `RankTwoLattice.matrix_conjugacy_reframe` proves their automorphism matrices are related by the
  expected `GL₂(ℤ)` change-of-basis conjugacy.

Thus the chosen basis is visibly useful for computation but absent from the classified
equivalence data.

## G. Mathematical specification cross-check

### Paper, printed page 125

The page defines a plane group by linearly independent vectors `t₁,t₂` whose integer combinations
are exactly the translation lattice, together with finiteness of the point group.  The Lean
implementation matches this:

- the integer combinations and their uniqueness are packaged by
  `Module.Basis (Fin 2) ℤ carrier`;
- real linear independence is the third lattice field;
- exact identification with all translations is `translationLattice_carrier`;
- point-group finiteness is `pointGroup_finite`.

Technical representation difference: the paper writes a set of integer combinations; Lean uses
an integer submodule and a basis of its subtype.  This changes no mathematical condition.

### Paper, printed page 127

The page declares two groups equivalent when an abstract group isomorphism maps `T` onto `T'`.
`TranslationPreservingIso.toMulEquiv` and `map_translationSubgroup` express exactly this.  The page
then derives a lattice isomorphism `λ`, a conjugacy of point groups, and compatibility of their
actions.  Lean derives:

- `translationLatticeEquiv` for `λ` on the integer lattices;
- `realLinearEquiv` for its ordinary real-linear extension;
- `pointGroupEquiv` for the point groups;
- `translationVector_pointAction`, `translationLattice_pointAction`, and
  `realLinearEquiv_pointAction` for compatibility;
- `integralMatrix_conjugacy` for the chosen-coordinate expression.

The paper's `λ` is not stated to be orthogonal, and Lean likewise does not claim that it is an
isometry.

### Roadmap M2

All implementation tasks and acceptance criteria in M2 are represented by declarations listed in
this document.  The roadmap phrase about preservation of shift classes is interpreted as building
the translation-lattice, point-group, and action transport prerequisites.  Shift classes are not
defined until M5.

### Explicit deviations

There is no substantive mathematical deviation from the paper's strong definition or equivalence
relation.  Technical representation differences are:

1. translation vectors are an `AddSubgroup`, while their stored lattice carrier is the canonically
   equal `Submodule ℤ`;
2. point groups are ranges of the restricted linear-part homomorphism and their induced map is
   constructed through kernel quotients rather than arbitrary lifts;
3. the point group stores `Finite`, not an enumerating `Fintype`;
4. matrices and real extensions use selected computational frames, with formal frame-independence
   theorems;
5. shift-class preservation is deferred to M5 because the shift class itself is not an M2 object.

These are implementation choices, not changes to the equivalence relation.

## H. Content deliberately not declared in M2

M2 does not implement or expose:

- orientation or an orientation subgroup;
- crystallographic restriction;
- rotation/reflection classification or order enumeration;
- shortest lattice vectors;
- finite-order `GL₂(ℤ)` classification;
- cyclic/dihedral point-group classification;
- shift vectors, norm maps, or shift classes;
- any of the 17 standard models or wallpaper labels;
- quotient-level classification or a quotient `Fintype`;
- discreteness/cocompactness bridges;
- general group cohomology.

M3 remains entirely unstarted.

## I. Source locations requiring focused human review

1. `WallpaperGroups/Basic/Plane.lean`
   - `Plane`
   - `Plane.finrank`
   - `Plane.canonicalRealBasis`
2. `WallpaperGroups/Basic/RankTwoLattice.lean`
   - `RankTwoLattice`
   - `realBasis`, `real_span_eq_top`
   - `equivMatrix`, `equivGL`
   - `matrix_intertwining`, `matrix_conjugacy`, `matrix_conjugacy_reframe`
   - `extendEquiv`, `extendEquiv_agrees`
3. `WallpaperGroups/Basic/PlaneGroup.lean`
   - `PlaneGroup`
   - `translationLattice_toAddSubgroup_eq`
   - `latticeTranslationEquiv`
   - `PlaneGroup.reframe`
4. `WallpaperGroups/Basic/Equivalence.lean`
   - `TranslationPreservingIso`
   - `translationSubgroupEquiv`, `translationVectorEquiv`, `translationLatticeEquiv`
   - `PlaneGroup.Equivalent`
   - `PlaneGroup.pointQuotientEquiv`, `pointGroupEquiv`
   - `pointGroupEquiv_pointProjection`
   - `PlaneGroup.reframeIso`, `PlaneGroup.reframe_equivalent`
5. `WallpaperGroups/Invariants/IntegralAction.lean`
   - `latticeAction`
   - `latticeActionHom_injective`
   - `integralRepresentation`, `integralRepresentation_injective`
6. `WallpaperGroups/Invariants/EquivalenceAction.lean`
   - `translationVector_pointAction`
   - `translationLattice_pointAction`
   - `realLinearEquiv`, `realLinearEquiv_pointAction`
   - `integralMatrix_conjugacy`, `integralRepresentation_conjugacy`

The two highest-priority specification decisions are the exact fields of `PlaneGroup` and
`TranslationPreservingIso`.

## J. Dependency graph and verification

High-level module graph:

```text
Plane ───────────────┐
                     ├─ RankTwoLattice ── PlaneGroup ── Equivalence ───────┐
EuclideanMotion ─────┴─ Translation ─ PointGroup ─ ExactSequence           │
                                             └─ IntegralAction ────────────┤
                                                                            └─ EquivalenceAction
```

Principal theorem dependency graph:

```text
translationLattice_carrier
  -> latticeTranslationEquiv
  -> latticeAction
  -> latticeActionHom_injective
  -> integralRepresentation_injective

map_translationSubgroup
  -> translationSubgroupEquiv
  -> translationVectorEquiv
  -> translationLatticeEquiv

map_translationSubgroup
  -> QuotientGroup.congr
  -> pointGroupEquiv
  -> pointGroupEquiv_pointProjection

map_translationElement + M1 conjugate_translationElement
  -> translationVector_pointAction
  -> translationLattice_pointAction
  -> latticeAction_intertwining
  -> integralMatrix_intertwining
  -> integralMatrix_conjugacy

translationLatticeEquiv + inverse integer matrices
  -> RankTwoLattice.extendEquiv
  -> realLinearEquiv_agrees
  -> realLinearEquiv_pointAction
  -> ambientAction_intertwining
```

Commands used during implementation and final verification include:

```text
lake env lean WallpaperGroups/Basic/Plane.lean
lake env lean WallpaperGroups/Basic/RankTwoLattice.lean
lake env lean WallpaperGroups/Basic/PlaneGroup.lean
lake env lean WallpaperGroups/Basic/Equivalence.lean
lake env lean WallpaperGroups/Invariants/IntegralAction.lean
lake env lean WallpaperGroups/Invariants/EquivalenceAction.lean
lake env lean WallpaperGroups/Prototype/RankTwoLattice.lean

lake build \
  WallpaperGroups.Prototype.APIAudit \
  WallpaperGroups.Prototype.EuclideanMotion \
  WallpaperGroups.Prototype.RankTwoLattice
lake build

git diff --check
rg -n '\b(sorry|admit|axiom)\b' WallpaperGroups WallpaperGroups.lean
rg -n '\bunsafe\b' WallpaperGroups WallpaperGroups.lean
rg -n 'import WallpaperGroups\.Prototype' WallpaperGroups -g '!Prototype/**'
```

At the time this review packet was prepared, all six new production files compiled individually,
the migrated rank-two-lattice regression file compiled, and `lake build` completed successfully
with 2387 jobs.  The final placeholder and `unsafe` scans have no project-source matches.  The
toolchain and mathlib revisions remain unchanged.  Final command results are also reported in the
task handoff; this review status must remain awaiting human approval until the project owner
explicitly accepts the specifications.
